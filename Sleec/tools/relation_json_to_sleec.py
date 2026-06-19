#!/usr/bin/env python3
"""
relation_json_to_sleec.py — convert a sleecvalDef-style relation.json
into a valid SLEEC spec.

Source format (one entry per Relationship):
    Event-event entries:    {"event1": "...", "event2": "...", "<flag>": <bool>, ...}
    Measure-measure entries:{"measure1": "...", "measure2": "...", "<flag>": <bool>, ...}

The flag is one of: witness, conflicts, HB, implies, equals, ME.

Authoritative source for the schema:
    https://github.com/NickF0211/sleecvalDef/blob/master/LLM_SAN/inference_rules.py

Mapping to SLEEC (sleec-gramar.tx):
    witness   E1 E2     -->  witness E1 E2                 (event-event)
    conflicts E1 E2     -->  mutualExclusive E1 E2         (event-event)
    HB        E1 E2     -->  happenBefore E1 E2            (event-event)
    implies   M1 M2     -->  measure imply {M1} {M2}        (measure-measure)
    equals    M1 M2     -->  measure iff   {M1} {M2}        (measure-measure)
    ME        M1 M2     -->  measure mutualExclusive {M1} {M2}

Outcome handling:
    truthy outcome  -> emit the relation
    falsy outcome   -> emit as a SLEEC comment, since SLEEC has no
                       native "not <relation>" form
    unknown outcome -> emit as a comment with a "FILL IN" marker

Self-pair handling (event1 == event2 or measure1 == measure2):
    witness/implies/equals  : trivially true at runtime, emit but flag
    conflicts/HB/ME         : trivially false at runtime, emit as comment

Commutative kinds (conflicts, equals, ME): identical pairs in both
orders are de-duplicated.

Usage:
    python3 relation_json_to_sleec.py INPUT.json [-o OUTPUT.sleec]

Exit codes:
    0  conversion succeeded
    1  conversion completed but with warnings (skipped/unknown entries)
    2  fatal error (file not found, malformed JSON)
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from typing import Dict, List, Optional, Set, Tuple


# -----------------------------------------------------------------------------
# Constants from the upstream inference_rules.py
# -----------------------------------------------------------------------------

EVENT_FLAGS = {"witness", "conflicts", "HB"}
MEASURE_FLAGS = {"implies", "equals", "ME"}
COMMUTATIVE = {"conflicts", "equals", "ME"}

SLEEC_KEYWORD = {
    "witness":   ("witness",         "event"),
    "conflicts": ("mutualExclusive", "event"),
    "HB":        ("happenBefore",    "event"),
    "implies":   ("imply",           "measure"),
    "equals":    ("iff",             "measure"),
    "ME":        ("mutualExclusive", "measure"),
}

SELF_TRIVIAL_TRUE  = {"witness", "implies", "equals"}
SELF_TRIVIAL_FALSE = {"conflicts", "HB", "ME"}


# -----------------------------------------------------------------------------
# Truthiness helpers (mirror inference_rules.py TRUE() / FALSE())
# -----------------------------------------------------------------------------

def is_true(v) -> bool:
    if isinstance(v, bool):
        return v is True
    if isinstance(v, str):
        s = v.strip().lower()
        return s == "true" or s.startswith("t")
    return False


def is_false(v) -> bool:
    if isinstance(v, bool):
        return v is False
    if isinstance(v, str):
        s = v.strip().lower()
        return s == "false" or s.startswith("f")
    return False


# -----------------------------------------------------------------------------
# Conversion
# -----------------------------------------------------------------------------

def detect_flag(rc: dict) -> Optional[str]:
    """Return the relation-flag key present in the relationship dict, or None."""
    for f in (EVENT_FLAGS | MEASURE_FLAGS):
        if f in rc:
            return f
    return None


def render_relation(flag: str, a: str, b: str) -> str:
    """Render a single SLEEC relation line (no surrounding block)."""
    keyword, kind = SLEEC_KEYWORD[flag]
    if kind == "event":
        return f"{keyword} {a} {b}"
    else:
        return f"measure {keyword} {{{a}}} {{{b}}}"


def convert(
    rel_doc: dict,
    *,
    placeholder_event: str = "RelOnlyPlaceholder",
    source_path: str = "<stdin>",
) -> Tuple[str, List[str]]:
    """Convert a parsed relation.json document to a SLEEC spec string.

    Returns (sleec_text, warnings).
    """
    warnings: List[str] = []
    relations = rel_doc.get("relations", [])
    if not isinstance(relations, list):
        raise ValueError("relation.json missing top-level 'relations' list")

    events: Set[str] = set()
    measures: Set[str] = set()
    emitted_lines: List[str] = []  # SLEEC relation lines (or comment lines)
    seen_pairs: Set[Tuple[str, str, str]] = set()  # (flag, a, b) canonical

    for idx, entry in enumerate(relations):
        rc = entry.get("Relationship", entry)
        if not isinstance(rc, dict):
            warnings.append(f"entry #{idx}: not a dict, skipping")
            continue

        flag = detect_flag(rc)
        if flag is None:
            warnings.append(f"entry #{idx}: no recognised relation flag, skipping")
            continue

        # Pull operands.
        if flag in EVENT_FLAGS:
            a = rc.get("event1"); b = rc.get("event2")
            if not a or not b:
                warnings.append(
                    f"entry #{idx} ({flag}): missing event1/event2, skipping")
                continue
            events.add(a); events.add(b)
            kind = "event"
        else:
            a = rc.get("measure1"); b = rc.get("measure2")
            if not a or not b:
                warnings.append(
                    f"entry #{idx} ({flag}): missing measure1/measure2, skipping")
                continue
            measures.add(a); measures.add(b)
            kind = "measure"

        outcome = rc.get(flag)
        justification = rc.get("justification", "").strip().replace("\n", " ")

        # Canonicalise commutative pairs and de-dupe.
        if flag in COMMUTATIVE:
            ca, cb = (a, b) if a <= b else (b, a)
        else:
            ca, cb = a, b
        key = (flag, ca, cb)
        if key in seen_pairs:
            continue
        seen_pairs.add(key)

        # Self-pair handling.
        is_self = (a == b)

        # Build the comment header for this entry.
        comment = f"// {flag}({a}, {b})"
        if justification:
            comment += f" -- {justification}"

        # Emit.
        line = render_relation(flag, a, b)
        if is_self:
            if flag in SELF_TRIVIAL_TRUE:
                emitted_lines.append(comment + "  [self-pair: trivially TRUE]")
                emitted_lines.append(f"// {line}    // commented; self-pair is vacuous")
                continue
            elif flag in SELF_TRIVIAL_FALSE:
                emitted_lines.append(comment + "  [self-pair: trivially FALSE]")
                emitted_lines.append(f"// {line}    // commented; would force {a} to never fire")
                warnings.append(
                    f"entry #{idx} ({flag} {a} {b}): self-pair is trivially "
                    f"unsatisfiable; emitted as comment")
                continue

        if is_true(outcome):
            emitted_lines.append(comment)
            emitted_lines.append("    " + line)
        elif is_false(outcome):
            emitted_lines.append(comment + "  [outcome=False; SLEEC has no native negation, emitted as comment]")
            emitted_lines.append("    // " + line)
        else:
            emitted_lines.append(comment + f"  [outcome={outcome!r}; UNKNOWN, emitted as comment]")
            emitted_lines.append("    // " + line)
            warnings.append(
                f"entry #{idx} ({flag} {a} {b}): outcome {outcome!r} is "
                f"neither true nor false; emitted as comment")

    # ----- assemble the SLEEC spec -----
    spec_name = rel_doc.get("name", "unknown")
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    # Pick a real event for the placeholder rule trigger. SLEEC requires
    # at least one rule, and the trigger must be a declared event.
    if events:
        placeholder_trigger = sorted(events)[0]
    else:
        placeholder_trigger = "RelOnlyTrigger"
        events.add(placeholder_trigger)

    out = []
    out.append(f"// SLEEC spec auto-generated from a sleecvalDef relation.json.")
    out.append(f"// Source name : {spec_name}")
    out.append(f"// Source path : {source_path}")
    out.append(f"// Generated   : {now}")
    out.append(f"// Tool        : Sleec/tools/relation_json_to_sleec.py")
    out.append(f"//")
    out.append(f"// The rule_start block holds a single placeholder rule because")
    out.append(f"// the SLEEC grammar requires rules+=Rule+ (>=1).  The placeholder")
    out.append(f"// is a synchronous self-firing on {placeholder_trigger!r} that")
    out.append(f"// adds no semantic constraint beyond what the relations express.")
    out.append("")

    # def_start
    out.append("def_start")
    for e in sorted(events):
        out.append(f"    event {e}")
    for m in sorted(measures):
        out.append(f"    measure {m}: boolean")
    out.append("def_end")
    out.append("")

    # rule_start (placeholder)
    out.append("rule_start")
    out.append(f"    R_placeholder when {placeholder_trigger} then {placeholder_trigger}")
    out.append("rule_end")
    out.append("")

    # relation_start
    if emitted_lines:
        out.append("relation_start")
        for line in emitted_lines:
            if line.startswith("//") or line.startswith("    //"):
                out.append(line)
            else:
                out.append(line)
        out.append("relation_end")
    else:
        out.append("// (no relations emitted; relation block omitted because SLEEC")
        out.append("//  requires relations+=Relation+ — at least one — inside it.)")

    out.append("")
    return "\n".join(out), warnings


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Convert a sleecvalDef relation.json to a SLEEC spec.")
    parser.add_argument("input", help="Path to a relation.json file.")
    parser.add_argument("-o", "--output", default=None,
                        help="Output .sleec path (default: stdout).")
    parser.add_argument("-q", "--quiet", action="store_true",
                        help="Suppress warnings on stderr.")
    args = parser.parse_args(argv)

    if not os.path.isfile(args.input):
        print(f"error: file not found: {args.input}", file=sys.stderr)
        return 2

    try:
        with open(args.input) as f:
            doc = json.load(f)
    except json.JSONDecodeError as e:
        print(f"error: malformed JSON in {args.input}: {e}", file=sys.stderr)
        return 2

    try:
        text, warnings = convert(doc, source_path=args.input)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)

    if warnings and not args.quiet:
        print("\n".join(f"warning: {w}" for w in warnings), file=sys.stderr)

    return 1 if warnings else 0


if __name__ == "__main__":
    raise SystemExit(main())
