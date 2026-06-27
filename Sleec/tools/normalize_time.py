#!/usr/bin/env python3
"""
normalize_time.py — scale all deadlines in a SLEEC spec by their GCD.

Given a SLEEC spec where every rule deadline and every TimedEM
``for N`` duration is a non-negative multiple of some common
divisor g, this tool produces an equivalent spec in which every
deadline has been divided by g. The two specs have identical
realizability verdicts (the time-axis abstraction is sound for
SLEEC's pointwise semantics — see notes below), but the
normalized spec's deadlines are smaller, which makes both the
B_max upper bound and the bounded SAT problem much smaller.

Soundness sketch
----------------
A bounded realizability check over horizon N seconds with all
deadlines D_i is equivalent to a bounded check over horizon
ceil(N/g) "scaled steps" with deadlines D_i/g, because:

  - Rule conditions and obligations are evaluated pointwise; no
    rule references inter-step granularity below g seconds.
  - Multiple env events placed within the same g-second window
    are indistinguishable to every rule.
  - Each TimedEM ``for N seconds`` window of length N is
    indistinguishable from a length-N/g window in the coarsened
    model.

So the normalized spec admits exactly the same set of
counterexamples (modulo time-axis stretching) as the original.

Output convention
-----------------
The output always uses ``seconds`` as the unit (regardless of
whether the input used minutes/hours/days). This avoids unit
mismatches between scaled and unscaled deadlines after the
division.

Usage
-----
    python3 normalize_time.py SPEC.sleec
    python3 normalize_time.py SPEC.sleec -o SPEC_normalized.sleec

Exit codes
----------
    0 success
    2 fatal error (file not found, parse failure, etc.)
"""

import argparse
import os
import sys
from functools import reduce
from math import gcd
from typing import List, Optional, Tuple


# -----------------------------------------------------------------------------
# Path setup
# -----------------------------------------------------------------------------

_HERE = os.path.dirname(os.path.abspath(__file__))
_SLEEC = os.path.dirname(_HERE)
_ANALYZER = os.path.join(os.path.dirname(_SLEEC), "Analyzer")
for _p in (_SLEEC, _ANALYZER):
    if _p not in sys.path:
        sys.path.insert(0, _p)


# -----------------------------------------------------------------------------
# Time-unit conversion
# -----------------------------------------------------------------------------

_UNIT_TO_SECONDS = {
    "second":  1, "seconds":  1,
    "minute":  60, "minutes": 60,
    "hour":    3600, "hours": 3600,
    "day":     86400, "days":  86400,
}


def _time_value_to_seconds(tv_node) -> Optional[int]:
    """Convert a textX TimeValue node to its value in seconds.

    Returns None if the value isn't a known integer literal or
    constant (i.e., the TimeValue's source meaning is non-trivial
    and we should not try to scale it).
    """
    unit = getattr(tv_node, "unit", None)
    if not isinstance(unit, str):
        return None
    factor = _UNIT_TO_SECONDS.get(unit.lower())
    if factor is None:
        return None

    nt = getattr(tv_node, "value", None)
    if nt is None:
        return None
    # Literal integer: NumTerminal.value is a Value with .value=int.
    lit = getattr(nt, "value", None)
    if lit is not None and hasattr(lit, "value") and isinstance(lit.value, int):
        return lit.value * factor
    # Named constant: NumTerminal.ID points to a Constant whose .value
    # is a Value with .value=int.
    cref = getattr(nt, "ID", None)
    if cref is not None:
        cval = getattr(cref, "value", None)
        if cval is not None and hasattr(cval, "value") and \
                isinstance(cval.value, int):
            return cval.value * factor
    return None


# -----------------------------------------------------------------------------
# AST walk
# -----------------------------------------------------------------------------

def _walk_textx(node):
    if node is None:
        return
    yield node
    for attr in dir(node):
        if attr.startswith("_") or attr == "parent":
            continue
        try:
            v = getattr(node, attr)
        except Exception:
            continue
        if isinstance(v, (str, bytes, int, float, bool)):
            continue
        if isinstance(v, list):
            for item in v:
                yield from _walk_textx(item)
        elif hasattr(v, "__module__") and \
                getattr(v, "__module__", "").startswith("textx"):
            yield from _walk_textx(v)


# -----------------------------------------------------------------------------
# Public API
# -----------------------------------------------------------------------------

def normalize_time_str(spec_text: str) -> Tuple[str, int]:
    """Normalize a SLEEC spec by scaling all deadlines by their GCD.

    Returns (normalized_spec_text, gcd_used).

    If no deadlines (or only zero deadlines, or only `eventually`
    deadlines, or coprime deadlines with no shared factor) are present,
    returns (spec_text, 1) unchanged.
    """
    import sleecRealizibilityCheck as _rlz
    _rlz._reset_sleecnorm_state()
    from sleecParser import parse_sleec

    model, *_ = parse_sleec(spec_text, read_file=False)

    # Find every TimeValue node, record (start, end, seconds).
    nodes: List[Tuple[int, int, int]] = []
    for n in _walk_textx(model):
        if type(n).__name__ != "TimeValue":
            continue
        secs = _time_value_to_seconds(n)
        if secs is None or secs <= 0:
            # Either unrecognised expression, or zero (instantaneous);
            # zero deadlines do not contribute to GCD anyway.
            continue
        start = getattr(n, "_tx_position", None)
        end = getattr(n, "_tx_position_end", None)
        if start is None or end is None:
            continue
        nodes.append((start, end, secs))

    if not nodes:
        return spec_text, 1

    g = reduce(gcd, (s for _, _, s in nodes))
    if g <= 1:
        return spec_text, 1

    # Substitute "<scaled> seconds" for each TimeValue's source span,
    # processing in reverse-position order so earlier spans aren't shifted.
    nodes.sort(key=lambda x: x[0], reverse=True)
    new_text = spec_text
    for start, end, secs in nodes:
        scaled = secs // g
        new_text = new_text[:start] + f"{scaled} seconds" + new_text[end:]

    return new_text, g


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Scale all deadlines in a SLEEC spec by their GCD. "
                    "The output spec is realizability-equivalent to the input "
                    "but has smaller (often dramatically smaller) deadline "
                    "values, shrinking B_max and the bounded SAT problem."
    )
    ap.add_argument("filename", help="Path to a .sleec spec.")
    ap.add_argument(
        "-o", "--output", default=None,
        help="Output path for the normalized spec (default: stdout).",
    )
    ap.add_argument(
        "-q", "--quiet", action="store_true",
        help="Suppress 'GCD = N seconds' info on stderr.",
    )
    args = ap.parse_args(argv)

    if not os.path.isfile(args.filename):
        print(f"error: file not found: {args.filename}", file=sys.stderr)
        return 2

    try:
        with open(args.filename) as f:
            spec_text = f.read()
    except OSError as exc:
        print(f"error: cannot read {args.filename}: {exc}", file=sys.stderr)
        return 2

    try:
        new_text, g = normalize_time_str(spec_text)
    except Exception as exc:
        print(f"error: normalization failed: {exc}", file=sys.stderr)
        return 2

    if not args.quiet:
        if g <= 1:
            print(f"# {args.filename}: no scaling applied "
                  f"(GCD = 1; deadlines already at finest granularity)",
                  file=sys.stderr)
        else:
            print(f"# {args.filename}: GCD = {g} seconds; "
                  f"all deadlines scaled by {g}.", file=sys.stderr)

    if args.output:
        try:
            with open(args.output, "w") as f:
                f.write(new_text)
        except OSError as exc:
            print(f"error: cannot write {args.output}: {exc}", file=sys.stderr)
            return 2
        if not args.quiet:
            print(f"# wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(new_text)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
