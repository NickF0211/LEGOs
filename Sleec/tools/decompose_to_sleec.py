#!/usr/bin/env python3
"""
decompose_to_sleec.py — split a SLEEC spec into per-component .sleec files.

Runs the dependency-graph decomposition from ``sleec_decompose`` on a
.sleec file and emits one self-contained .sleec spec per component.
Each emitted spec contains:

  - a ``def_start`` block with exactly the events, measures, and constants
    referenced by the component's rules and relations (in source order),
  - a ``rule_start`` block with the component's rules (in source order),
  - a ``relation_start`` block with the component's gating relations and
    all *global* (measure-only) relations that apply to every component.

The emitted specs are individually runnable through
``sleecRealizibilityCheck.py`` (e.g.\\ for per-component realizability
checking).

Usage
-----
    python3 decompose_to_sleec.py SPEC.sleec [-o DIR] [-q]

    -o DIR       write per-component specs to DIR/SPEC_component_NN.sleec
                 (creates DIR if it does not exist).
    (no -o)      print each component's spec to stdout with a banner.
    -q           suppress 'wrote ...' status lines.

Exit codes
----------
    0   decomposition succeeded
    2   fatal error (file not found, parse failure, etc.)
"""

import argparse
import os
import sys
from typing import Iterable, List, Optional, Set


# -----------------------------------------------------------------------------
# Path setup — mirrors sleecRealizibilityCheck so imports resolve regardless
# of where the user runs the script from.
# -----------------------------------------------------------------------------

_HERE = os.path.dirname(os.path.abspath(__file__))
_SLEEC = os.path.dirname(_HERE)
_ANALYZER = os.path.join(os.path.dirname(_SLEEC), "Analyzer")
for _p in (_SLEEC, _ANALYZER):
    if _p not in sys.path:
        sys.path.insert(0, _p)


# -----------------------------------------------------------------------------
# AST walking helpers (mirrors sleec_decompose._walk_textx so we don't have
# to import private symbols).
# -----------------------------------------------------------------------------

def _walk_textx(node) -> Iterable:
    """Yield every sub-node of a textX AST object reachable from ``node``."""
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


def _collect_referenced_names(ast_node, defined_names: Set[str]) -> Set[str]:
    """Walk ``ast_node`` and return the names from ``defined_names`` that
    are referenced anywhere inside (events, measures, constants)."""
    result: Set[str] = set()
    for sub in _walk_textx(ast_node):
        name = getattr(sub, "name", None)
        if isinstance(name, str) and name in defined_names:
            result.add(name)
    return result


def _extract_source(spec_text: str, ast_node) -> str:
    """Return the original source slice for ``ast_node`` (using textX
    ``_tx_position`` / ``_tx_position_end``), trailing whitespace stripped.

    Some objects we get from ``parse_sleec_norm`` are wrapper classes
    (e.g.\\ ``EventRelation`` wraps a textX ``EventRel``); for those, the
    underlying positioned node is accessible via the ``reference``
    attribute. We look there first when the wrapper itself has no
    position.
    """
    node = ast_node
    if not hasattr(node, "_tx_position") or node._tx_position is None:
        ref = getattr(node, "reference", None)
        if ref is not None and hasattr(ref, "_tx_position"):
            node = ref
    start = getattr(node, "_tx_position", None)
    end = getattr(node, "_tx_position_end", None)
    if start is None or end is None:
        return ""
    return spec_text[start:end].rstrip()


# -----------------------------------------------------------------------------
# Component spec builder
# -----------------------------------------------------------------------------

def _build_component_spec(
    *,
    model,
    spec_text: str,
    component,
    global_relation_indices: List[int],
    relations: List,
    normalized_rules: List,
) -> str:
    """Construct the .sleec text for a single component.

    Robustness contract: every input element that we need to emit must
    extract to non-empty source text. Failures (a normalized rule with
    no .og_rule, a textX node missing position info, a relation wrapper
    with neither own position nor .reference) raise RuntimeError rather
    than silently producing a degraded spec. The only intentional skip
    is the per-textX-position dedupe loop, where multiple normalized
    rules legitimately map to the same source-level Rule (primary +
    defeater branches).
    """
    # component.rule_indices indexes into normalized_rules. Multiple
    # normalized rules may share the same underlying textX Rule (a primary
    # rule and its defeater branch each become a normalized rule). We
    # dedupe by tx position so the source text appears once.
    seen_positions: Set[tuple] = set()
    comp_textx_rules = []
    for i in component.rule_indices:
        nr = normalized_rules[i]
        textx_rule = getattr(nr, "og_rule", None)
        if textx_rule is None:
            raise RuntimeError(
                f"normalized rule #{i} has no .og_rule attribute. "
                f"Decomposition assumes every normalized rule corresponds "
                f"to a source-level Rule. Synthetic rules without an "
                f"underlying textX node are not supported here."
            )
        start = getattr(textx_rule, "_tx_position", None)
        end = getattr(textx_rule, "_tx_position_end", None)
        if start is None or end is None:
            raise RuntimeError(
                f"og_rule for normalized rule #{i} "
                f"(type {type(textx_rule).__name__}) has no textX position "
                f"information; cannot extract source text."
            )
        key = (start, end)
        if key in seen_positions:
            # Intentional dedupe: defeater branches share an og_rule.
            continue
        seen_positions.add(key)
        comp_textx_rules.append(textx_rule)

    # Preserve original source order (sort by start position).
    comp_textx_rules.sort(key=lambda r: getattr(r, "_tx_position", 0))

    comp_relations = [relations[i] for i in component.relation_indices]
    global_relations = [relations[i] for i in global_relation_indices]
    all_relations = comp_relations + global_relations

    # Names of every event / measure / constant defined in the spec.
    defined_names: Set[str] = {
        getattr(d, "name", None)
        for d in model.definitions
        if getattr(d, "name", None)
    }

    # Walk rules and relations to discover which defined names are referenced.
    used: Set[str] = set()
    for r in comp_textx_rules:
        used |= _collect_referenced_names(r, defined_names)
    for rel in all_relations:
        # Relation wrappers (EventRelation, Causation, ...) are not textX
        # nodes; walk into their `.reference` so the walker actually visits
        # the underlying AST.
        node = rel
        if not hasattr(node, "_tx_position") or node._tx_position is None:
            ref = getattr(node, "reference", None)
            if ref is not None and hasattr(ref, "_tx_position"):
                node = ref
        used |= _collect_referenced_names(node, defined_names)

    # Assemble the spec text.
    out: List[str] = []

    out.append("def_start")
    for d in model.definitions:
        name = getattr(d, "name", None)
        if name not in used:
            continue  # Intentional filter: only emit referenced definitions.
        text = _extract_source(spec_text, d)
        if not text:
            raise RuntimeError(
                f"definition {name!r} (type {type(d).__name__}) has no "
                f"textX position info; cannot extract source. This "
                f"indicates a definition that was not parsed normally."
            )
        out.append("    " + text)
    out.append("def_end")
    out.append("")

    out.append("rule_start")
    for r in comp_textx_rules:
        text = _extract_source(spec_text, r)
        if not text:
            raise RuntimeError(
                f"rule {getattr(r, 'name', '?')!r} produced empty source "
                f"text despite having valid position info."
            )
        out.append("    " + text)
    out.append("rule_end")

    if all_relations:
        out.append("")
        out.append("relation_start")
        for idx, rel in enumerate(all_relations):
            text = _extract_source(spec_text, rel)
            if not text:
                # Every relation should be reachable via .reference (the
                # wrapper attribute, see _extract_source) or have its own
                # _tx_position. Fail loudly if neither: silently dropping
                # the relation would (a) produce a spec that no longer
                # has the same constraints as the original and (b) hide
                # a real bug in the wrapper-handling code.
                raise RuntimeError(
                    f"could not extract source text for relation #{idx} "
                    f"(type={type(rel).__name__}, "
                    f"has_tx_position={hasattr(rel, '_tx_position')}, "
                    f"has_reference={hasattr(rel, 'reference')}). "
                    f"This indicates a new relation wrapper kind that "
                    f"_extract_source does not yet know how to unwrap."
                )
            out.append("    " + text)
        out.append("relation_end")

    out.append("")
    return "\n".join(out)


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Decompose a SLEEC spec into per-component .sleec files."
    )
    ap.add_argument("filename", help="Path to a .sleec spec file.")
    ap.add_argument(
        "-o", "--output-dir", default=None,
        help="Directory to write per-component .sleec files. "
             "If omitted, each component's spec is printed to stdout.",
    )
    ap.add_argument(
        "-q", "--quiet", action="store_true",
        help="Suppress informational messages on stderr.",
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

    # Reset analyzer module state (same pattern as the CLI's static checks)
    # so a fresh parse starts from a clean type_constructor.
    import sleecRealizibilityCheck as _rlz
    _rlz._reset_sleecnorm_state()

    try:
        from SleecNorm import parse_sleec_norm
        from sleec_decompose import decompose_with_relations
        from sleec_event_classification import classify_events_with_annotations
    except ImportError as exc:
        print(f"error: cannot import SLEEC modules: {exc}", file=sys.stderr)
        return 2

    try:
        model, normalized_rules, _AM, _Actions, og_rules, _concerns, relations = \
            parse_sleec_norm(spec_text, read_file=False)
    except Exception as exc:
        print(f"error: parse failure on {args.filename}: {exc}",
              file=sys.stderr)
        return 2

    try:
        ec = classify_events_with_annotations(model)
    except Exception as exc:
        print(f"error: event classification failed: {exc}", file=sys.stderr)
        return 2

    try:
        decomp = decompose_with_relations(
            normalized_rules, og_rules, relations, ec
        )
    except Exception as exc:
        print(f"error: decomposition failed: {exc}", file=sys.stderr)
        return 2

    base_name = os.path.splitext(os.path.basename(args.filename))[0]
    n_components = len(decomp.components)
    n_global = len(decomp.global_relation_indices)

    if not args.quiet:
        print(
            f"# {args.filename}: {len(normalized_rules)} rule(s) "
            f"-> {n_components} component(s)"
            + (f" + {n_global} global relation(s)" if n_global else ""),
            file=sys.stderr,
        )

    for i, component in enumerate(decomp.components, 1):
        content = _build_component_spec(
            model=model,
            spec_text=spec_text,
            component=component,
            global_relation_indices=decomp.global_relation_indices,
            relations=relations,
            normalized_rules=normalized_rules,
        )

        if args.output_dir:
            try:
                os.makedirs(args.output_dir, exist_ok=True)
            except OSError as exc:
                print(f"error: cannot create {args.output_dir}: {exc}",
                      file=sys.stderr)
                return 2
            out_path = os.path.join(
                args.output_dir,
                f"{base_name}_component_{i:02d}.sleec",
            )
            try:
                with open(out_path, "w") as f:
                    f.write(content)
            except OSError as exc:
                print(f"error: cannot write {out_path}: {exc}", file=sys.stderr)
                return 2
            if not args.quiet:
                n_rules = len(component.rule_indices)
                n_rels = len(component.relation_indices)
                print(
                    f"  wrote {out_path}  "
                    f"({n_rules} rule(s), {n_rels} relation(s)"
                    + (f" + {n_global} global" if n_global else "")
                    + ")",
                    file=sys.stderr,
                )
        else:
            sep = "=" * 72
            n_rules = len(component.rule_indices)
            n_rels = len(component.relation_indices)
            sys.stdout.write(f"// {sep}\n")
            sys.stdout.write(
                f"// Component {i} of {n_components}: "
                f"{n_rules} rule(s), {n_rels} component-relation(s)"
                + (f" + {n_global} global relation(s)" if n_global else "")
                + "\n"
            )
            sys.stdout.write(f"// {sep}\n\n")
            sys.stdout.write(content)
            sys.stdout.write("\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
