#!/usr/bin/env python3
"""
compute_max_bound.py — compute the completeness threshold B_max for a
SLEEC spec.

Implements the algorithm in the paper's "Bound Determination for Unbounded
Realizability" subsection. Returns the smallest horizon $B$ at which a
successful bounded realizability check certifies unbounded realizability;
the value comes from the cardinality of the lookahead state space
    (T_max + 2)^|R| * |H|
where T_max is the largest rule deadline, |R| is the number of normalized
rules, and |H| = 2^(c_hb + c_un) * prod_j (N_j + 1) is the relation memory
size.

If the spec uses 'eventually' anywhere, this returns infinity: bounded
analysis is sound for unrealizability only, and no finite completeness
threshold exists.

Usage
-----
    python3 compute_max_bound.py SPEC.sleec [--decompose] [-v]

    --decompose   Compute a per-component bound for each decomposition
                  component and report the max and sum.
    -v            Show per-component breakdown components (rule deadlines,
                  relation counts, etc.).
"""

import argparse
import os
import sys
from typing import Dict, List, Optional, Sequence


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
# Public API
# -----------------------------------------------------------------------------

INF = float("inf")


def compute_b_max(normalized_rules: Sequence, relations: Sequence) -> Dict:
    """Compute B_max for a given set of normalized rules and relations.

    Returns a dict with keys:
        b_max          : int, or INF if the spec uses 'eventually'
        T_max          : int (largest deadline in seconds)
        rule_count     : int (|R|, number of normalized rules)
        h_size         : int (|H|, relation-memory cardinality)
        c_hb           : int (number of happenBefore declarations)
        c_un           : int (number of UntilEM declarations)
        for_durations  : list of int (durations of TimedEM 'for N' decls)
        has_eventually : bool
    """
    # ---- Step 1: scan rule deadlines, watch for 'eventually'. ----
    # After SleecNorm normalization, every finite deadline is a Constant
    # whose str() is the integer count in seconds. If we encounter a
    # deadline that is neither infinite, instantaneous, nor parseable as
    # an integer, that signals an unsupported deadline expression and we
    # fail loudly --- silently treating it as 0 would underestimate
    # T_max and produce an unsound bound.
    has_eventually = False
    T_max = 0
    for nr_idx, nr in enumerate(normalized_rules):
        oc = getattr(nr, "oc", None)
        if oc is None:
            raise RuntimeError(
                f"normalized rule #{nr_idx} has no obligation chain "
                f"(.oc is None). Bound computation requires a valid "
                f"normalization."
            )
        for cobg_idx, cobg in enumerate(oc.obligations):
            obg = getattr(cobg, "obligation", None)
            if obg is None:
                raise RuntimeError(
                    f"normalized rule #{nr_idx}, obligation #{cobg_idx} "
                    f"has no .obligation attribute"
                )
            dl = getattr(obg, "deadline", None)
            if dl is None:
                raise RuntimeError(
                    f"normalized rule #{nr_idx}, obligation #{cobg_idx} "
                    f"has no deadline (.deadline is None)"
                )
            if dl.is_inf():
                has_eventually = True
                break
            if dl.is_inst():
                continue  # Deadline is 0; does not raise T_max.
            try:
                end_val = int(str(dl.end))
            except (ValueError, TypeError) as exc:
                raise RuntimeError(
                    f"could not parse deadline end value {str(dl.end)!r} "
                    f"for normalized rule #{nr_idx}, obligation #{cobg_idx}: "
                    f"{exc}. After SleecNorm normalization, all finite "
                    f"deadlines should be integer constants in seconds."
                )
            if end_val < 0:
                raise RuntimeError(
                    f"negative deadline {end_val} for normalized rule "
                    f"#{nr_idx}, obligation #{cobg_idx}"
                )
            if end_val > T_max:
                T_max = end_val
        if has_eventually:
            break

    if has_eventually:
        return {
            "b_max":          INF,
            "T_max":          INF,
            "rule_count":     len(normalized_rules),
            "h_size":         None,
            "c_hb":           None,
            "c_un":           None,
            "for_durations":  None,
            "has_eventually": True,
        }

    # ---- Step 2: count relation contributions to |H|. ----
    # Only relations with temporal state contribute: happenBefore (1
    # bit per declaration), UntilEM (1 bit), TimedEM (N+1 values per
    # declaration where N is the for-duration in seconds). All other
    # relation kinds are pointwise constraints with no state. Any
    # parse failure on TimedEM's duration is a hard error: after
    # SleecNorm the duration is a Constant in seconds.
    c_hb = 0
    c_un = 0
    for_durations: List[int] = []
    for rel_idx, rel in enumerate(relations):
        cls = type(rel).__name__
        if cls == "EventRelation" and getattr(rel, "op", None) == "happenBefore":
            c_hb += 1
        elif cls == "UntilEMRelation":
            c_un += 1
        elif cls == "TimedEMRelation":
            d = getattr(rel, "duration", None)
            if d is None:
                raise RuntimeError(
                    f"TimedEM relation #{rel_idx} has no .duration "
                    f"attribute. Cannot compute the +1 to relation memory."
                )
            try:
                for_durations.append(int(str(d)))
            except (ValueError, TypeError) as exc:
                raise RuntimeError(
                    f"could not parse TimedEM duration {str(d)!r} "
                    f"(relation #{rel_idx}): {exc}. After SleecNorm "
                    f"normalization, TimedEM durations should be integer "
                    f"constants in seconds."
                )

    # ---- Step 3: assemble |H| and B_max. ----
    h_size = 2 ** (c_hb + c_un)
    for nj in for_durations:
        h_size *= (nj + 1)

    R = len(normalized_rules)
    b_max = (T_max + 2) ** R * h_size

    return {
        "b_max":          b_max,
        "T_max":          T_max,
        "rule_count":     R,
        "h_size":         h_size,
        "c_hb":           c_hb,
        "c_un":           c_un,
        "for_durations":  for_durations,
        "has_eventually": False,
    }


# -----------------------------------------------------------------------------
# Formatting helpers
# -----------------------------------------------------------------------------

def _fmt(x) -> str:
    if x == INF or x is None:
        return "infinity" if x == INF else "n/a"
    if isinstance(x, int) and x.bit_length() > 60:
        # For very large ints, show order-of-magnitude in addition.
        digits = len(str(x))
        return f"{x:,}  (~10^{digits-1})"
    return f"{x:,}" if isinstance(x, int) else str(x)


def _print_result(r: Dict, verbose: bool, prefix: str = "") -> None:
    if r["has_eventually"]:
        print(f"{prefix}B_max = infinity (spec uses `eventually`; "
              f"bounded analysis is sound for unrealizability only)")
        return
    line = (
        f"{prefix}B_max = {_fmt(r['b_max'])}"
        f"   (T_max = {r['T_max']}s,"
        f"  |R| = {r['rule_count']},"
        f"  |H| = {_fmt(r['h_size'])})"
    )
    print(line)
    if verbose:
        print(f"{prefix}  c_hb={r['c_hb']}  c_un={r['c_un']}"
              f"  for_durations={r['for_durations']}")


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Compute the realizability completeness threshold B_max "
                    "for a SLEEC spec."
    )
    ap.add_argument("filename", help="Path to a .sleec spec file.")
    ap.add_argument(
        "--decompose", action="store_true",
        help="Compute the bound per component and report the max + sum.",
    )
    ap.add_argument(
        "-v", "--verbose", action="store_true",
        help="Show breakdown of T_max, |R|, |H|, c_hb, c_un, for-durations.",
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

    import sleecRealizibilityCheck as _rlz
    _rlz._reset_sleecnorm_state()
    from SleecNorm import parse_sleec_norm

    try:
        model, normalized_rules, _AM, _Actions, og_rules, _concerns, relations = \
            parse_sleec_norm(spec_text, read_file=False)
    except Exception as exc:
        print(f"error: parse failure: {exc}", file=sys.stderr)
        return 2

    if not args.decompose:
        result = compute_b_max(normalized_rules, relations)
        _print_result(result, args.verbose)
        return 1 if result["has_eventually"] else 0

    # --decompose: per-component bounds.
    from sleec_decompose import decompose_with_relations
    from sleec_event_classification import classify_events_with_annotations

    try:
        ec = classify_events_with_annotations(model)
        decomp = decompose_with_relations(
            normalized_rules, og_rules, relations, ec
        )
    except Exception as exc:
        print(f"error: decomposition failed: {exc}", file=sys.stderr)
        return 2

    print(f"# {args.filename}: {len(normalized_rules)} rule(s) "
          f"-> {len(decomp.components)} component(s)")

    max_bound, sum_bound = 0, 0
    any_eventually = False
    for i, comp in enumerate(decomp.components, 1):
        comp_nr = [normalized_rules[idx] for idx in comp.rule_indices]
        comp_rel = [relations[idx] for idx in comp.relation_indices]
        global_rel = [relations[idx] for idx in decomp.global_relation_indices]
        result = compute_b_max(comp_nr, comp_rel + global_rel)
        _print_result(result, args.verbose,
                      prefix=f"  Component {i:2d} ({len(comp_nr):3d} rule(s)): ")
        if result["has_eventually"]:
            any_eventually = True
            max_bound, sum_bound = INF, INF
        else:
            max_bound = max(max_bound, result["b_max"])
            sum_bound = sum_bound + result["b_max"]

    print()
    print(f"  per-component max:  {_fmt(max_bound)}")
    print(f"  per-component sum:  {_fmt(sum_bound)}")
    return 1 if any_eventually else 0


if __name__ == "__main__":
    raise SystemExit(main())
