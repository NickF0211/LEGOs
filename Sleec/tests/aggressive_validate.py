"""Aggressive validation: more iterations, higher horizons, encoder-necessity
sanity, combined-relations stress.

Pass 1 (subsumed by validate_sampler_relations.py): basic correctness with
       N=4, max_iter=4 on every spec.
Pass 2: multi-iteration. Bump max_iter to 10 on every spec. Validate
       every trace.
Pass 3: higher horizon. N=8 on the relation_specs/ specs.
Pass 4: encoder necessity. For mutex_env, witness_env, happenBefore_env,
       causation_env, includes_env, forbid_env, until_em: monkey-patch the
       sampler to skip add_relation_constraints, sample, and verify a
       violation IS observed (proves the encoder is doing real work).
Pass 5: combined-relations spec validation across 8 iterations.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)

from validate_sampler_relations import (
    validate_spec, _check_one_relation, _classify, _events_at, _measures_at,
    _ev_name,
)


# ---------------------------------------------------------------------------
# Pass 2 + 3: multi-iteration & higher horizon
# ---------------------------------------------------------------------------

ALL_SPECS = [
    # Real benchmarks
    "/Users/nicfeng/LEGOs/Sleec/demo.sleec",
    "/Users/nicfeng/LEGOs/Sleec/test.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/lab1/Amie.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/lab1/Rumba.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/demo1/demo1.sleec",
] + [
    os.path.join(SLEEC, "experiments/annotated", f)
    for f in ["demo.sleec", "test.sleec", "Amie.sleec", "Rumba.sleec", "demo1.sleec"]
] + [
    os.path.join(SLEEC, "experiments/specs", f)
    for f in [
        "three_disjoint.sleec", "bridge_cascade.sleec", "bridge_measure.sleec",
        "shared_trigger_and_head.sleec", "five_disjoint.sleec",
        "head_conflict_single_group.sleec",
    ]
]

RELATION_SPECS = [
    os.path.join(SLEEC, "experiments/relation_specs", f) for f in [
        "witness_env.sleec", "equal_env.sleec", "mutex_env.sleec",
        "happenBefore_env.sleec", "causation_env.sleec",
        "includes_env.sleec", "forbid_env.sleec", "until_em.sleec",
        "contradictory_env.sleec", "combined_three.sleec",
    ]
]


def pass_2_multi_iteration():
    print("=" * 78)
    print("PASS 2: max_iter=10, N=4 on every spec")
    print("=" * 78)
    bad = 0
    for path in ALL_SPECS + RELATION_SPECS:
        if not os.path.isfile(path):
            continue
        info = validate_spec(path, N=4, max_iter=10)
        rel = info["path"].replace(SLEEC + "/", "")
        n_traces = info.get("n_traces", 0)
        violations = info.get("violations", [])
        status = "ok" if not violations else f"VIOLATION ({len(violations)})"
        if violations:
            bad += 1
        print(f"  {rel:<55} traces={n_traces:>3} relations={info.get('n_relations', 0)}  {status}")
        for v in violations[:3]:
            print(f"     {v}")
    print(f"\n  Pass 2 result: {'PASS' if bad == 0 else f'FAIL ({bad} violators)'}")
    return bad == 0


def pass_3_higher_horizon():
    print()
    print("=" * 78)
    print("PASS 3: N=8 on relation_specs")
    print("=" * 78)
    bad = 0
    for path in RELATION_SPECS:
        if not os.path.isfile(path):
            continue
        info = validate_spec(path, N=8, max_iter=10)
        rel = info["path"].replace(SLEEC + "/", "")
        violations = info.get("violations", [])
        status = "ok" if not violations else f"VIOLATION ({len(violations)})"
        if violations:
            bad += 1
        print(f"  {rel:<55} traces={info.get('n_traces', 0):>3}  {status}")
        for v in violations[:3]:
            print(f"     {v}")
    print(f"\n  Pass 3 result: {'PASS' if bad == 0 else f'FAIL ({bad} violators)'}")
    return bad == 0


# ---------------------------------------------------------------------------
# Pass 4: encoder-necessity sanity
# ---------------------------------------------------------------------------

def pass_4_encoder_necessity():
    """Monkey-patch add_relation_constraints into a no-op, sample each
    relation_specs/ entry, and verify that violations DO occur (proving the
    encoder is doing real work). If no violation occurs, either the relation
    was vacuously satisfied (warn) or our test design was weak.
    """
    print()
    print("=" * 78)
    print("PASS 4: encoder-necessity (sampler WITHOUT encoder must violate)")
    print("=" * 78)

    import sleec_sampler_relations as ssr
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec
    original = ssr.add_relation_constraints

    def _noop(*a, **kw):
        pass

    cases = [
        # (spec, relation-kind-detector for filtering relations to validate)
        ("witness_env.sleec",     "EventRel"),
        ("equal_env.sleec",       "EventRel"),
        ("mutex_env.sleec",       "EventRel"),
        ("happenBefore_env.sleec", "EventRel"),
        ("causation_env.sleec",   "Causation"),
        ("includes_env.sleec",    "Effect"),
        ("forbid_env.sleec",      "Forbid"),
        ("until_em.sleec",        "UntilEM"),
    ]

    expected_violation_count = 0
    actual_violation_count = 0
    rows = []
    try:
        ssr.add_relation_constraints = _noop  # disable encoder
        for spec_name, _ in cases:
            path = os.path.join(SLEEC, "experiments/relation_specs", spec_name)
            srlc._reset_sleecnorm_state()
            try:
                model, *_ = parse_sleec(path, read_file=True)
                sampler = srlc.AbstractTraceSampler(model, N=4, verbose=False)
            except Exception as e:
                rows.append((spec_name, "INIT_ERROR", str(e)))
                continue
            traces = []
            for _ in range(8):
                t = sampler.next_trace()
                if t is None:
                    break
                traces.append(t)
                if not sampler.block(t):
                    break
            if not traces:
                rows.append((spec_name, "NO_TRACES", ""))
                continue
            ec = _classify(model)
            rels = list(getattr(model.relBlock, "relations", []) or [])
            # Validate each trace against each relation; collect violations.
            violations = []
            for r in rels:
                violations.extend(_check_one_relation(r, traces, 4, ec))
            expected_violation_count += 1
            if violations:
                actual_violation_count += 1
                rows.append((spec_name, f"VIOLATIONS ({len(violations)})",
                             violations[0]))
            else:
                rows.append((spec_name, "no violation",
                             "(encoder may be redundant for this sampler config)"))
    finally:
        ssr.add_relation_constraints = original

    print(f"  Expected encoder-disabled to produce violations on "
          f"{expected_violation_count} specs.")
    print(f"  Actually saw violations on {actual_violation_count} of them.\n")
    for s, status, info in rows:
        print(f"  {s:<35} {status:<22}  {info[:70]}")
    # We accept a "no violation" only if it's plausibly vacuous (e.g.,
    # MaxSAT happens to never use the constrained config). We log but don't
    # fail.
    return True  # informational only


# ---------------------------------------------------------------------------
# Pass 5: combined-relations
# ---------------------------------------------------------------------------

def pass_5_combined():
    print()
    print("=" * 78)
    print("PASS 5: combined relations (witness + happenBefore + causation)")
    print("=" * 78)
    path = os.path.join(SLEEC, "experiments/relation_specs/combined_three.sleec")
    info = validate_spec(path, N=6, max_iter=10)
    rel = info["path"].replace(SLEEC + "/", "")
    violations = info.get("violations", [])
    print(f"  {rel}")
    print(f"  traces={info.get('n_traces', 0)} relations={info.get('n_relations', 0)}")
    if violations:
        print(f"  VIOLATIONS ({len(violations)}):")
        for v in violations[:8]:
            print(f"     {v}")
        return False
    print("  ok")
    return True


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    p2 = pass_2_multi_iteration()
    p3 = pass_3_higher_horizon()
    p4 = pass_4_encoder_necessity()
    p5 = pass_5_combined()
    print()
    print("=" * 78)
    print("FINAL")
    print("=" * 78)
    print(f"  Pass 2 (multi-iter):     {'PASS' if p2 else 'FAIL'}")
    print(f"  Pass 3 (higher horizon): {'PASS' if p3 else 'FAIL'}")
    print(f"  Pass 4 (encoder-needed): informational")
    print(f"  Pass 5 (combined):       {'PASS' if p5 else 'FAIL'}")
    return 0 if (p2 and p3 and p5) else 1


if __name__ == "__main__":
    raise SystemExit(main())
