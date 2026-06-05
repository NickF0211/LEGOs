"""Comprehensive validation: every spec at multiple horizons and
multi-iteration. Designed to catch corner-case bugs in the relation
encoders.

Specs covered:
  - 6 existing benchmarks (demo, test, Amie, Rumba, demo1) + their
    annotated counterparts.
  - 6 synthetic decomposition specs (three_disjoint etc.).
  - 8 single-relation-kind specs.
  - 1 contradictory_env stress test.
  - 1 combined_three (3 relations).
  - 1 realistic_alarm (4 relations).
  - 1 realistic_robot (3 relations including UntilEM).
  - 1 edge_n1_happenBefore (boundary case).
  - 1 edge_chain_happenBefore (chained ordering).
  - 1 edge_self_mutex (self-referential mutex).
  - 1 all_kinds_combined (7 relations of all encodable kinds at once).

Total: ~31 specs. Validated at horizons N in {1, 2, 4, 8} where
applicable (N=1 only for boundary cases). max_iter=8.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)

from validate_sampler_relations import validate_spec


SPEC_BATTERY = (
    [   # Existing benchmarks
        "/Users/nicfeng/LEGOs/Sleec/demo.sleec",
        "/Users/nicfeng/LEGOs/Sleec/test.sleec",
        "/Users/nicfeng/LEGOs/Tutorial1/lab1/Amie.sleec",
        "/Users/nicfeng/LEGOs/Tutorial1/lab1/Rumba.sleec",
        "/Users/nicfeng/LEGOs/Tutorial1/demo1/demo1.sleec",
    ]
    + [os.path.join(SLEEC, "experiments/annotated", f)
       for f in ["demo.sleec", "test.sleec", "Amie.sleec",
                 "Rumba.sleec", "demo1.sleec"]]
    + [os.path.join(SLEEC, "experiments/specs", f)
       for f in ["three_disjoint.sleec", "bridge_cascade.sleec",
                 "bridge_measure.sleec", "shared_trigger_and_head.sleec",
                 "five_disjoint.sleec",
                 "head_conflict_single_group.sleec"]]
    + [os.path.join(SLEEC, "experiments/relation_specs", f)
       for f in ["witness_env.sleec", "equal_env.sleec", "mutex_env.sleec",
                 "happenBefore_env.sleec", "causation_env.sleec",
                 "includes_env.sleec", "forbid_env.sleec",
                 "until_em.sleec", "contradictory_env.sleec",
                 "combined_three.sleec",
                 "realistic_alarm.sleec", "realistic_robot.sleec",
                 "edge_n1_happenBefore.sleec",
                 "edge_chain_happenBefore.sleec",
                 "edge_self_mutex.sleec",
                 "all_kinds_combined.sleec"]]
)

# Some N values are only meaningful for some specs. boundary specs run at N=1.
HORIZONS = [2, 4, 8]
EDGE_BOUNDARY = ["edge_n1_happenBefore.sleec"]


def main():
    print(f"{'spec':<55} {'N':>3} {'#trc':>4} {'#rel':>4}  status")
    print("-" * 80)
    bad = 0
    total_traces = 0
    n_skipped = 0
    for path in SPEC_BATTERY:
        if not os.path.isfile(path):
            print(f"  SKIP {os.path.basename(path)} (missing)")
            n_skipped += 1
            continue
        # Determine which horizons to run.
        horizons = HORIZONS[:]
        if any(path.endswith(s) for s in EDGE_BOUNDARY):
            horizons = [1] + HORIZONS
        for N in horizons:
            info = validate_spec(path, N=N, max_iter=8)
            rel = info["path"].replace(SLEEC + "/", "")
            n_traces = info.get("n_traces", 0)
            total_traces += n_traces
            n_relations = info.get("n_relations", 0)
            violations = info.get("violations", [])
            if "error" in info:
                status = f"ERROR: {info['error'][:50]}"
                bad += 1
            elif violations:
                status = f"VIOLATION ({len(violations)})"
                bad += 1
            else:
                status = "ok"
            print(f"  {rel:<55} {N:>3} {n_traces:>4} {n_relations:>4}  {status}")
            for v in violations[:3]:
                print(f"     {v}")
    print()
    print(f"  total traces sampled and validated: {total_traces}")
    print(f"  specs with errors or violations:    {bad}")
    print(f"  specs skipped (missing):            {n_skipped}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
