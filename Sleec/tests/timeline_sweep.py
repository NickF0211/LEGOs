"""Sweep the obligation-timeline UI rendering over many specs.

Prints for each (spec, N):
  - verdict
  - #conflict-cells (⚠ markers in the timeline)
  - #culprit_rule tag spans
  - #trigger_event tag spans
  - the timeline text (truncated)

This exercises both the build_timeline builder and the frontend wiring
via the headless harness.
"""

import os
import sys
from collections import Counter


HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, HERE, ANALYZER):
    if p not in sys.path:
        sys.path.insert(0, p)


def run_one(spec_path: str, N: int):
    from ui_headless_smoke import run
    # Reset pysmt/sleecparser global state between runs so scalar
    # measures etc. don't leak (see sleecRealizibilityCheck._reset_sleecnorm_state).
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    cap = run(spec_path, N)
    text = cap.text

    # Extract the timeline section.
    i = text.find("-- Obligation timeline")
    j = text.find("-- Verdict", i) if i >= 0 else -1
    timeline = text[i:j] if i >= 0 and j > i else ""

    # Extract verdict.
    verdict = "?"
    if "UNREALIZABLE" in text:
        verdict = "UNREAL"
    elif "REALIZABLE:" in text:
        verdict = "REAL"

    # Tag summary.
    tags = Counter(tag for _, tag in cap.chunks if tag)

    # Count conflict cells heuristically (one ⚠ per conflict-cell span).
    n_conflict = tags.get("conflict", 0)
    n_culprit = tags.get("culprit_rule", 0)
    n_trigger = tags.get("trigger_event", 0)
    return dict(
        verdict=verdict,
        n_conflict=n_conflict,
        n_culprit=n_culprit,
        n_trigger=n_trigger,
        timeline=timeline,
    )


def main():
    specs = [
        ("demo",              "demo.sleec"),
        ("test",              "test.sleec"),
        ("Amie",              "../Tutorial1/lab1/Amie.sleec"),
        ("Rumba",             "../Tutorial1/lab1/Rumba.sleec"),
        ("demo1",             "../Tutorial1/demo1/demo1.sleec"),
        ("three_disj",        "experiments/specs/three_disjoint.sleec"),
        ("bridge_cascade",    "experiments/specs/bridge_cascade.sleec"),
        ("bridge_measure",    "experiments/specs/bridge_measure.sleec"),
        ("shared_trig_head",  "experiments/specs/shared_trigger_and_head.sleec"),
        ("five_disj",         "experiments/specs/five_disjoint.sleec"),
        ("head_conflict",     "experiments/specs/head_conflict_single_group.sleec"),
    ]
    horizons = [3, 5]

    widths = [18, 3, 8, 10, 8, 8]
    hdr = ("spec", "N", "verdict", "#conflict", "#culprit", "#trig")
    def fmt(cells):
        return "  ".join(str(c).ljust(w)[:w] for c, w in zip(cells, widths))

    print(fmt(hdr))
    print(fmt(["-" * (w - 1) for w in widths]))
    rows = []
    for alias, rel in specs:
        path = rel if os.path.isabs(rel) else os.path.join(SLEEC, rel)
        if not os.path.isfile(path):
            continue
        for N in horizons:
            try:
                info = run_one(path, N)
            except Exception as e:
                print(f"  {alias:18} N={N}  ERROR: {type(e).__name__}: {e}")
                continue
            print(fmt([alias, N, info["verdict"], info["n_conflict"],
                       info["n_culprit"], info["n_trigger"]]))
            rows.append((alias, N, info))

    # NOTE: "potential conflict cells > 0" does NOT imply verdict=UNREAL.
    # The timeline is an over-approximation: it shows obligations that
    # MIGHT coincide on paper, without knowing whether the solver can
    # schedule events to avoid the collision. Rumba is a good example:
    # R4 (StartVacuum -> not StartMoping) and R12 (RequestMoping ->
    # StartMoping unless garbageFull) overlap on StartMoping if both
    # fire, yet the solver can place StartMoping before any StartVacuum,
    # so the spec stays realizable.
    #
    # The timeline is diagnostic: "here's what COULD conflict"; the
    # verdict is authoritative. Specs with verdict UNREAL AND
    # potential conflict cells are the "easy" failure mode.
    print()
    print("Potential-vs-actual conflict correlation:")
    print("  UNREAL verdict AND potential conflict cells > 0 = definite head clash.")
    print("  REAL verdict AND potential conflict cells > 0 = solver dodged it.")
    print()
    real_with_warn = 0
    unreal_with_warn = 0
    for alias, N, info in rows:
        if info["n_conflict"] > 0:
            if info["verdict"] == "UNREAL":
                unreal_with_warn += 1
            elif info["verdict"] == "REAL":
                real_with_warn += 1
                print(f"  {alias} N={N}: potential conflict but verdict REAL "
                      f"(solver dodged the collision)")
    print(f"\nSummary: {unreal_with_warn} definite head clashes, "
          f"{real_with_warn} solver-dodged potential conflicts.")


if __name__ == "__main__":
    main()
