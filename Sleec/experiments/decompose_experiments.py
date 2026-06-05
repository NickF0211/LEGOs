"""decompose_experiments.py — Run a grid of SLEEC specs through the bounded
realizability checker with and without --decompose, and tabulate:
  * #rules (normalized)
  * #components
  * monolithic verdict + time
  * decomposed verdict + time
  * agreement (must always be ✓ if the Decomposition Theorem holds)

Intended as a one-shot experiment harness, NOT a unit test. Runs in a few
minutes on the default spec battery.

Usage:
    cd /Users/nicfeng/LEGOs/Sleec
    python3 experiments/decompose_experiments.py           # default battery
    python3 experiments/decompose_experiments.py --horizon 5 --mode strong
    python3 experiments/decompose_experiments.py --specs demo.sleec test.sleec
"""

import argparse
import os
import sys
import time
from dataclasses import dataclass, field
from typing import List, Optional, Tuple


# Make imports resolvable when run from anywhere.
HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC_DIR = os.path.dirname(HERE)
ANALYZER_DIR = os.path.join(os.path.dirname(SLEEC_DIR), "Analyzer")
for p in (SLEEC_DIR, ANALYZER_DIR):
    if p not in sys.path:
        sys.path.insert(0, p)


# ---------- Default battery of specs --------------------------------------

# Resolved lazily; paths are relative to the Sleec/ dir.
DEFAULT_SPECS = [
    # (alias, relative-or-abs path)
    ("demo",              "demo.sleec"),
    ("test",              "test.sleec"),
    ("Amie",              "../Tutorial1/lab1/Amie.sleec"),
    ("Rumba",             "../Tutorial1/lab1/Rumba.sleec"),
    ("demo1",             "../Tutorial1/demo1/demo1.sleec"),
    # Synthetics (in experiments/specs)
    ("three_disjoint",    "experiments/specs/three_disjoint.sleec"),
    ("bridge_cascade",    "experiments/specs/bridge_cascade.sleec"),
    ("bridge_measure",    "experiments/specs/bridge_measure.sleec"),
    ("shared_trig_head",  "experiments/specs/shared_trigger_and_head.sleec"),
    ("five_disjoint",     "experiments/specs/five_disjoint.sleec"),
    ("head_conflict",     "experiments/specs/head_conflict_single_group.sleec"),
]

HORIZONS = [3, 5]
MODES = ["strong", "weak"]


# ---------- One experiment --------------------------------------------------

@dataclass
class ExpRow:
    alias: str
    path: str
    N: int
    mode: str
    num_rules: int
    num_components: int
    mono_verdict: str = ""
    mono_secs: float = 0.0
    deco_verdict: str = ""
    deco_secs: float = 0.0
    agrees: bool = False
    error: str = ""


def run_one(alias: str, path: str, N: int, mode: str) -> ExpRow:
    """Run both monolithic and decomposed checks on (spec, N, mode)."""
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec, read_model_file
    from SleecNorm import parse_sleec_norm
    from sleec_decompose import decompose_rules

    row = ExpRow(alias=alias, path=path, N=N, mode=mode,
                 num_rules=0, num_components=0)
    try:
        # Reset global state BEFORE any parse call. parse_sleec reads
        # `registered_type` / `scalar_type` / `type_dict` in a way that
        # leaks state across invocations otherwise.
        srlc._reset_sleecnorm_state()

        model_str = read_model_file(path)
        model, *_ = parse_sleec(path, read_file=True)

        # Parse once to count rules/components (needs fresh pysmt env).
        srlc._reset_sleecnorm_state()
        _m, rules_, _Am, _Acts, og_rules_, _c, relations_ = \
            parse_sleec_norm(model_str, read_file=False)
        row.num_rules = len(rules_)
        row.num_components = len(
            decompose_rules(rules_, og_rules_, relations_))

        # Sample a single partial trace (shared between mono and decompose).
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
        trace = sampler.next_trace()
        if trace is None:
            row.error = "sampler produced no trace"
            return row

        # Monolithic.
        ck_mono = srlc.RealizabilityChecker(
            model, N=N, model_str=model_str, mode=mode, decompose=False)
        t0 = time.time()
        v_mono = ck_mono.check(trace)
        row.mono_secs = time.time() - t0
        row.mono_verdict = v_mono.status

        # Decomposed.
        ck_deco = srlc.RealizabilityChecker(
            model, N=N, model_str=model_str, mode=mode, decompose=True)
        t0 = time.time()
        v_deco = ck_deco.check(trace)
        row.deco_secs = time.time() - t0
        row.deco_verdict = v_deco.status

        row.agrees = (v_mono.status == v_deco.status)
    except Exception as e:
        import traceback
        tb = traceback.format_exc()
        row.error = f"{type(e).__name__}: {e}"
        # Dump the full traceback to stderr for debugging.
        print(f"\n=== TRACEBACK for {alias} mode={mode} N={N} ===\n{tb}",
              file=sys.stderr)
    return row


# ---------- Main ------------------------------------------------------------

def main(argv=None):
    p = argparse.ArgumentParser(
        description="Run mono-vs-decompose experiments on SLEEC specs.")
    p.add_argument("--horizon", type=int, nargs="+", default=HORIZONS,
                   help="Horizons to test at (default 3 5).")
    p.add_argument("--mode", choices=MODES + ["both"], default="both",
                   help="Semantics mode (default: both strong and weak).")
    p.add_argument("--specs", nargs="+", default=None,
                   help="Explicit list of spec paths (overrides the default "
                        "battery). Each arg is a filename/path.")
    p.add_argument("--no-weak", action="store_true",
                   help="Skip weak mode (short-hand for --mode strong).")
    args = p.parse_args(argv)

    modes = ["strong", "weak"] if args.mode == "both" else [args.mode]
    if args.no_weak:
        modes = [m for m in modes if m != "weak"]

    # Resolve spec list to (alias, absolute-path).
    specs: List[Tuple[str, str]] = []
    if args.specs:
        for s in args.specs:
            if os.path.isabs(s):
                abs_ = s
            else:
                abs_ = os.path.normpath(os.path.join(SLEEC_DIR, s))
            alias = os.path.splitext(os.path.basename(abs_))[0]
            specs.append((alias, abs_))
    else:
        for alias, rel in DEFAULT_SPECS:
            abs_ = rel if os.path.isabs(rel) else \
                os.path.normpath(os.path.join(SLEEC_DIR, rel))
            if os.path.isfile(abs_):
                specs.append((alias, abs_))
            else:
                print(f"[warn] skipping missing spec: {abs_}", file=sys.stderr)

    # Run the grid.
    rows: List[ExpRow] = []
    for alias, path in specs:
        for mode in modes:
            for N in args.horizon:
                print(f"  running  {alias:20s} mode={mode:6s} N={N} ...",
                      file=sys.stderr, flush=True)
                rows.append(run_one(alias, path, N, mode))

    # Print summary table.
    hdr = ("Spec", "Mode", "N", "#rules", "#comps",
           "mono", "deco", "Δt (s)", "agree", "note")
    cell_widths = [20, 6, 3, 6, 6, 14, 14, 10, 5, 30]
    def fmt(cells):
        return "  ".join(str(c).ljust(w)[:w]
                         for c, w in zip(cells, cell_widths))
    print()
    print(fmt(hdr))
    print(fmt(["-" * (w - 1) for w in cell_widths]))
    all_agree = True
    for r in rows:
        note = r.error or ("speed: "
                           f"{r.mono_secs / r.deco_secs:.2f}x"
                           if r.mono_secs and r.deco_secs else "")
        mono_str = r.mono_verdict or "?"
        deco_str = r.deco_verdict or "?"
        dt = f"{r.deco_secs - r.mono_secs:+.2f}"
        agree = "✓" if r.agrees else "✗"
        if not r.agrees and not r.error:
            all_agree = False
        print(fmt([r.alias, r.mode, r.N, r.num_rules, r.num_components,
                   mono_str, deco_str, dt, agree, note]))

    # Print footer summary.
    total = len(rows)
    agreed = sum(1 for r in rows if r.agrees)
    errors = sum(1 for r in rows if r.error)
    print()
    print(f"total: {total}   agree: {agreed}   errors: {errors}")
    if not all_agree:
        print("FAILURE: at least one mono vs decompose disagreement above!")
        return 1
    if errors:
        print("WARN: errors occurred on some rows (see note column).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
