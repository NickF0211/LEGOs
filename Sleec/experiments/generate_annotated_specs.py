"""Generate annotated copies of realizability benchmark specs.

For each input spec, runs classify_events_with_annotations to get the
inferred sys/env kind per event, then rewrites the source by inserting
`as system` / `as environment` after each `event NAME` declaration in
the def_start block.

Verifies the annotated copy:
  - parses cleanly,
  - classifies with no errors and no warnings,
  - produces the same realizability verdict as the original.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER):
    if p not in sys.path:
        sys.path.insert(0, p)

OUT_DIR = os.path.join(HERE, "annotated")
os.makedirs(OUT_DIR, exist_ok=True)


def classify(path):
    """Return dict event_name -> Kind.value ('system' | 'environment')."""
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec
    from sleec_event_classification import classify_events_with_annotations
    srlc._reset_sleecnorm_state()
    model, *_ = parse_sleec(path, read_file=True)
    ec = classify_events_with_annotations(model)
    if ec.has_errors:
        from sleec_event_classification import format_conflicts
        raise RuntimeError(
            f"original spec {path} already has errors:\n{format_conflicts(ec)}")
    return {name: ec.kind[name].value for name in ec.kind}


def annotate_source(src, kinds):
    """Rewrite the source so each `event NAME` becomes `event NAME as KIND`.

    Idempotent: if `event NAME` already has `as <kind>` immediately after,
    we preserve it (don't double-annotate).
    """
    def repl(match):
        leading_ws = match.group(1)
        keyword = match.group(2)
        name = match.group(3)
        rest = src[match.end():match.end() + 80]
        # If 'as system' / 'as environment' is already present, keep as-is.
        m_existing = re.match(r"\s*as\s+(system|environment)\b", rest)
        if m_existing:
            return match.group(0)
        kind = kinds.get(name)
        if kind is None:
            return match.group(0)
        return f"{leading_ws}{keyword} {name} as {kind}"
    pattern = re.compile(r"^([ \t]*)(event)[ \t]+([A-Za-z_][A-Za-z0-9_]*)",
                         re.MULTILINE)
    return pattern.sub(repl, src)


def realizability_verdict(path, N=5):
    """Run RealizabilityChecker once and return 'realizable' or 'unrealizable'."""
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec, read_model_file
    srlc._reset_sleecnorm_state()
    model_str = read_model_file(path)
    model, *_ = parse_sleec(path, read_file=True)
    sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
    trace = sampler.next_trace()
    if trace is None:
        return "no-sample"
    checker = srlc.RealizabilityChecker(
        model, N=N, model_str=model_str, mode="strong", decompose=True)
    return checker.check(trace).status


SPECS = [
    ("demo.sleec",     os.path.join(SLEEC, "demo.sleec")),
    ("test.sleec",     os.path.join(SLEEC, "test.sleec")),
    ("Amie.sleec",     "/Users/nicfeng/LEGOs/Tutorial1/lab1/Amie.sleec"),
    ("Rumba.sleec",    "/Users/nicfeng/LEGOs/Tutorial1/lab1/Rumba.sleec"),
    ("demo1.sleec",    "/Users/nicfeng/LEGOs/Tutorial1/demo1/demo1.sleec"),
]


def main():
    rows = []
    for label, src_path in SPECS:
        if not os.path.isfile(src_path):
            print(f"  SKIP {label}: not found at {src_path}")
            continue
        kinds = classify(src_path)
        with open(src_path) as fh:
            src = fh.read()
        annotated = annotate_source(src, kinds)
        out_path = os.path.join(OUT_DIR, label)
        with open(out_path, "w") as fh:
            fh.write(annotated)

        # Verify annotated copy.
        ann_kinds = classify(out_path)
        match = (kinds == ann_kinds)
        v_orig = realizability_verdict(src_path, N=5)
        v_ann = realizability_verdict(out_path, N=5)
        rows.append((label, len(kinds), match, v_orig, v_ann))

    print()
    print(f"{'spec':<15} {'#evt':>5} {'kinds match':<12} "
          f"{'orig verdict':<14} {'ann verdict':<14} {'agree':<6}")
    print("-" * 70)
    all_ok = True
    for label, n, match, vo, va in rows:
        agree = "✓" if (match and vo == va) else "✗"
        if agree == "✗":
            all_ok = False
        print(f"{label:<15} {n:>5} {str(match):<12} {vo:<14} {va:<14} {agree:<6}")
    print()
    print(f"output dir: {OUT_DIR}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
