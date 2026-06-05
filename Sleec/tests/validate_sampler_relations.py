"""Validation harness: run the sampler on every .sleec spec we know,
collect samples, check each sampled trace against each relation's
semantics. Reports any violations.

This catches both:
  - new-encoder bugs (constraints not actually enforced),
  - missing coverage (a relation kind / spec combo we don't handle).

For every spec found, we run AbstractTraceSampler with a small horizon
and pull a handful of traces (blocking between each). For each trace,
we verify all encodable relations hold. Non-encodable kinds (sys-only
event relations, mixed env+sys, sys+measure) are skipped silently.
"""

import os
import sys
from typing import Dict, List, Optional, Set

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)


def _events_at(trace, t):
    for step in trace["per_step"]:
        if step["t"] == t:
            return set(step["events"])
    return set()


def _measures_at(trace, t):
    for step in trace["per_step"]:
        if step["t"] == t:
            return dict(step["measures"])
    return {}


def _ev_name(node):
    """Resolve event-class name from textX Event ref or Trigger node."""
    if node is None:
        return None
    if hasattr(node, "event") and node.event is not None:
        return getattr(node.event, "name", None)
    return getattr(node, "name", None)


def _check_event_rel(rel, traces, N) -> List[str]:
    """Return list of violation messages for an EventRel, or empty if all ok."""
    violations = []
    op = rel.rel
    lhs = _ev_name(rel.lhs)
    rhs = _ev_name(rel.rhs)
    for ti, trace in enumerate(traces):
        for t in range(1, N + 1):
            evs = _events_at(trace, t)
            l = lhs in evs
            r = rhs in evs
            if op == "witness" and l and not r:
                violations.append(f"trace #{ti}: witness {lhs} {rhs} violated at t={t}")
            elif op == "equal" and l != r:
                violations.append(f"trace #{ti}: equal {lhs} {rhs} violated at t={t}")
            elif op == "mutualExclusive" and l and r:
                violations.append(f"trace #{ti}: mutualExclusive {lhs} {rhs} violated at t={t}")
            elif op == "happenBefore" and r:
                earlier = set()
                for tp in range(1, t):
                    earlier.update(_events_at(trace, tp))
                if lhs not in earlier:
                    violations.append(
                        f"trace #{ti}: happenBefore {lhs} {rhs} violated: "
                        f"{rhs}@{t} without earlier {lhs}"
                    )
    return violations


def _eval_mexpr(expr_node, ms):
    """Evaluate a textX MBoolExpr against a measure-record dict.

    Best-effort; returns None if a node type isn't supported (then we skip
    that rel for that step). Mirrors the small fragment _z3_eval_bool_expr
    handles."""
    if expr_node is None:
        return None
    cls = type(expr_node).__name__
    try:
        if cls == "BoolTerminal":
            v = getattr(expr_node, "value", None)
            if v is not None:
                return bool(v)
            ID = getattr(expr_node, "ID", None)
            if ID is not None:
                name = getattr(ID, "name", None)
                if name and name in ms:
                    return bool(ms[name])
            return None
        if cls == "Negation":
            inner = _eval_mexpr(expr_node.expr, ms)
            return None if inner is None else (not inner)
        if cls in ("BoolBinaryOp",):
            op = getattr(expr_node, "op", None)
            l = _eval_mexpr(expr_node.lhs, ms)
            r = _eval_mexpr(expr_node.rhs, ms)
            if l is None or r is None:
                return None
            if op == "and":
                return l and r
            if op == "or":
                return l or r
            return None
        return None
    except Exception:
        return None


def _check_causation(rel, traces, N) -> List[str]:
    """forall t. effect(t) => cause@t."""
    violations = []
    cause = _ev_name(rel.cause)
    for ti, trace in enumerate(traces):
        for t in range(1, N + 1):
            ms = _measures_at(trace, t)
            eff = _eval_mexpr(rel.effect, ms)
            if eff is None:
                continue  # effect not evaluable in our small evaluator
            evs = _events_at(trace, t)
            if eff and cause not in evs:
                violations.append(f"trace #{ti}: causation {cause} {{...}} "
                                  f"violated at t={t}: effect=True, {cause} absent")
    return violations


def _check_effect(rel, traces, N) -> List[str]:
    """forall t. cause@t => effect(t)."""
    violations = []
    cause = _ev_name(rel.cause)
    for ti, trace in enumerate(traces):
        for t in range(1, N + 1):
            evs = _events_at(trace, t)
            if cause not in evs:
                continue
            ms = _measures_at(trace, t)
            eff = _eval_mexpr(rel.effect, ms)
            if eff is None:
                continue
            if not eff:
                violations.append(f"trace #{ti}: includes {cause} {{...}} "
                                  f"violated at t={t}: cause present, effect=False")
    return violations


def _check_forbid(rel, traces, N) -> List[str]:
    violations = []
    cause = _ev_name(rel.cause)
    for ti, trace in enumerate(traces):
        for t in range(1, N + 1):
            evs = _events_at(trace, t)
            if cause not in evs:
                continue
            ms = _measures_at(trace, t)
            eff = _eval_mexpr(rel.effect, ms)
            if eff is None:
                continue
            if eff:
                violations.append(f"trace #{ti}: forbid {cause} {{...}} "
                                  f"violated at t={t}: cause present, effect=True")
    return violations


def _check_until_em(rel, traces, N) -> List[str]:
    """when start [and start_cond] then inv [until end] [and end_cond].

    For each trace, for each t_start where (start@t_start AND start_cond):
        find t_end = next t' > t_start with (end@t' AND end_cond), or N+1
        for t' in [t_start, t_end-1]:
            assert inv(t').
    """
    violations = []
    start_name = _ev_name(rel.start_trigger)
    end_name = _ev_name(rel.end_trigger) if rel.end_trigger is not None else None
    has_end = end_name is not None
    for ti, trace in enumerate(traces):
        for t_start in range(1, N + 1):
            evs = _events_at(trace, t_start)
            if start_name not in evs:
                continue
            ms_start = _measures_at(trace, t_start)
            sc = _eval_mexpr(rel.start_condition, ms_start) if rel.start_condition else True
            if sc is None or not sc:
                continue
            t_end = N + 1
            if has_end:
                for tp in range(t_start, N + 1):
                    evs_tp = _events_at(trace, tp)
                    if end_name in evs_tp:
                        ms_tp = _measures_at(trace, tp)
                        ec = _eval_mexpr(rel.end_condition, ms_tp) if rel.end_condition else True
                        if ec is None or ec:
                            t_end = tp
                            break
            for tp in range(t_start, t_end):
                ms_tp = _measures_at(trace, tp)
                inv = _eval_mexpr(rel.inv, ms_tp)
                if inv is None:
                    continue  # inv not evaluable
                if not inv:
                    violations.append(
                        f"trace #{ti}: UntilEM {start_name}->{end_name} violated: "
                        f"inv False at t={tp} (window [{t_start}, {t_end-1}])")
    return violations


def _classify(model):
    from sleec_event_classification import classify_events_with_annotations
    return classify_events_with_annotations(model)


def _check_one_relation(rel, traces, N, ec) -> List[str]:
    """Dispatch to the right checker. Returns violations."""
    from sleec_event_classification import (
        classify_relation_actors, RelationActorKind, Kind,
    )
    actor_kind = classify_relation_actors(rel, ec)
    cls = type(rel).__name__
    if cls == "EventRel":
        if actor_kind != RelationActorKind.ENV_ONLY_EVENTS:
            return []
        return _check_event_rel(rel, traces, N)
    if cls in ("Causation", "Effect", "Forbid"):
        # only env-cause is encoded; skip otherwise
        cause_name = _ev_name(rel.cause)
        if cause_name is None or ec.kind.get(cause_name) != Kind.ENVIRONMENT:
            return []
        if cls == "Causation":
            return _check_causation(rel, traces, N)
        if cls == "Effect":
            return _check_effect(rel, traces, N)
        if cls == "Forbid":
            return _check_forbid(rel, traces, N)
    if cls == "UntilEM":
        st_name = _ev_name(rel.start_trigger)
        if st_name is None or ec.kind.get(st_name) != Kind.ENVIRONMENT:
            return []
        if rel.end_trigger is not None:
            end_name = _ev_name(rel.end_trigger)
            if end_name is not None and ec.kind.get(end_name) != Kind.ENVIRONMENT:
                return []
        return _check_until_em(rel, traces, N)
    return []


def validate_spec(spec_path, N=4, max_iter=4) -> Dict[str, object]:
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec
    srlc._reset_sleecnorm_state()
    try:
        model, *_ = parse_sleec(spec_path, read_file=True)
    except Exception as e:
        return {"path": spec_path, "error": f"parse failed: {e}"}
    try:
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
    except Exception as e:
        return {"path": spec_path, "error": f"sampler init failed: {e}"}
    traces = []
    for _ in range(max_iter):
        t = sampler.next_trace()
        if t is None:
            break
        traces.append(t)
        if not sampler.block(t):
            break
    if not traces:
        return {"path": spec_path, "n_traces": 0, "violations": []}
    ec = _classify(model)
    relations = list(getattr(model.relBlock, "relations", []) or [])
    violations: List[str] = []
    for rel in relations:
        violations.extend(_check_one_relation(rel, traces, N, ec))
    return {
        "path": spec_path,
        "n_traces": len(traces),
        "n_relations": len(relations),
        "violations": violations,
    }


SPECS = [
    "/Users/nicfeng/LEGOs/Sleec/demo.sleec",
    "/Users/nicfeng/LEGOs/Sleec/test.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/lab1/Amie.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/lab1/Rumba.sleec",
    "/Users/nicfeng/LEGOs/Tutorial1/demo1/demo1.sleec",
] + sorted(
    os.path.join(SLEEC, "experiments/annotated", f)
    for f in ["demo.sleec", "test.sleec", "Amie.sleec", "Rumba.sleec", "demo1.sleec"]
) + sorted(
    os.path.join(SLEEC, "experiments/specs", f)
    for f in [
        "three_disjoint.sleec", "bridge_cascade.sleec", "bridge_measure.sleec",
        "shared_trigger_and_head.sleec", "five_disjoint.sleec",
        "head_conflict_single_group.sleec",
    ]
) + sorted(
    os.path.join(SLEEC, "experiments/relation_specs", f)
    for f in [
        "witness_env.sleec", "equal_env.sleec", "mutex_env.sleec",
        "happenBefore_env.sleec", "causation_env.sleec",
        "includes_env.sleec", "forbid_env.sleec", "until_em.sleec",
    ]
)


def main():
    print(f"{'spec':<55} {'#trc':>5} {'#rel':>5}  status")
    print("-" * 80)
    bad = 0
    for path in SPECS:
        if not os.path.isfile(path):
            print(f"{os.path.basename(path):<55} {'-':>5} {'-':>5}  MISSING")
            continue
        info = validate_spec(path, N=4, max_iter=4)
        rel = info.get("path", path)
        rel = rel.replace(SLEEC + "/", "")
        if "error" in info:
            print(f"{rel:<55} {'-':>5} {'-':>5}  ERROR: {info['error']}")
            bad += 1
            continue
        status = "ok" if not info["violations"] else f"VIOLATION ({len(info['violations'])})"
        if info["violations"]:
            bad += 1
        print(f"{rel:<55} {info['n_traces']:>5} {info['n_relations']:>5}  {status}")
        for v in info["violations"]:
            print(f"   {v}")
    print()
    print(f"specs with errors or violations: {bad}/{len([p for p in SPECS if os.path.isfile(p)])}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
