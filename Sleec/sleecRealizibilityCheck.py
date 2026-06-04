"""Bounded realizability analysis for SLEEC specifications.

This module is a thin pipeline on top of sleecParser / SleecNorm / Analyzer.
It exposes three analyses:

  1. Summarize the spec (events, measures, rules, inferred environment-vs-
     system event roles, the SleecNorm obligation form of each rule).

  2. Sample partial traces that maximize rule triggering over environment
     events + measures. Two samplers:
       - TraceSampler         : concrete per-step SSA over env events + measures.
       - AbstractTraceSampler : per-rule Bool assumption a_{r,t} bound to the
                                rule condition via Iff; env events assumed on.
     Both support streaming multiple distinct traces via ALO blocking.

  3. Check bounded-weak realizability of a sampled (or supplied) partial trace
     via RealizabilityChecker. The check is a pure SLEEC-semantic FOL* query
     built from SleecNorm.encode_limited + Analyzer.check_property_refining --
     no custom z3 encoding, no invented semantics. An obligation whose
     deadline has passed the horizon is treated as vacuously not-violated
     (matches check_situational_conflict own semantics).

See README.md in this folder for a user-facing walkthrough.

Typical CLI usage:
    python3 sleecRealizibilityCheck.py demo.sleec                       # summary
    python3 sleecRealizibilityCheck.py demo.sleec --normalize           # + obligation form
    python3 sleecRealizibilityCheck.py demo.sleec --sample 5 --abstract # partial trace
    python3 sleecRealizibilityCheck.py demo.sleec --sample 5 --abstract --realizability-check
"""
from __future__ import annotations

import argparse
import contextlib
import io
import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

# Make sibling Analyzer/ importable whether launched from the Sleec/ folder
# or elsewhere. Matches the path hack in sleecFrontEnd.py.
_HERE = os.path.dirname(os.path.abspath(__file__))
_ANALYZER = os.path.join(os.path.dirname(_HERE), "Analyzer")
if _ANALYZER not in sys.path:
    sys.path.insert(0, _ANALYZER)

from sleecParser import (  # noqa: E402
    parse_sleec,
    read_model_file,
    isXinstance,
    check_input_conflict,
)


# ---------------------------------------------------------------------------
# Summary from the parsed model
# ---------------------------------------------------------------------------

def print_declarations(model, source_path: Optional[str] = None) -> None:
    """Walk model.definitions and print events / measures / constants."""
    if source_path:
        print(f"=== Declarations in {source_path} ===\n")

    events, bools, nums, scalars, consts = [], [], [], [], []
    for d in model.definitions:
        if isXinstance(d, "Event"):
            events.append(d.name)
        elif isXinstance(d, "BoolMeasure"):
            bools.append(d.name)
        elif isXinstance(d, "NumMeasure"):
            nums.append(d.name)
        elif isXinstance(d, "ScalarMeasure"):
            scalars.append((d.name, [sp.name for sp in d.type.scaleParams]))
        elif isXinstance(d, "Constant"):
            v = d.value
            consts.append((d.name, v.value if v.value is not None else f"-> {v.constant.name}"))

    print(f"Events ({len(events)}):")
    for e in events:
        print(f"  - {e}")

    print(f"\nBoolean measures ({len(bools)}):")
    for m in bools:
        print(f"  - {m}")

    print(f"\nNumeric measures ({len(nums)}):")
    for m in nums:
        print(f"  - {m}")

    print(f"\nScalar measures ({len(scalars)}):")
    for name, params in scalars:
        print(f"  - {name}: scale({', '.join(params)})")

    if consts:
        print(f"\nConstants ({len(consts)}):")
        for name, val in consts:
            print(f"  - {name} = {val}")


def print_rules(model) -> None:
    """One-line summary per rule, reading the textX AST directly."""
    if model.ruleBlock is None:
        return
    rules = model.ruleBlock.rules
    print(f"\nRules ({len(rules)}):")
    for r in rules:
        occ = r.response.occ if r.response is not None else None
        event = occ.event.event.name if occ else "(no response)"
        neg = "not " if (occ and occ.neg) else ""
        within = ""
        if occ and occ.limit and occ.limit.end:
            end = occ.limit.end
            mul = {"seconds": 1, "minutes": 60, "hours": 3600, "days": 86400}.get(end.unit, 1)
            lit = getattr(end.value, "value", None)
            inner = getattr(lit, "value", lit) if lit is not None else None
            if isinstance(inner, int):
                within = f" within {inner * mul}s"
        cond = " [+cond]" if r.condition else ""
        defeaters = f" [+{len(r.response.defeater)} defeater(s)]" if r.response and r.response.defeater else ""
        print(f"  {r.name}: when {r.trigger.event.name}{cond} -> {neg}{event}{within}{defeaters}")


def collect_response_events(response_node, acc: Set[str]) -> None:
    """Recursively collect every event that appears anywhere in a response.

    Walks the full tree:
      - primary `occ.event.event`
      - `alternative.response` (an InnerResponse) — used by `otherwise`
      - `nd.response` (an InnerResponse)          — used by `else`
      - each `defeater[i].response` if present   — used by `unless {..} then {..}`
    All branches count, regardless of negation polarity (`Occ.neg`).
    `InnerResponse` has the same shape as `Response`, so the same walker covers both.
    """
    if response_node is None:
        return
    occ = getattr(response_node, "occ", None)
    if occ is not None and occ.event is not None:
        acc.add(occ.event.event.name)
    alt = getattr(response_node, "alternative", None)
    if alt is not None:
        collect_response_events(alt.response, acc)
    nd = getattr(response_node, "nd", None)
    if nd is not None:
        collect_response_events(nd.response, acc)
    for d in getattr(response_node, "defeater", None) or []:
        collect_response_events(getattr(d, "response", None), acc)


def collect_extended_response_events(ext_response_node, acc: Set[str]) -> None:
    """ExtendedResponse = Response ("while" ExtendedResponse)?. Used in concerns/purposes."""
    if ext_response_node is None:
        return
    collect_response_events(getattr(ext_response_node, "head", None), acc)
    nxt = getattr(ext_response_node, "next", None)
    if nxt is not None:
        collect_extended_response_events(nxt, acc)


def classify_events(model) -> Tuple[List[str], Set[str], Set[str], Set[str], List[str]]:
    """Partition declared events into system vs environment.

    Definitions (per user request):
      - A **response event** (= SYSTEM event) is an event that appears anywhere
        in a Response / InnerResponse / ExtendedResponse tree of any rule,
        concern, or purpose: primary `occ`, the `otherwise` branch, the `else`
        branch, or the consequence of any `unless {…} then {…}` defeater.
        Polarity (the `not` in `Occ.neg`) does not matter.

      - An **environment event** is a declared event that never appears as a
        response event. It may or may not appear as a trigger.

    Additionally we report:
      - `triggers`          : events appearing as the trigger of a
                              Rule / Concern / Purpose / UntilEM / TimedEM.
      - `other_referenced`  : events appearing ONLY inside relation-level
                              constructs (EventRel / Causation / Effect /
                              Forbid / UntilEM / TimedEM). Useful to surface
                              events that are referenced but never directly
                              triggered nor produced as a response.
      - `unused`            : declared events not referenced anywhere.

    Returns: (all_events, triggers, responses, other_referenced, unused).
    """
    all_events = [d.name for d in model.definitions if isXinstance(d, "Event")]
    triggers: Set[str] = set()
    responses: Set[str] = set()
    other_referenced: Set[str] = set()

    def _visit_trigger(trig_node) -> None:
        if trig_node is not None and trig_node.event is not None:
            triggers.add(trig_node.event.name)

    def _visit_event_ref(ev_node, bucket: Set[str]) -> None:
        if ev_node is not None and getattr(ev_node, "name", None) is not None:
            bucket.add(ev_node.name)

    # --- Rules: Rule := "when" trigger ("and" cond)? "then" Response
    if model.ruleBlock is not None:
        for r in model.ruleBlock.rules:
            _visit_trigger(r.trigger)
            collect_response_events(r.response, responses)

    # --- Concerns: both "exists"-form and "when"-form share field names.
    # The response field is an ExtendedResponse. Walk `meanwhile (Headless_Concern)` chain.
    def _walk_concern_like(nodes):
        for node in nodes:
            cur = node
            while cur is not None:
                _visit_trigger(getattr(cur, "trigger", None))
                collect_extended_response_events(getattr(cur, "response", None), responses)
                cur = getattr(cur, "next", None)

    if getattr(model, "concernBlock", None) is not None:
        _walk_concern_like(model.concernBlock.concerns)
    if getattr(model, "purposeBlock", None) is not None:
        _walk_concern_like(model.purposeBlock.purposes)

    # --- Relation block: events here are NEITHER a response NOR (mostly) a
    # direct trigger, but they ARE referenced. We surface them in `other_referenced`.
    # Grammar:
    #   EventRel:   rel=RelType lhs=[Event] rhs=[Event]
    #   Causation:  "causation"  cause=[Event] effect=MBoolExpr
    #   Effect:     "includes"   cause=[Event] effect=MBoolExpr
    #   Forbid:     "forbid"     cause=[Event] effect=MBoolExpr
    #   UntilEM:    "when" start_trigger=Trigger ... ("until" end_trigger=Trigger)? ...
    #   TimedEM:    "when" start_trigger=Trigger ... "for" duration=TimeValue
    if getattr(model, "relBlock", None) is not None:
        for rel in model.relBlock.relations:
            if isXinstance(rel, "EventRel"):
                _visit_event_ref(getattr(rel, "lhs", None), other_referenced)
                _visit_event_ref(getattr(rel, "rhs", None), other_referenced)
            elif isXinstance(rel, "Causation") or isXinstance(rel, "Effect") or isXinstance(rel, "Forbid"):
                _visit_event_ref(getattr(rel, "cause", None), other_referenced)
            elif isXinstance(rel, "UntilEM"):
                # UntilEM uses trigger-style events to bracket the invariant; treat as triggers.
                _visit_trigger(getattr(rel, "start_trigger", None))
                _visit_trigger(getattr(rel, "end_trigger", None))
            elif isXinstance(rel, "TimedEM"):
                _visit_trigger(getattr(rel, "start_trigger", None))
            # MeasureRel / MeasureInv contain no event references, skip.

    # Remove events from `other_referenced` that are already categorized
    # as either triggers or responses — keep it strictly for "only here".
    other_referenced -= (triggers | responses)

    unused = [e for e in all_events if e not in triggers and e not in responses and e not in other_referenced]
    return all_events, triggers, responses, other_referenced, unused


def print_event_roles(model) -> None:
    """Print the environment-vs-system partition per classify_events().

    Per the user's definition: an event is a SYSTEM event iff it appears in a
    response (primary / otherwise / else / defeater-then — any polarity).
    Every other declared event is an ENVIRONMENT event. We additionally
    annotate dual-role events (also a trigger), relation-only events, and
    truly unused events so you can see where each environment event came from.
    """
    all_events, triggers, responses, other_referenced, unused = classify_events(model)

    system = sorted(e for e in all_events if e in responses)
    environment = sorted(e for e in all_events if e not in responses)
    dual = sorted(e for e in system if e in triggers)

    print("\nInferred event roles:")
    print(f"  System events      ({len(system)}): "
          + (", ".join(system) if system else "(none)"))
    print(f"  Environment events ({len(environment)}): "
          + (", ".join(environment) if environment else "(none)"))
    if dual:
        print(f"  (Of the system events, also appearing as a trigger: {', '.join(dual)})")
    if other_referenced:
        print(f"  (Environment events referenced only in relation block: "
              f"{', '.join(sorted(other_referenced))})")
    if unused:
        print(f"  (Environment events never referenced anywhere: {', '.join(sorted(unused))})")

    # Annotation-aware classification: same partition (sys vs env) but
    # respects user `as system|environment` annotations and propagates
    # SYSTEM through relations. Surface any conflicts as warnings here;
    # they only abort when actually running --realizability-check.
    try:
        from sleec_event_classification import (
            classify_events_with_annotations,
            format_classification, format_conflicts,
        )
        ec = classify_events_with_annotations(model)
        if ec.has_errors or ec.has_warnings:
            print()
            print(format_conflicts(ec))
    except Exception as exc:
        # Defensive: never let summary printing crash because of the
        # annotation pass.
        print(f"\n[event-classification] (skipped: {exc!s})")


# ---------------------------------------------------------------------------
# Rule normalization — decompose each rule into Obligation form via SleecNorm
# ---------------------------------------------------------------------------

def _time_window_str(tw) -> str:
    """Pretty-print a SleecNorm TimeWindow as human text, in seconds."""
    if tw.is_inf():
        return "eventually"
    if tw.is_inst():
        return "within 0 seconds (instant)"
    # start may be 0 (default) or a Constant; keep it simple
    if hasattr(tw.start, "val") and tw.start.val != 0:
        return f"within [{tw.start}, {tw.end}] seconds"
    return f"within {tw.end} seconds"


def _obligation_str(obg) -> str:
    """Pretty-print a SleecNorm Obligation (head + deadline)."""
    head = obg.head
    neg = "not " if head.neg else ""
    return f"{neg}{head.expr} {_time_window_str(obg.deadline)}"


def _condition_str(cond) -> str:
    """SleecNorm conditions: literal True/False or a Prop algebra tree."""
    if cond is True:
        return "True"
    if cond is False:
        return "False"
    # The Prop classes all implement __str__/__repr__
    return str(cond)


def print_normalized_rules(model_str: str) -> None:
    """Normalize the rules via SleecNorm and print the obligation form.

    Each SLEEC rule becomes one or more NormalizedRule objects of shape:
        (trigger_event, ObligationChain([Conditional_Obligation(cond, Obligation(head, window))...]))
    Rules with `otherwise` / `else` produce multiple NormalizedRules (one per branch).
    Defeaters end up as extra Conditional_Obligations in the chain, guarded by the
    defeater condition; the rule-level `and <cond>` guard flows into every branch.
    """
    # Lazy import: SleecNorm drags in more state/modules than the plain parser.
    from SleecNorm import parse_sleec_norm

    _model, norm_rules, _amap, _actions, _og, _concerns, _rels = parse_sleec_norm(
        model_str, read_file=False
    )
    print(f"\nNormalized rules ({len(norm_rules)}):")
    for nr in norm_rules:
        src_name = getattr(nr.og_rule, "name", "?")
        print(f"  {src_name}:  trigger = {nr.triggering_event}")
        # Each NormalizedRule carries an ObligationChain of Conditional_Obligations.
        for i, cobg in enumerate(nr.oc.obligations):
            cond = _condition_str(cobg.condition)
            head = _obligation_str(cobg.obligation)
            if cond == "True":
                print(f"    obligation[{i}]: {head}")
            else:
                print(f"    obligation[{i}]: if ({cond}) then {head}")


# ---------------------------------------------------------------------------
# Realizability checks — orchestrate existing LEGOS analyses
# ---------------------------------------------------------------------------

def _capture(fn):
    """Run `fn` while redirecting stdout; return (result, captured_output)."""
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        result = fn()
    return result, buf.getvalue()


def _interpret(res) -> Tuple[bool, str]:
    """Normalize check_input_* / check_situational_conflict return values.

    They return (flag, text, highlights) where flag=True means a problem was
    detected. 'ok' == not flag.
    """
    if isinstance(res, tuple) and len(res) >= 2:
        return (not bool(res[0])), (res[1] if isinstance(res[1], str) else "")
    if isinstance(res, str):
        return True, res
    return True, str(res)


def run_realizability_report(model_str: str, *, skip: Set[str], verbose: bool) -> Tuple[bool, List[Tuple[str, bool, str]]]:
    """Returns (overall_pass, [(step_name, passed, detail), ...])."""
    outcomes: List[Tuple[str, bool, str]] = []

    # 1. Internal consistency — delegates to sleecParser.check_input_conflict
    if "conflict" not in skip:
        if verbose:
            print("[check] internal consistency ...", flush=True)
        res, _ = _capture(lambda: check_input_conflict(model_str))
        ok, detail = _interpret(res)
        outcomes.append((
            "Internal consistency (no rule-level conflicts)",
            ok,
            "No rule-level conflicts." if ok else detail.strip(),
        ))

    # 2. Situational consistency — delegates to SleecNorm.check_situational_conflict
    if "situational" not in skip:
        from SleecNorm import check_situational_conflict
        if verbose:
            print("[check] situational consistency ...", flush=True)
        res, _ = _capture(lambda: check_situational_conflict(model_str))
        ok, detail = _interpret(res)
        outcomes.append((
            "Situational consistency (no stuck obligations)",
            ok,
            "No situational conflicts." if ok else detail.strip(),
        ))

    overall = all(ok for _, ok, _ in outcomes)
    return overall, outcomes


def print_report(outcomes, overall: bool) -> None:
    print("\n=== Realizability report ===")
    width = max((len(name) for name, _, _ in outcomes), default=0)
    for name, ok, detail in outcomes:
        mark = "PASS" if ok else "FAIL"
        print(f"  [{mark}] {name.ljust(width)}  {detail}")
    verdict = "REALIZABLE (under the checks run)" if overall else "NOT realizable"
    print(f"\nOverall: {verdict}\n")


# ---------------------------------------------------------------------------
# Bounded realizability — environment trace sampler (MaxSMT)
# ---------------------------------------------------------------------------
#
# Given an integer N and a SLEEC file, sample an N-point partial trace over
# ENVIRONMENT events + measure valuations that maximally triggers rules.
#
# Per the bounded-realizability formulation:
#   Signature E = M (environment events) ∪ S (system events).
#   Measures θ and any declared measure invariants form project(θ, t).
#   A partial trace of length t assigns a truth value to each environment
#   event and each measure at every time step 1..t.
#
# Encoding here (SSA over boolean variables):
#   - per environment event `e` and time step `i`:   bool `e_i`
#   - per boolean measure `m` and time step `i`:     bool `m_i`
#   - hard constraints  : any MeasureInv / MeasureRel in the relBlock,
#                         instantiated at every time step.
#   - soft constraints  : for each rule `r` and time step `i`,
#                         trigger_event_i ∧ eval(r.condition, measures_i) = True.
#     A soft clause being satisfied means rule `r` fires at time `i`.
#
# MaxSMT maximizes the number of satisfied soft clauses ⇒ the maximum
# triggering partial trace. Corresponds to `maximize(sample(trace_formula))`
# in the bounded-realizability algorithm.
#
# What is NOT (yet) here:
#   - The outer realizability loop: LEGOS(R, p_trace, t) → check feasibility →
#     block subsumed traces → resample.
#   - Numeric or scalar measures in rule conditions (only booleans for now).
#   - Relation-block encodings beyond MeasureInv (EventRel / Causation / etc.).

def _rule_trigger_event_name(rule_node) -> Optional[str]:
    trig = getattr(rule_node, "trigger", None)
    if trig is None or trig.event is None:
        return None
    return trig.event.name


def _collect_all_measure_names(model) -> Tuple[List[str], List[str], List[str]]:
    bools, nums, scalars = [], [], []
    for d in model.definitions:
        if isXinstance(d, "BoolMeasure"):
            bools.append(d.name)
        elif isXinstance(d, "NumMeasure"):
            nums.append(d.name)
        elif isXinstance(d, "ScalarMeasure"):
            scalars.append(d.name)
    return bools, nums, scalars


def _z3_eval_bool_expr(expr_node, ctx):
    """Translate a SLEEC MBoolExpr AST node into a z3 boolean expression.

    `ctx` is a dict with per-step views into all measure and constant vars:
        ctx = {
            "bool":     {measure_name  -> z3.BoolRef},   # boolean measures at step t
            "num":      {measure_name  -> z3.ArithRef},  # numeric measures at step t
            "scalar":   {measure_name  -> z3.ArithRef},  # scalar measures at step t (Int)
            "scaleIdx": {param_name    -> int},          # scale param -> index
            "const":    {constant_name -> int | str},    # named constants
        }
    """
    import z3
    if expr_node is None:
        return z3.BoolVal(True)

    # BoolTerminal : true | false | "{" BoolMeasure "}"
    if isXinstance(expr_node, "BoolTerminal"):
        if getattr(expr_node, "value", None) is not None:
            v = expr_node.value
            if v is True or v == "true":
                return z3.BoolVal(True)
            if v is False or v == "false":
                return z3.BoolVal(False)
            return z3.BoolVal(bool(v))
        if getattr(expr_node, "ID", None) is not None:
            name = expr_node.ID.name
            if name in ctx["bool"]:
                return ctx["bool"][name]
            raise NotImplementedError(f"BoolTerminal references non-boolean measure `{name}`")
        return z3.BoolVal(True)

    # Negation : "(" "not" BoolExp ")"
    if isXinstance(expr_node, "Negation"):
        return z3.Not(_z3_eval_bool_expr(expr_node.expr, ctx))

    # BoolBinaryOp : "(" lhs op rhs ")" where op in {and, or}
    if isXinstance(expr_node, "BoolBinaryOp"):
        lhs = _z3_eval_bool_expr(expr_node.lhs, ctx)
        rhs = _z3_eval_bool_expr(expr_node.rhs, ctx)
        if expr_node.op == "and":
            return z3.And(lhs, rhs)
        if expr_node.op == "or":
            return z3.Or(lhs, rhs)
        raise NotImplementedError(f"Unsupported BoolOp: {expr_node.op}")

    # NumericalOp : "(" NumExp op NumExp ")"
    if isXinstance(expr_node, "NumericalOp"):
        lhs = _z3_eval_num_expr(expr_node.lhs, ctx)
        rhs = _z3_eval_num_expr(expr_node.rhs, ctx)
        return _apply_relop(expr_node.op, lhs, rhs)

    # ScalarBinaryOp : "(" ScalarTerminal op ScalarTerminal ")"
    if isXinstance(expr_node, "ScalarBinaryOp"):
        lhs = _z3_eval_scalar_expr(expr_node.lhs, ctx)
        rhs = _z3_eval_scalar_expr(expr_node.rhs, ctx)
        return _apply_relop(expr_node.op, lhs, rhs)

    raise NotImplementedError(f"Unhandled MBoolExpr node type: {type(expr_node).__name__}")


def _apply_relop(op: str, lhs, rhs):
    """Dispatch on RelOp ∈ {<=, >=, <>, <, >, =}."""
    if op == "<=":  return lhs <= rhs
    if op == ">=":  return lhs >= rhs
    if op == "<":   return lhs < rhs
    if op == ">":   return lhs > rhs
    if op == "=":   return lhs == rhs
    if op == "<>":  return lhs != rhs
    raise NotImplementedError(f"Unsupported RelOp: {op}")


def _z3_eval_num_expr(node, ctx):
    """Translate a NumExp AST node to a z3 arithmetic expression."""
    import z3
    # NumTerminal : Value | "{" NumMeasure "}" | [Constant]
    # Subtlety: textX is permissive about the `[X]` cross-reference check,
    # so `{sound}` (a scalar measure) and `loud` (a scale parameter) both get
    # parsed as NumTerminal.ID. We dispatch on the resolved target's class.
    if isXinstance(node, "NumTerminal"):
        if getattr(node, "value", None) is not None:
            # NumTerminal.value is a Value node (INT literal or constant ref).
            return _z3_eval_value_node(node.value, ctx)
        if getattr(node, "ID", None) is not None:
            target = node.ID
            target_name = getattr(target, "name", None)
            # Numeric measure reference.
            if target_name in ctx["num"]:
                return ctx["num"][target_name]
            # Scalar measure reference — parsed as NumTerminal due to grammar overlap.
            if target_name in ctx["scalar"]:
                return ctx["scalar"][target_name]
            # Scale parameter reference (e.g. `loud`) — resolves to its index.
            if target_name in ctx["scaleIdx"]:
                return z3.IntVal(ctx["scaleIdx"][target_name])
            # Named constant.
            if target_name in ctx["const"]:
                v = ctx["const"][target_name]
                if isinstance(v, int):
                    return z3.IntVal(v)
            raise NotImplementedError(
                f"NumTerminal references unsupported target `{target_name}`")
        return z3.IntVal(0)

    # NumBinOp : "(" NumExp (+|-|*) NumExp ")"
    if isXinstance(node, "NumBinOp"):
        lhs = _z3_eval_num_expr(node.lhs, ctx)
        rhs = _z3_eval_num_expr(node.rhs, ctx)
        if node.op == "+": return lhs + rhs
        if node.op == "-": return lhs - rhs
        if node.op == "*": return lhs * rhs
        raise NotImplementedError(f"Unsupported BinaryArth: {node.op}")

    raise NotImplementedError(f"Unhandled NumExp node: {type(node).__name__}")


def _z3_eval_value_node(node, ctx):
    """Value := INT | "->" Constant. Return a z3 arithmetic expression."""
    import z3
    if node is None:
        return z3.IntVal(0)
    # Plain INT literal: node.value is an int.
    v = getattr(node, "value", None)
    if isinstance(v, int):
        return z3.IntVal(v)
    # Constant reference via the `->` sugar.
    c = getattr(node, "constant", None)
    if c is not None:
        name = getattr(c, "name", None)
        if name in ctx["const"]:
            cv = ctx["const"][name]
            if isinstance(cv, int):
                return z3.IntVal(cv)
        raise NotImplementedError(f"Value references unsupported constant `{name}`")
    return z3.IntVal(0)


def _z3_eval_scalar_expr(node, ctx):
    """ScalarTerminal : "{" ScalarMeasure "}" | ScaleParam ref."""
    import z3
    # ScalarTerminal has either ID (scalar measure ref) or value (ScaleParam ref).
    if isXinstance(node, "ScalarTerminal"):
        if getattr(node, "ID", None) is not None:
            name = node.ID.name
            if name in ctx["scalar"]:
                return ctx["scalar"][name]
            raise NotImplementedError(f"ScalarTerminal references unknown measure `{name}`")
        if getattr(node, "value", None) is not None:
            param_name = node.value.name
            if param_name in ctx["scaleIdx"]:
                return z3.IntVal(ctx["scaleIdx"][param_name])
            raise NotImplementedError(f"Unknown scale parameter `{param_name}`")
    raise NotImplementedError(f"Unhandled ScalarTerminal node: {type(node).__name__}")


# ---------------------------------------------------------------------------
# TraceSampler: stateful, supports streaming multiple traces with ALO blocking.
# ---------------------------------------------------------------------------

class TraceSampler:
    """Stateful MaxSMT trace sampler for bounded realizability.

    Usage:
        sampler = TraceSampler(model, N)
        first  = sampler.next_trace()   # maximum-triggering trace
        sampler.block(first)            # add ALO(~first) to the formula
        second = sampler.next_trace()   # next max-triggering trace that
                                        # triggers at least one env event
                                        # absent from `first`; or None if
                                        # no such trace exists (exhausted).

    The single-shot helper sample_max_triggering_trace() is a thin wrapper
    that creates one sampler and returns its first trace.
    """

    def __init__(self, model, N: int, *, verbose: bool = True):
        import z3
        if N < 1:
            raise ValueError("N must be >= 1")
        self.model = model
        self.N = N
        self.verbose = verbose

        # --- environment events & measures classification ------------------
        # Use the annotation-aware classifier. Its output respects
        # `event X as system|environment` annotations, infers kinds from
        # rule responses, and propagates SYSTEM through relations. If
        # the classifier finds hard-error conflicts (e.g. env-annotated
        # event used as a response), raise EventClassificationError so
        # the realizability run aborts cleanly.
        from sleec_event_classification import (
            classify_events_with_annotations, Kind,
            EventClassificationError,
        )
        ec = classify_events_with_annotations(model)
        if ec.has_errors:
            raise EventClassificationError(ec)
        self.event_classification = ec
        self.env_events = [
            d.name for d in model.definitions
            if isXinstance(d, "Event") and ec.kind.get(d.name) == Kind.ENVIRONMENT
        ]
        self.bool_measures: List[str] = []
        self.num_measures: List[str] = []
        self.scalar_measures: List[Tuple[str, List[str]]] = []
        for d in model.definitions:
            if isXinstance(d, "BoolMeasure"):
                self.bool_measures.append(d.name)
            elif isXinstance(d, "NumMeasure"):
                self.num_measures.append(d.name)
            elif isXinstance(d, "ScalarMeasure"):
                params = [sp.name for sp in d.type.scaleParams]
                self.scalar_measures.append((d.name, params))

        # --- SSA variables -------------------------------------------------
        self.e_vars: Dict[str, List["z3.BoolRef"]] = {
            e: [z3.Bool(f"{e}_{t}") for t in range(1, N + 1)] for e in self.env_events
        }
        self.m_bool_vars: Dict[str, List["z3.BoolRef"]] = {
            m: [z3.Bool(f"{m}_{t}") for t in range(1, N + 1)] for m in self.bool_measures
        }
        self.m_num_vars: Dict[str, List["z3.ArithRef"]] = {
            m: [z3.Int(f"{m}_{t}") for t in range(1, N + 1)] for m in self.num_measures
        }
        self.m_scalar_vars: Dict[str, List["z3.ArithRef"]] = {
            name: [z3.Int(f"{name}_{t}") for t in range(1, N + 1)]
            for name, _params in self.scalar_measures
        }

        # Pull the constants / scale-param indices resolved by sleecParser.
        # Safe: parse_sleec() was called earlier in main() and populates these.
        from sleecParser import constants as _constants, scalar_type as _scalar_type
        self._constants = dict(_constants)
        self._scalar_idx = dict(_scalar_type)

        self.opt = z3.Optimize()

        # Hard: bound each scalar measure to its index range [0, |params|-1].
        for name, params in self.scalar_measures:
            for t in range(N):
                v = self.m_scalar_vars[name][t]
                self.opt.add(v >= 0, v <= len(params) - 1)

        # Hard: measure-level relations (project(theta, t) per step).
        self._add_measure_relations()

        # Hard: env-event-only and env+measure relations encoded into the
        # sampler's z3 Optimize (witness, equal, mutualExclusive,
        # happenBefore, Causation, Effect, Forbid, UntilEM, TimedEM where
        # the relevant actor is an env event).
        from sleec_sampler_relations import add_relation_constraints
        add_relation_constraints(
            self.opt, self.model, self.e_vars,
            self._ctx_at_step, _z3_eval_bool_expr,
            self.event_classification, self.N, verbose=verbose,
        )

        # Soft: per (env-triggered rule, step), assert the rule's trigger pattern.
        self.rule_soft: List[Tuple[str, int, "z3.BoolRef"]] = []
        self._add_rule_soft_clauses()

        if verbose:
            print(f"[sampler] N={N} env_events={self.env_events} "
                  f"bool={self.bool_measures} num={self.num_measures} "
                  f"scalar={[n for n,_ in self.scalar_measures]}")
            print(f"[sampler] {len(self.rule_soft)} soft clauses")

    # -- context builder ---------------------------------------------------
    def _ctx_at_step(self, t_idx: int) -> dict:
        return {
            "bool":     {m: self.m_bool_vars[m][t_idx]   for m in self.bool_measures},
            "num":      {m: self.m_num_vars[m][t_idx]    for m in self.num_measures},
            "scalar":   {n: self.m_scalar_vars[n][t_idx] for n, _ in self.scalar_measures},
            "scaleIdx": self._scalar_idx,
            "const":    self._constants,
        }

    def _add_measure_relations(self) -> None:
        import z3
        rb = getattr(self.model, "relBlock", None)
        if rb is None:
            return
        for rel in rb.relations:
            if isXinstance(rel, "MeasureInv"):
                for t in range(self.N):
                    try:
                        self.opt.add(_z3_eval_bool_expr(rel.expr, self._ctx_at_step(t)))
                    except NotImplementedError as e:
                        if self.verbose:
                            print(f"[sampler] skip MeasureInv @ step {t+1}: {e}", file=sys.stderr)
            elif isXinstance(rel, "MeasureRel"):
                op = rel.rel
                for t in range(self.N):
                    ctx = self._ctx_at_step(t)
                    try:
                        lhs = _z3_eval_bool_expr(rel.lhs, ctx)
                        rhs = _z3_eval_bool_expr(rel.rhs, ctx)
                    except NotImplementedError as e:
                        if self.verbose:
                            print(f"[sampler] skip MeasureRel @ step {t+1}: {e}", file=sys.stderr)
                        continue
                    if op == "imply":
                        self.opt.add(z3.Implies(lhs, rhs))
                    elif op == "iff":
                        self.opt.add(lhs == rhs)
                    elif op == "mutualExclusive":
                        self.opt.add(z3.Implies(lhs, z3.Not(rhs)))
                    elif op == "opposite":
                        self.opt.add(z3.And(z3.Implies(lhs, z3.Not(rhs)),
                                            z3.Implies(rhs, z3.Not(lhs))))

    def _add_rule_soft_clauses(self) -> None:
        import z3
        for r in (self.model.ruleBlock.rules if self.model.ruleBlock else []):
            trig_name = _rule_trigger_event_name(r)
            if trig_name is None or trig_name not in self.env_events:
                continue
            for t in range(self.N):
                ctx = self._ctx_at_step(t)
                try:
                    cond = _z3_eval_bool_expr(r.condition, ctx)
                except NotImplementedError as e:
                    if self.verbose:
                        print(f"[sampler] rule {r.name}: condition not encodable "
                              f"({e}); using trigger-only soft clause.", file=sys.stderr)
                    cond = z3.BoolVal(True)
                clause = z3.And(self.e_vars[trig_name][t], cond)
                self.opt.add_soft(clause, 1)
                self.rule_soft.append((r.name, t + 1, clause))

    # -- public interface --------------------------------------------------
    def next_trace(self) -> Optional[dict]:
        """Return the next maximum-triggering trace, or None if exhausted."""
        import z3
        status = self.opt.check()
        if status != z3.sat:
            return None
        model_z3 = self.opt.model()

        def _b(v) -> bool:
            return bool(model_z3.eval(v, model_completion=True))

        def _i(v) -> int:
            return model_z3.eval(v, model_completion=True).as_long()

        per_step = []
        for t in range(self.N):
            events = {e for e in self.env_events if _b(self.e_vars[e][t])}
            measures: Dict[str, object] = {}
            for m in self.bool_measures:
                measures[m] = _b(self.m_bool_vars[m][t])
            for m in self.num_measures:
                measures[m] = _i(self.m_num_vars[m][t])
            for name, params in self.scalar_measures:
                idx = _i(self.m_scalar_vars[name][t])
                measures[name] = params[idx] if 0 <= idx < len(params) else idx
            per_step.append({"t": t + 1, "events": events, "measures": measures})

        rules_fired = [(name, t) for (name, t, clause) in self.rule_soft if _b(clause)]

        return {
            "N": self.N,
            "environment_events": list(self.env_events),
            "bool_measures": list(self.bool_measures),
            "num_measures": list(self.num_measures),
            "scalar_measures": [n for n, _ in self.scalar_measures],
            "per_step": per_step,
            "rules_fired": rules_fired,
            "num_rule_firings": len(rules_fired),
            "num_soft_clauses": len(self.rule_soft),
        }

    def block(self, trace: dict) -> bool:
        """Add an At-Least-One blocking constraint that forces the next
        sampled trace to fire a (rule, step) combination that `trace` did
        NOT fire.

        The complement is computed at the soft-clause level. Each soft
        clause has the form `env_var(trigger, t) AND condition(rule).at(t)`.
        Two traces that satisfy the same set of soft clauses are considered
        equivalent and are NOT enumerated separately. This captures both:
          - env event presence differences (the previous behavior), AND
          - measure value differences that flip a rule's condition (new).

        Returns False if every soft clause was already satisfied by `trace`,
        meaning no further refinement of the rule-firing pattern is possible
        and the search should stop. In that case no constraint is added.

        Note: rules whose trigger is a system event are not in self.rule_soft,
        so they neither contribute to the MaxSAT objective nor participate in
        blocking. (Cascaded firings happen only at Phase II.)
        """
        import z3
        fired = {(name, t) for (name, t) in trace["rules_fired"]}
        complement = [
            clause for (name, t, clause) in self.rule_soft
            if (name, t) not in fired
        ]
        if not complement:
            return False
        self.opt.add(z3.Or(*complement))
        return True


def sample_max_triggering_trace(model, N: int, verbose: bool = True) -> dict:
    """Back-compat wrapper: return one maximum-triggering trace."""
    sampler = TraceSampler(model, N, verbose=verbose)
    trace = sampler.next_trace()
    if trace is None:
        raise RuntimeError("sampler: optimizer returned unsat on first call")
    return trace


# ---------------------------------------------------------------------------
# AbstractTraceSampler — assumption-based abstraction over rule triggers.
# ---------------------------------------------------------------------------
#
# Design idea (vs the concrete TraceSampler above):
#
#   For each environment-triggered rule `r` and each step `t`, allocate a
#   single fresh Bool `a_{r,t}` that stands for "the trigger CONDITION of `r`
#   holds at step t" (excluding the trigger-event occurrence itself, which is
#   unconstrained for environment events).
#
#   Bind each `a_{r,t}` to its concrete measure predicate via:
#       Iff(a_{r,t}, eval(r.condition, measures_t))
#   where measures_t are the concrete per-step measure variables (z3.Int for
#   numeric/scalar, z3.Bool for boolean). Theory reasoning (e.g. the mutual
#   incompatibility of `batteryLevel < 20` and `batteryLevel >= 20`) is left to
#   z3's DPLL(T) via the Iff binding.
#
#   Maximize `a_{r,t}` (soft, weight 1) ⇒ a measure valuation that enables the
#   maximum number of rule triggerings.
#
#   The *trace* at the abstract level is just the tuple of truth values of
#   `a_{r,t}`. Two concrete measure valuations that enable the same set of
#   rule triggerings are the same abstract trace ⇒ ALO blocking is sharper:
#       block(trace) ≡ Or( a_{r,t} : (r,t) not currently active )
#   If no inactive assumption exists, the abstract search is exhausted.
#
# Environment events are implicitly assumed to be "on" at every step (i.e.
# they are not variables the sampler constrains). Relations over events
# (EventRel, Causation, etc.) are not yet enforced here.

class AbstractTraceSampler:
    """MaxSMT sampler that operates on per-rule abstraction assumptions.

    Usage mirrors TraceSampler:
        sampler = AbstractTraceSampler(model, N)
        trace = sampler.next_trace()
        sampler.block(trace)
    """

    def __init__(self, model, N: int, *, verbose: bool = True):
        import z3
        if N < 1:
            raise ValueError("N must be >= 1")
        self.model = model
        self.N = N
        self.verbose = verbose

        # Classify events: respect user annotations + propagate SYSTEM
        # through relations. Errors abort the run.
        from sleec_event_classification import (
            classify_events_with_annotations, Kind,
            EventClassificationError,
        )
        ec = classify_events_with_annotations(model)
        if ec.has_errors:
            raise EventClassificationError(ec)
        self.event_classification = ec
        self.env_events = [
            d.name for d in model.definitions
            if isXinstance(d, "Event") and ec.kind.get(d.name) == Kind.ENVIRONMENT
        ]

        # Collect measure declarations.
        self.bool_measures: List[str] = []
        self.num_measures: List[str] = []
        self.scalar_measures: List[Tuple[str, List[str]]] = []
        for d in model.definitions:
            if isXinstance(d, "BoolMeasure"):
                self.bool_measures.append(d.name)
            elif isXinstance(d, "NumMeasure"):
                self.num_measures.append(d.name)
            elif isXinstance(d, "ScalarMeasure"):
                self.scalar_measures.append((d.name, [sp.name for sp in d.type.scaleParams]))

        # Per-step measure SSA variables (concrete).
        self.m_bool_vars: Dict[str, List["z3.BoolRef"]] = {
            m: [z3.Bool(f"{m}_{t}") for t in range(1, N + 1)] for m in self.bool_measures
        }
        self.m_num_vars: Dict[str, List["z3.ArithRef"]] = {
            m: [z3.Int(f"{m}_{t}") for t in range(1, N + 1)] for m in self.num_measures
        }
        self.m_scalar_vars: Dict[str, List["z3.ArithRef"]] = {
            name: [z3.Int(f"{name}_{t}") for t in range(1, N + 1)]
            for name, _params in self.scalar_measures
        }
        # Per-step env-event presence Booleans. Previously this sampler
        # treated env events as always-on; that was incorrect for any spec
        # with env-event relations (e.g. mutualExclusive A B between two env
        # events). Now env presence is a free Boolean per (event, step) and
        # the MaxSAT objective drives its values: rules only contribute to
        # the objective when their env trigger is True AND their condition
        # holds, so the optimizer naturally sets e_vars to True at every
        # step that helps fire rules. For specs without env-event relations
        # this reduces to the old "always on" behavior.
        self.e_vars: Dict[str, List["z3.BoolRef"]] = {
            e: [z3.Bool(f"{e}_{t}") for t in range(1, N + 1)]
            for e in self.env_events
        }

        from sleecParser import constants as _constants, scalar_type as _scalar_type
        self._constants = dict(_constants)
        self._scalar_idx = dict(_scalar_type)

        self.opt = z3.Optimize()

        # Scalar bounds per step.
        for name, params in self.scalar_measures:
            for t in range(N):
                v = self.m_scalar_vars[name][t]
                self.opt.add(v >= 0, v <= len(params) - 1)

        # Measure-level invariants (project(theta, t)) per step.
        self._add_measure_relations()

        # Hard: env-event and env+measure relations (witness, equal,
        # mutualExclusive, happenBefore, Causation, Effect, Forbid,
        # UntilEM, TimedEM with env-side actors). Sys-only-event and
        # sys+measure relations are NOT encoded here; the realizability
        # checker errors on the latter at parse time.
        from sleec_sampler_relations import add_relation_constraints
        add_relation_constraints(
            self.opt, self.model, self.e_vars,
            self._ctx_at_step, _z3_eval_bool_expr,
            self.event_classification, self.N, verbose=verbose,
        )

        # Per-rule, per-step abstraction assumption booleans.
        # assumption_vars[(rule_name, step_index)] -> z3.Bool
        self.assumption_vars: Dict[Tuple[str, int], "z3.BoolRef"] = {}
        self._build_assumptions()

        if verbose:
            print(f"[abstract-sampler] N={N} env_events={self.env_events}")
            print(f"[abstract-sampler] {len(self.assumption_vars)} assumption(s) "
                  f"= {len(self.assumption_vars)} soft clause(s)")

    # ---- shared helpers --------------------------------------------------
    def _ctx_at_step(self, t_idx: int) -> dict:
        return {
            "bool":     {m: self.m_bool_vars[m][t_idx]   for m in self.bool_measures},
            "num":      {m: self.m_num_vars[m][t_idx]    for m in self.num_measures},
            "scalar":   {n: self.m_scalar_vars[n][t_idx] for n, _ in self.scalar_measures},
            "scaleIdx": self._scalar_idx,
            "const":    self._constants,
        }

    def _add_measure_relations(self) -> None:
        import z3
        rb = getattr(self.model, "relBlock", None)
        if rb is None:
            return
        for rel in rb.relations:
            if isXinstance(rel, "MeasureInv"):
                for t in range(self.N):
                    try:
                        self.opt.add(_z3_eval_bool_expr(rel.expr, self._ctx_at_step(t)))
                    except NotImplementedError as e:
                        if self.verbose:
                            print(f"[abstract-sampler] skip MeasureInv @ step {t+1}: {e}",
                                  file=sys.stderr)
            elif isXinstance(rel, "MeasureRel"):
                op = rel.rel
                for t in range(self.N):
                    ctx = self._ctx_at_step(t)
                    try:
                        lhs = _z3_eval_bool_expr(rel.lhs, ctx)
                        rhs = _z3_eval_bool_expr(rel.rhs, ctx)
                    except NotImplementedError as e:
                        if self.verbose:
                            print(f"[abstract-sampler] skip MeasureRel @ step {t+1}: {e}",
                                  file=sys.stderr)
                        continue
                    if op == "imply":
                        self.opt.add(z3.Implies(lhs, rhs))
                    elif op == "iff":
                        self.opt.add(lhs == rhs)
                    elif op == "mutualExclusive":
                        self.opt.add(z3.Implies(lhs, z3.Not(rhs)))
                    elif op == "opposite":
                        self.opt.add(z3.And(z3.Implies(lhs, z3.Not(rhs)),
                                            z3.Implies(rhs, z3.Not(lhs))))

    def _build_assumptions(self) -> None:
        """For each (env-triggered rule, step) allocate a fresh Bool assumption,
        bind it to the rule's concrete measure condition via Iff, and add it
        as a weight-1 soft clause to the optimizer."""
        import z3
        for r in (self.model.ruleBlock.rules if self.model.ruleBlock else []):
            trig_name = _rule_trigger_event_name(r)
            if trig_name is None or trig_name not in self.env_events:
                continue
            for t in range(self.N):
                ctx = self._ctx_at_step(t)
                try:
                    cond = _z3_eval_bool_expr(r.condition, ctx)
                except NotImplementedError as e:
                    if self.verbose:
                        print(f"[abstract-sampler] rule {r.name} @ step {t+1}: "
                              f"condition not encodable ({e}); assumption := True",
                              file=sys.stderr)
                    cond = z3.BoolVal(True)
                a = z3.Bool(f"assume__{r.name}__{t+1}")
                # Bind the abstraction assumption to (env trigger present at t)
                # AND (concrete measure condition at t). MaxSAT thus jointly
                # picks env-event presence and measure values to maximize
                # rule firings.
                self.opt.add(a == z3.And(self.e_vars[trig_name][t], cond))
                # Maximize satisfied assumptions.
                self.opt.add_soft(a, 1)
                self.assumption_vars[(r.name, t + 1)] = a

    # ---- public interface ------------------------------------------------
    def next_trace(self) -> Optional[dict]:
        """Return the next maximum-triggering abstract trace, or None if unsat."""
        import z3
        status = self.opt.check()
        if status != z3.sat:
            return None
        model_z3 = self.opt.model()

        def _b(v) -> bool:
            return bool(model_z3.eval(v, model_completion=True))

        def _i(v) -> int:
            return model_z3.eval(v, model_completion=True).as_long()

        per_step = []
        for t in range(self.N):
            # Env-event presence is now a free Boolean per (event, step).
            # Read it from the model.
            events = {e for e in self.env_events if _b(self.e_vars[e][t])}
            measures: Dict[str, object] = {}
            for m in self.bool_measures:
                measures[m] = _b(self.m_bool_vars[m][t])
            for m in self.num_measures:
                measures[m] = _i(self.m_num_vars[m][t])
            for name, params in self.scalar_measures:
                idx = _i(self.m_scalar_vars[name][t])
                measures[name] = params[idx] if 0 <= idx < len(params) else idx
            per_step.append({"t": t + 1, "events": events, "measures": measures})

        rules_fired = [(name, step) for (name, step), a in self.assumption_vars.items()
                       if _b(a)]
        rules_fired.sort(key=lambda rt: (rt[1], rt[0]))

        return {
            "N": self.N,
            "environment_events": list(self.env_events),
            "bool_measures": list(self.bool_measures),
            "num_measures": list(self.num_measures),
            "scalar_measures": [n for n, _ in self.scalar_measures],
            "per_step": per_step,
            "rules_fired": rules_fired,
            "num_rule_firings": len(rules_fired),
            "num_soft_clauses": len(self.assumption_vars),
            "abstraction": "per-rule",
        }

    def block(self, trace: dict) -> bool:
        """ALO blocking over the abstract trace: require at least one
        currently-inactive assumption to become true in the next sample.

        Returns False if every assumption is already active (saturated)."""
        import z3
        active = {(name, t) for (name, t) in trace["rules_fired"]}
        inactive_vars = [a for (name, t), a in self.assumption_vars.items()
                         if (name, t) not in active]
        if not inactive_vars:
            return False
        self.opt.add(z3.Or(*inactive_vars))
        return True


# ---------------------------------------------------------------------------
# RealizabilityChecker — REMOVED.
# ---------------------------------------------------------------------------
#
# The previous implementation used a custom z3/MaxSMT encoding with per-step
# SSA variables for events and measures, plus per-rule selection literals for
# partial-realizability diagnosis. That encoding diverged from the canonical
# SLEEC semantics used by the rest of the LEGOS pipeline (check_conflict,
# check_situational_conflict, etc.), which operate over FOL* formulas via
# SleecNorm's `encode_limited` and `Analyzer.check_property_refining`.
#
# TODO: reimplement `RealizabilityChecker.check(trace)` on top of SLEEC
# semantics:
#   1. Parse the spec with `SleecNorm.parse_sleec_norm` to get the
#      NormalizedRules plus the FOL* Action_Mapping.
#   2. Build the bounded-satisfaction query via `nr.encode_limited(...)`:
#           AND( measure_inv,
#                blocked_axioms,
#                relational_constraints,
#                *[ nr.encode_limited(c_measure, A_Mapping) for nr in rules ],
#                trace_assertions(partial_trace) )
#      where `trace_assertions` converts the sampled partial trace into FOL*
#      assertions pinning env events and measure snapshots per step.
#   3. Solve with `check_property_refining(..., ret_model=True)`. SAT means
#      the partial trace is realizable in the current bound.
#   4. For partial-realizability diagnosis, either (a) iteratively drop rules
#      using the UNSAT-core-guided subset search (mirroring the
#      partial_validity.py algorithm we reviewed), or (b) rely on the
#      situational-conflict analysis's UNSAT-core extraction for culprit
#      identification.
#
# Until the rewrite lands, `RealizabilityChecker.check(...)` raises
# NotImplementedError so no code silently gets a wrong answer. Callers should
# gate any realizability-check calls on feature availability.

@dataclass
class RealizabilityVerdict:
    status: str            # "realizable", "partially_realizable", "unrealizable"
    selected_rules: List[str]
    culprit_rules: List[str]
    system_events_schedule: Dict[int, Set[str]]

    def __str__(self) -> str:
        if self.status == "realizable":
            return f"REALIZABLE: all {len(self.selected_rules)} rule(s) satisfiable."
        if self.status == "partially_realizable":
            return (f"PARTIALLY REALIZABLE: {len(self.selected_rules)} of "
                    f"{len(self.selected_rules) + len(self.culprit_rules)} rule(s) "
                    f"selected; culprit(s): {', '.join(self.culprit_rules)}.")
        return "UNREALIZABLE: even the empty rule set cannot realize this trace."


def _reset_sleecnorm_state() -> None:
    """SleecNorm (via sleecParser) keeps module-level state that accumulates
    across parse_sleec_norm calls. Wipe everything between invocations so we
    don't inherit obligations / actions / registered scalar types from earlier
    calls (including earlier check_situational_conflict runs)."""
    import sleecParser
    sleecParser.constants.clear()
    sleecParser.scalar_type.clear()
    sleecParser.scalar_mask.clear()
    sleecParser.registered_type.clear()
    try:
        import type_constructor
        for attr in ("request_action_map", "attribute_variable_map", "exception_map"):
            coll = getattr(type_constructor, attr, None)
            if coll is not None:
                coll.clear()
    except Exception:
        pass
    try:
        import SleecNorm as _sn
        _sn.Obligation.Obg_by_head.clear()
        _sn.Constant.Constant_map.clear()
        _sn.blocked_actions.clear()
    except Exception:
        pass
    # pysmt caches Symbol definitions globally; if two SLEEC specs use the
    # same action name (e.g. "Measure") with different attribute lists, the
    # second parse_sleec_norm will raise PysmtTypeError on Symbol redefinition.
    # Resetting the pysmt env avoids that. NOTE: this invalidates any pysmt
    # FNodes held elsewhere, so callers must not keep FNodes across resets.
    try:
        from pysmt.environment import reset_env, get_env
        reset_env()
        # The Analyzer code uses infix notation (e.g. `measure.time <= t`).
        # pysmt's default env enables it, but `reset_env()` produces a fresh
        # env with the setting at its factory default — re-enable it here.
        try:
            get_env().enable_infix_notation = True
        except Exception:
            pass
    except Exception:
        pass


class RealizabilityChecker:
    """Bounded-weak realizability check over SLEEC FOL* semantics.

    Given a SLEEC model, a horizon N, and an environment partial trace, ask:
      "Does the partial trace admit a bounded extension under which every
       SLEEC rule is NOT VIOLATED within the horizon?"

    Implementation mirrors `SleecNorm.check_situational_conflict` exactly,
    minus the rule-forcing clauses (triggered_now + blocked). All primitives
    come from SleecNorm/Analyzer:

      * `parse_sleec_norm`                  — normalized rules + Action_Mapping
      * `NormalizedRule.encode_limited`     — per-rule bounded obligation
      * `add_blocked_obgs` / `get_blocked_axioms` / `process_conflict`
      * `get_relational_constraints`        — event/measure relations
      * `exist`, `forall`, `EQ`, `AND`, `NOT` from logic_operator
      * `pysmt.shortcuts.Int`               — integer literals for .time comparisons
      * `check_property_refining`           — the FOL* solver

    Trace assertions take the form:
      * Event: `exist(EventClass, lambda e: EQ(e.time, Int(t)))`
      * Measure snapshot at t with bool field `f` true:
          `exist(Measure, lambda m: AND(EQ(m.time, Int(t)), m.f))`
        with `NOT(m.f)` for false, `EQ(m.f, Int(v))` for numeric/scalar.
      * Horizon anchor: `EQ(c_measure.time, Int(N))`.

    SEMANTICS NOTE (important): `encode_limited` implements the paper's
    BOUNDED WEAK realizability. An obligation whose deadline has passed the
    horizon is vacuously "not violated". This is intentional in the research
    code. For strong realizability (every triggered obligation discharged
    within its deadline), a different encoding is required — see the
    observations in the module-level TODO.

    Verdict:
      * SAT    → REALIZABLE   (partial trace admits a bounded extension)
      * UNSAT  → UNREALIZABLE (rules forbid this partial trace outright)
    Culprit-set diagnosis via partial-validity is NOT implemented here.
    """

    def __init__(self, model, N: int, *, model_str: Optional[str] = None,
                 mode: str = "strong", decompose: bool = False):
        if N < 1:
            raise ValueError("N must be >= 1")
        if not model_str:
            raise ValueError(
                "RealizabilityChecker requires the raw SLEEC source text. "
                "Pass model_str=<file contents> so parse_sleec_norm can run."
            )
        if mode not in ("strong", "weak"):
            raise ValueError(f"mode must be 'strong' or 'weak', got {mode!r}")
        self.model = model
        self.N = N
        self.model_str = model_str
        self.mode = mode
        self.decompose = decompose

    def check(self, trace: dict, *, verbose: bool = False) -> RealizabilityVerdict:
        """Run the bounded realizability check against `trace`.

        `trace` is the dict shape produced by AbstractTraceSampler / TraceSampler:
          {
            "N": int,
            "per_step": [ {"t": int, "events": set[str], "measures": {name: val}} ],
            ...
          }
        Only `per_step` is consumed here.

        If `self.decompose` is True, the rules are partitioned into
        components via the rule-dependency graph (see sleec_decompose.py),
        and each component is checked independently. The overall verdict
        is UNREALIZABLE iff any component is UNREALIZABLE. Under the
        Decomposition Theorem, this is equivalent to the monolithic check.
        """
        # Lazy imports: these modules have side effects on import (the Analyzer
        # package initializes global state when first loaded).
        from pysmt.shortcuts import Int
        from logic_operator import AND, NOT, EQ, Implication, exist, forall
        from analyzer import check_property_refining, clear_all
        from SleecNorm import (parse_sleec_norm, add_blocked_obgs, process_conflict,
                                get_blocked_axioms)
        from sleecParser import (get_relational_constraints, scalar_mask,
                                  clear_relational_constraints, reset_rules)
        import derivation_rule

        # --- 1. Parse the spec via SleecNorm. ---------------------------------
        _reset_sleecnorm_state()
        _model, rules, Action_Mapping, Actions, og_rules, _concerns, relations = \
            parse_sleec_norm(self.model_str, read_file=False)

        Measure = Action_Mapping["Measure"]
        c_measure = Measure()
        measure_inv = forall(
            [Measure, Measure],
            lambda m1, m2: Implication(EQ(m1.time, m2.time), EQ(m1, m2))
        )
        add_blocked_obgs(Actions, rules)
        process_conflict(relations)

        # --- 2. Decide partitioning. -----------------------------------------
        # og_rules has one entry per AST Rule; `rules` (normalized) can have
        # multiple entries per AST Rule (one per obligation/defeater branch).
        # Build a mapping from normalized-rule index to og-rule index using
        # identity on the shared AST node (`nr.og_rule` IS the AST Rule).
        rule_nodes = _model.ruleBlock.rules
        ast_to_og_idx = {id(n): i for i, n in enumerate(rule_nodes)}
        nr_to_og_idx = [ast_to_og_idx[id(nr.og_rule)] for nr in rules]

        if self.decompose:
            from sleec_decompose import (decompose_rules, describe_components,
                                          has_polarity_clash,
                                          decompose_with_relations)
        else:
            from sleec_decompose import has_polarity_clash  # noqa: F401

        # --- 3. Build the common background (same in every component solve).
        # Phase II FOL* query for each component is the conjunction of:
        #   (i) the measure invariant,
        #  (ii) each rule in the component's encoded form,
        # (iii) relations belonging to the component (coupling) plus
        #       relations that are global (measure-only / measure-invariant),
        #  (iv) the partial-trace assertions.
        # Relations that mix system events with measures are not yet
        # supported and abort the run here. See classify_relation_actors.
        from sleec_event_classification import (
            classify_events_with_annotations, classify_relation_actors,
            RelationActorKind, RelationClassificationError,
        )
        ec_for_relations = classify_events_with_annotations(_model)
        offenders = []
        for rel in relations:
            actor_kind = classify_relation_actors(rel, ec_for_relations)
            if actor_kind in (RelationActorKind.SYS_EVENT_AND_MEASURE,
                              RelationActorKind.MIXED_AND_MEASURE):
                offenders.append((rel, actor_kind))
        if offenders:
            raise RelationClassificationError(offenders=offenders)

        # Decompose rules + relations together.
        if self.decompose:
            decomposition = decompose_with_relations(
                rules, og_rules, relations, ec_for_relations,
            )
            components_struct = decomposition.components
            global_relations = [relations[i]
                                for i in decomposition.global_relation_indices]
            if verbose:
                print(f"[realizability] decomposed into "
                      f"{len(components_struct)} component(s); "
                      f"{len(global_relations)} global relation(s)",
                      file=sys.stderr)
                # Describe rule clusters using the legacy formatter.
                legacy = [c.rule_indices for c in components_struct]
                print(describe_components(rules, legacy), file=sys.stderr)
        else:
            # Single monolithic component containing every rule and every
            # eligible relation. (Measure-only and other empty-alphabet
            # relations are folded into the same component for simplicity.)
            from sleec_decompose import Component
            kept_rel_indices = []
            for ri, rel in enumerate(relations):
                kind = classify_relation_actors(rel, ec_for_relations)
                # Skip MIXED_ENV_SYS_EVENTS (deferred); other eligible kinds keep.
                if kind in (RelationActorKind.SYS_EVENT_AND_MEASURE,
                            RelationActorKind.MIXED_AND_MEASURE,
                            RelationActorKind.MIXED_ENV_SYS_EVENTS):
                    continue
                kept_rel_indices.append(ri)
            components_struct = [Component(
                rule_indices=list(range(len(rules))),
                relation_indices=kept_rel_indices,
            )]
            global_relations = []

        # Encode the global relations once; reused in every per-component solve.
        global_relational_constraints = get_relational_constraints(global_relations)

        # Build the trace assertions once; they are asserted in every
        # per-component solve. (Environment events and measure snapshots
        # must be visible inside every component query so that triggers
        # fire as the seed intends.)
        trace_assertions = []
        if self.mode == "weak":
            trace_assertions.append(EQ(c_measure.time, Int(self.N)))
        for step in trace["per_step"]:
            t = step["t"]
            t_lit = Int(t)
            for ev_name in step.get("events", ()):
                if ev_name not in Action_Mapping:
                    if verbose:
                        print(f"[realizability] skipping unknown event "
                              f"{ev_name!r}", file=sys.stderr)
                    continue
                ev_class = Action_Mapping[ev_name]
                trace_assertions.append(
                    exist(ev_class, lambda e, t=t_lit: EQ(e.time, t))
                )
            measure_clauses = []
            for m_name, val in step.get("measures", {}).items():
                clause = self._measure_field_clause(m_name, val, verbose=verbose)
                if clause is not None:
                    measure_clauses.append(clause)
            if measure_clauses:
                def measure_body(m, t=t_lit, clauses=measure_clauses):
                    parts = [EQ(m.time, t)] + [c(m) for c in clauses]
                    return AND(parts) if len(parts) > 1 else parts[0]
                trace_assertions.append(exist(Measure, measure_body))
            else:
                trace_assertions.append(
                    exist(Measure, lambda m, t=t_lit: EQ(m.time, t))
                )

        # --- 4. Per-component solve loop. ------------------------------------
        # Short-circuit as soon as any component is UNREALIZABLE.
        overall_status = "realizable"
        culprit_component_idx = None
        short_circuited: List[int] = []   # 1-based indices realizable by inspection
        for ci, comp in enumerate(components_struct):
            comp_rule_indices = comp.rule_indices
            comp_relation_indices = comp.relation_indices
            # Short-circuit only when the component carries no relations.
            # Relations can introduce UNSAT that polarity-clash cannot see
            # (e.g., mutualExclusive between two positive sys heads).
            if (not comp.has_relations and
                    not has_polarity_clash(rules, comp_rule_indices)):
                short_circuited.append(ci + 1)
                if verbose:
                    print(f"[realizability] component {ci+1}/"
                          f"{len(components_struct)}: no polarity clash, "
                          "realizable by inspection",
                          file=sys.stderr)
                continue

            # Encode this component's relations + always-on global ones.
            comp_relations = [relations[i] for i in comp_relation_indices]
            comp_relational_constraints = get_relational_constraints(comp_relations)

            # Build per-component rule clauses.
            fol_rules = [measure_inv]
            fol_rules.extend(global_relational_constraints)
            fol_rules.extend(comp_relational_constraints)
            if self.mode == "strong":
                # Strong mode uses per-WhenRule encoding. Deduplicate the
                # og_rules indices because multiple normalized rules may
                # share the same og_rule (primary + defeater branches).
                og_idx_set = sorted({nr_to_og_idx[i] for i in comp_rule_indices})
                for og_idx in og_idx_set:
                    fol_rules.append(og_rules[og_idx].get_rule())
            else:
                fol_rules.append(c_measure.presence)
                fol_rules.extend(get_blocked_axioms(Action_Mapping, c_measure))
                for idx in comp_rule_indices:
                    fol_rules.append(
                        rules[idx].encode_limited(c_measure, Action_Mapping)
                    )

            query = AND(fol_rules + trace_assertions)
            if verbose:
                print(f"[realizability] component {ci+1}/{len(components_struct)}: "
                      f"{len(fol_rules)} rule clauses, "
                      f"{len(trace_assertions)} trace assertions, "
                      f"horizon N={self.N}", file=sys.stderr)
            res = check_property_refining(
                query, set(), set(),
                Actions, [], True,
                min_solution=False, final_min_solution=True,
                restart=False, boundary_case=False,
                universal_blocking=False, vol_bound=200,
                ret_model=True, scalar_mask=scalar_mask,
            )
            if not isinstance(res, tuple):
                # UNSAT on this component ⇒ whole spec unrealizable.
                overall_status = "unrealizable"
                culprit_component_idx = ci
                break  # short-circuit

        # --- 5. Clean up global state mutated by check_property_refining. ----
        try:
            clear_all(Actions)
            reset_rules(og_rules)
            measure_inv.clear()
            clear_relational_constraints(relational_constraints)
            derivation_rule.reset()
        except Exception:
            pass  # best-effort cleanup

        # --- 6. Interpret. ---------------------------------------------------
        all_rule_names = [getattr(nr.og_rule, "name", "?") for nr in rules]
        if overall_status == "realizable":
            return RealizabilityVerdict(
                status="realizable",
                selected_rules=all_rule_names,
                culprit_rules=[],
                system_events_schedule={},
            )
        # unrealizable; narrow culprit to the failing component's rule names.
        culprit_names = (
            [getattr(rules[i].og_rule, "name", "?")
             for i in components_struct[culprit_component_idx].rule_indices]
            if culprit_component_idx is not None else all_rule_names
        )
        return RealizabilityVerdict(
            status="unrealizable",
            selected_rules=[],
            culprit_rules=culprit_names,
            system_events_schedule={},
        )

    # ----------------------------------------------------------------------
    # Helpers
    # ----------------------------------------------------------------------

    def _measure_field_clause(self, name, val, *, verbose: bool):
        """Build a callable `lambda m: <predicate over m.<name>>` matching the
        trace's measure value. Returns None if the measure is unknown / we
        cannot encode it.

        Supported:
          * bool:   True -> m.name,  False -> NOT(m.name)
          * int:    EQ(m.name, Int(val))
          * scalar: val is a param label (str). Resolve to its index via
                    sleecParser.scalar_type[val] and emit EQ(m.name, Int(idx)).
        """
        from pysmt.shortcuts import Int
        from logic_operator import EQ, NOT
        import sleecParser

        # Figure out what kind of measure this is by looking at the model defs.
        m_def = None
        for d in self.model.definitions:
            if isXinstance(d, "Measure") and getattr(d, "name", None) == name:
                m_def = d
                break
        if m_def is None:
            if verbose:
                print(f"[realizability] unknown measure {name!r}", file=sys.stderr)
            return None

        if isXinstance(m_def, "BoolMeasure"):
            if val:
                return lambda m, n=name: getattr(m, n)
            return lambda m, n=name: NOT(getattr(m, n))
        if isXinstance(m_def, "NumMeasure"):
            if isinstance(val, bool) or not isinstance(val, int):
                if verbose:
                    print(f"[realizability] numeric measure {name!r} got {val!r}",
                          file=sys.stderr)
                return None
            return lambda m, n=name, v=Int(val): EQ(getattr(m, n), v)
        if isXinstance(m_def, "ScalarMeasure"):
            # val may be the param label (e.g. "loud") or already an int index.
            if isinstance(val, int):
                idx = val
            else:
                idx = sleecParser.scalar_type.get(val)
                if idx is None:
                    if verbose:
                        print(f"[realizability] unknown scalar param {val!r} "
                              f"for measure {name!r}", file=sys.stderr)
                    return None
            return lambda m, n=name, v=Int(idx): EQ(getattr(m, n), v)
        return None


def print_sampled_trace(result, *, index: Optional[int] = None) -> None:
    N = result["N"]
    header = "Maximum-triggering partial trace"
    if index is not None:
        header = f"Trace #{index} (maximum-triggering)"
    print(f"\n=== {header} (N={N}) ===")
    print(f"Environment events: {', '.join(result['environment_events']) or '(none)'}")
    all_ms = (result.get("bool_measures", []) +
              result.get("num_measures", []) +
              result.get("scalar_measures", []))
    if all_ms:
        print(f"Measures:           {', '.join(all_ms)}")
    print(f"Rule firings:       {result['num_rule_firings']} / "
          f"{result['num_soft_clauses']} soft clauses satisfied")
    print()
    for step in result["per_step"]:
        t = step["t"]
        events = sorted(step["events"])
        events_str = ", ".join(events) if events else "(no env event)"
        measure_pairs = []
        for m, v in sorted(step["measures"].items()):
            if isinstance(v, bool):
                measure_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                measure_pairs.append(f"{m}={v}")
        measures_str = ", ".join(measure_pairs)
        sep = "  | " if measures_str else ""
        print(f"  t={t}: {events_str}{sep}{measures_str}")
    if result["rules_fired"]:
        print("\nTriggered (rule, step):")
        for name, t in result["rules_fired"]:
            print(f"  - {name} @ t={t}")


def print_realizability_result(trace: dict, verdict: "RealizabilityVerdict",
                                *, index: Optional[int] = None) -> None:
    """Print the outcome of a bounded-weak realizability check on a trace.

    Realizable traces get a concise OK banner. Unrealizable traces get a
    prominent *** UNREALIZABLE PARTIAL TRACE *** banner with the offending
    trace re-printed so the user can see exactly which env events + measure
    valuations the checker found infeasible.
    """
    tag = f" (trace #{index})" if index is not None else ""
    if verdict.status == "realizable":
        print(f"\n[realizability{tag}] REALIZABLE — the partial trace admits a "
              "bounded extension under which no SLEEC rule is demonstrably "
              "violated before the horizon.")
        return

    # Unrealizable / partially_realizable: show the offending trace clearly.
    N = trace.get("N", "?")
    print("\n" + "!" * 72)
    print(f"!!! UNREALIZABLE PARTIAL TRACE{tag}  (N={N})")
    print("!" * 72)
    print("The SLEEC rules forbid this partial trace — no bounded extension "
          "exists.\n")
    for step in trace["per_step"]:
        t = step["t"]
        events = sorted(step.get("events", ()))
        events_str = ", ".join(events) if events else "(no env event)"
        measure_pairs = []
        for m, v in sorted(step.get("measures", {}).items()):
            if isinstance(v, bool):
                measure_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                measure_pairs.append(f"{m}={v}")
        measures_str = ", ".join(measure_pairs)
        sep = "  | " if measures_str else ""
        print(f"  t={t}: {events_str}{sep}{measures_str}")
    if verdict.culprit_rules:
        print(f"\nRules involved: {', '.join(verdict.culprit_rules)}")
    print("!" * 72)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="SLEEC realizability analysis.")
    parser.add_argument("filename", help="Path to a .sleec file")
    parser.add_argument("--check", action="store_true",
                        help="Run the realizability check pipeline.")
    parser.add_argument("--skip", action="append", default=[],
                        choices=["conflict", "situational"],
                        help="Skip a check step (repeatable).")
    parser.add_argument("--quiet", "-q", action="store_true",
                        help="Suppress progress messages.")
    parser.add_argument("--no-rules", action="store_true", help="Skip rule summary.")
    parser.add_argument("--no-roles", action="store_true", help="Skip event roles.")
    parser.add_argument("--normalize", action="store_true",
                        help="Show the normalized (obligation-form) rules via SleecNorm.")
    parser.add_argument("--sample", type=int, default=None, metavar="N",
                        help="Sample a maximum-triggering partial trace of length N "
                             "over environment events + measures (MaxSMT).")
    parser.add_argument("--k", type=int, default=1, metavar="K",
                        help="With --sample N, request K distinct max-triggering "
                             "traces, blocking each with ALO(~p_trace) between "
                             "calls (default 1).")
    parser.add_argument("--abstract", action="store_true",
                        help="(deprecated, no-op) AbstractTraceSampler is "
                             "now the default; this flag is accepted for "
                             "backward compatibility with existing scripts.")
    parser.add_argument("--legacy-sampler", action="store_true",
                        help="Use the legacy TraceSampler (per-step SSA over "
                             "env events + measures, no per-rule abstraction "
                             "Booleans). Default is AbstractTraceSampler.")
    parser.add_argument("--realizability-check", action="store_true",
                        help="With --sample N, after producing each partial "
                             "trace run the SLEEC bounded realizability check "
                             "(strong by default: uses WhenRule.get_rule() — "
                             "every triggered obligation must be actually "
                             "satisfied). Use --weak for bounded-weak semantics "
                             "(uses SleecNorm.encode_limited).")
    parser.add_argument("--weak", action="store_true",
                        help="Use bounded-weak semantics for --realizability-check "
                             "(default is strong). Obligations whose deadlines "
                             "are past the horizon are vacuously not-violated.")
    parser.add_argument("--decompose", action="store_true",
                        help="Decompose the rule set into dependency-graph "
                             "components and check each independently. By the "
                             "Decomposition Theorem, if every component is "
                             "realizable on the seed then so is the whole spec. "
                             "Off by default.")
    args = parser.parse_args(argv)

    if not os.path.isfile(args.filename):
        print(f"error: file not found: {args.filename}", file=sys.stderr)
        return 2

    # Reuse the parser already in sleecParser.py.
    model, rules, concerns, purposes, relations, action_mapping, actions = parse_sleec(
        args.filename, read_file=True
    )

    print_declarations(model, source_path=args.filename)
    if not args.no_rules:
        print_rules(model)
    if not args.no_roles:
        print_event_roles(model)

    if args.normalize:
        print_normalized_rules(read_model_file(args.filename))

    if args.sample is not None:
        if args.sample < 1:
            print("error: --sample N must be >= 1", file=sys.stderr)
            return 2
        if args.k < 1:
            print("error: --k K must be >= 1", file=sys.stderr)
            return 2
        sampler_cls = TraceSampler if args.legacy_sampler else AbstractTraceSampler
        try:
            sampler = sampler_cls(model, args.sample, verbose=not args.quiet)
        except Exception as exc:
            # Surface event-classification conflicts cleanly without a traceback.
            if type(exc).__name__ == "EventClassificationError":
                from sleec_event_classification import format_conflicts
                print("\nrealizability run aborted: event classification "
                      "produced conflicts.\n", file=sys.stderr)
                print(format_conflicts(exc.classification), file=sys.stderr)
                return 2
            raise

        # If the user asked for a realizability check, construct the checker
        # once (it parses via SleecNorm, which is slow; don't redo per trace).
        rz_checker = None
        if args.realizability_check:
            rz_checker = RealizabilityChecker(
                model, N=args.sample,
                model_str=read_model_file(args.filename),
                mode="weak" if args.weak else "strong",
                decompose=args.decompose,
            )

        any_unrealizable = False
        for i in range(1, args.k + 1):
            trace = sampler.next_trace()
            if trace is None:
                print(f"\n[sampler] (exhausted after {i-1} trace(s) — no more "
                      "max-triggering traces consistent with ALO blocking)")
                break
            print_sampled_trace(trace, index=i if args.k > 1 else None)
            if rz_checker is not None:
                try:
                    verdict = rz_checker.check(trace, verbose=not args.quiet)
                except Exception as exc:
                    if type(exc).__name__ == "RelationClassificationError":
                        print("\nrealizability run aborted: unsupported "
                              "relation kind.\n", file=sys.stderr)
                        print(str(exc), file=sys.stderr)
                        return 2
                    raise
                print_realizability_result(trace, verdict,
                                            index=i if args.k > 1 else None)
                if verdict.status != "realizable":
                    any_unrealizable = True
            if i < args.k:
                if not sampler.block(trace):
                    saturation_msg = (
                        "trace triggered every env event at every step"
                        if args.legacy_sampler
                        else "every (rule, step) firing is already saturated"
                    )
                    print(f"\n[sampler] (trace #{i}: {saturation_msg}; "
                          "complement is empty, exhausting here)")
                    break

        # Exit with non-zero if we found any unrealizable trace, useful for CI.
        if any_unrealizable:
            return 1

    if args.check:
        model_str = read_model_file(args.filename)
        overall, outcomes = run_realizability_report(
            model_str, skip=set(args.skip), verbose=not args.quiet
        )
        print_report(outcomes, overall)
        return 0 if overall else 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
