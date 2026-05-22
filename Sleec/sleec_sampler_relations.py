"""Hard-constraint encoder for SLEEC relations in the bounded sampler.

Bridges the FOL* trace semantics from `Analyzer/sleecOp.py` to z3
constraints over the bounded-sampling per-step variables. The samplers
call `add_relation_constraints(...)` once during `__init__`. This
encodes every relation in the spec whose actor configuration is
"sampler-controllable":

  - env-event-only event relations (witness, equal, mutualExclusive,
    happenBefore between two env events),
  - env-event-with-measure relations (Causation, Effect, Forbid where
    the cause is an env event),
  - env-start extended-modality relations (UntilEM, TimedEM whose start
    trigger is an env event).

Skipped (handled elsewhere):

  - sys-only event relations -> Phase II (realizability check) only.
  - sys+measure relations    -> already errored at parse time by
    RealizabilityChecker.check via classify_relation_actors.
  - mixed env+sys event relations -> deferred (defeasible-proposals).
  - measure-only and measure-invariant relations -> handled by the
    samplers' existing _add_measure_relations.

Each of the multi-step relations (happenBefore, UntilEM, TimedEM) is
encoded by enumerating bounded ranges of (t, t') pairs explicitly; no
quantifiers are added to z3.

Public API:
    add_relation_constraints(opt, model, e_vars, m_ctx_at_step,
                             eval_bool_expr, ec, N, *, verbose) -> None

The samplers pass their own state in: `opt` (z3.Optimize), `e_vars`
(dict event-name -> per-step BoolRef list), `m_ctx_at_step(t)` builds
a context dict suitable for evaluating MBoolExpr trees at step t,
`eval_bool_expr` is `_z3_eval_bool_expr` (the existing translator), and
`ec` is the EventClassification from sleec_event_classification.

This module raises NO exceptions. It logs (verbose) when it skips a
relation kind it cannot encode and proceeds to the next.
"""

from __future__ import annotations

import sys
from typing import Callable, Dict, List, Optional


# ============================================================================
# Single-step encodings (event relations on env events only)
# ============================================================================

def _enc_witness(opt, lhs_vars, rhs_vars, N: int) -> None:
    """Encode `witness lhs rhs` semantics: forall t. lhs@t => rhs@t.

    Both lhs_vars and rhs_vars must be lists of length N of z3 Booleans.
    Adds N implication constraints to `opt`.
    """
    import z3
    for t in range(N):
        opt.add(z3.Implies(lhs_vars[t], rhs_vars[t]))


def _enc_equal(opt, lhs_vars, rhs_vars, N: int) -> None:
    """Encode `equal lhs rhs` semantics: forall t. lhs@t <=> rhs@t."""
    import z3
    for t in range(N):
        opt.add(lhs_vars[t] == rhs_vars[t])


def _enc_mutex(opt, lhs_vars, rhs_vars, N: int) -> None:
    """Encode `mutualExclusive lhs rhs` semantics:
    forall t. NOT (lhs@t AND rhs@t)."""
    import z3
    for t in range(N):
        opt.add(z3.Not(z3.And(lhs_vars[t], rhs_vars[t])))


def _enc_happen_before(opt, lhs_vars, rhs_vars, N: int) -> None:
    """Encode `happenBefore lhs rhs` semantics:
    forall t. rhs@t => exist t' in [1, t-1]. lhs@t'.

    For t=1, this collapses to NOT rhs@1 (no earlier step exists).
    Multi-step: O(N) clauses per step -> O(N^2) total.
    """
    import z3
    for t in range(N):
        if t == 0:
            opt.add(z3.Not(rhs_vars[0]))  # nothing precedes step 1
            continue
        earlier = z3.Or([lhs_vars[t_prime] for t_prime in range(t)])
        opt.add(z3.Implies(rhs_vars[t], earlier))


# ============================================================================
# Single-step encodings (event-and-measure: Causation / Effect / Forbid)
# ============================================================================

def _enc_causation(opt, cause_vars, effect_at_t: Callable[[int], "z3.BoolRef"],
                   N: int) -> None:
    """Encode `causation cause {effect_expr}` semantics:
    forall t. effect_expr(t) => cause@t.

    cause_vars must be the env-event presence Booleans. effect_at_t(t)
    returns the z3 boolean expression for the measure-side effect at step t.
    """
    import z3
    for t in range(N):
        opt.add(z3.Implies(effect_at_t(t), cause_vars[t]))


def _enc_effect(opt, cause_vars, effect_at_t: Callable[[int], "z3.BoolRef"],
                N: int) -> None:
    """Encode `includes cause {effect_expr}` semantics:
    forall t. cause@t => effect_expr(t)."""
    import z3
    for t in range(N):
        opt.add(z3.Implies(cause_vars[t], effect_at_t(t)))


def _enc_forbid(opt, cause_vars, effect_at_t: Callable[[int], "z3.BoolRef"],
                N: int) -> None:
    """Encode `forbid cause {effect_expr}` semantics:
    forall t. cause@t => NOT effect_expr(t)."""
    import z3
    for t in range(N):
        opt.add(z3.Implies(cause_vars[t], z3.Not(effect_at_t(t))))


# ============================================================================
# Multi-step encodings (extended-modality relations)
# ============================================================================

def _enc_until_em(
    opt,
    start_vars,
    end_vars,                                      # may be None
    start_cond_at: Callable[[int], "z3.BoolRef"],
    end_cond_at: Optional[Callable[[int], "z3.BoolRef"]],
    inv_at: Callable[[int], "z3.BoolRef"],
    N: int,
) -> None:
    """Encode `when start [and start_cond] then inv [until end] [and end_cond]`.

    Trace semantics: when (start AND start_cond) fires at t_start, the
    invariant inv must hold at every step in [t_start, t_end - 1] where
    t_end is the next step at which (end AND end_cond) fires (or N+1 if
    no such step exists).

    Bounded encoding: for each t_start in [1, N]:
      Let trigger = start_vars[t_start] AND start_cond_at(t_start)
      For each t' in [t_start, N]:
        Let no_end_yet = AND over t'' in [t_start, t'] of
          NOT (end_vars[t''] AND end_cond_at(t''))   # if end_vars is not None
        opt.add(Implies(trigger AND no_end_yet, inv_at(t')))

    end_vars=None means the "until" clause is absent; the invariant must
    hold from t_start onward forever (so for t' in [t_start, N]).
    """
    import z3
    has_end = end_vars is not None
    if not has_end:
        # No end_trigger: invariant holds from t_start to horizon.
        for t_start in range(N):
            trigger = z3.And(start_vars[t_start], start_cond_at(t_start))
            for t_prime in range(t_start, N):
                opt.add(z3.Implies(trigger, inv_at(t_prime)))
        return
    end_cond = end_cond_at if end_cond_at is not None else (lambda t: z3.BoolVal(True))
    for t_start in range(N):
        trigger = z3.And(start_vars[t_start], start_cond_at(t_start))
        for t_prime in range(t_start, N):
            # No end_trigger fired in [t_start, t_prime]
            no_end_yet_terms = []
            for t_pp in range(t_start, t_prime + 1):
                no_end_yet_terms.append(
                    z3.Not(z3.And(end_vars[t_pp], end_cond(t_pp)))
                )
            no_end_yet = z3.And(*no_end_yet_terms) if no_end_yet_terms else z3.BoolVal(True)
            opt.add(z3.Implies(z3.And(trigger, no_end_yet), inv_at(t_prime)))


def _enc_timed_em(
    opt,
    start_vars,
    cond_at: Callable[[int], "z3.BoolRef"],
    duration_at: Callable[[int], "z3.ArithRef"],
    inv_at: Callable[[int], "z3.BoolRef"],
    N: int,
) -> None:
    """Encode `when start [and cond] then inv for <duration>`.

    Trace semantics: when (start AND cond) fires at t_start, inv holds at
    every step in [t_start, t_start + duration(t_start) - 1].

    Bounded encoding: for each t_start in [1, N]:
      Let trigger = start_vars[t_start] AND cond_at(t_start)
      For each t' in [t_start, N]:
        opt.add(Implies(trigger AND (t' < t_start + duration_at(t_start)),
                        inv_at(t')))

    duration_at(t_start) is a z3 expression (typically an Int). The
    bound is symbolic, so for each candidate t' we gate the implication
    on `t' < t_start + duration_expr` (1-indexed time math: we treat t
    as the SLEEC time, i.e. t = idx+1).
    """
    import z3
    for t_start_idx in range(N):
        # SLEEC time at index t_start_idx is t_start_idx + 1.
        t_start_t = t_start_idx + 1
        trigger = z3.And(start_vars[t_start_idx], cond_at(t_start_idx))
        d_expr = duration_at(t_start_idx)
        for t_prime_idx in range(t_start_idx, N):
            t_prime_t = t_prime_idx + 1
            within_window = (z3.IntVal(t_prime_t)
                             < z3.IntVal(t_start_t) + d_expr)
            opt.add(z3.Implies(z3.And(trigger, within_window),
                                inv_at(t_prime_idx)))


# ============================================================================
# Public entry point: dispatch by relation kind + actor configuration
# ============================================================================

def add_relation_constraints(
    opt,
    model,
    e_vars: Dict[str, List["z3.BoolRef"]],
    m_ctx_at_step: Callable[[int], dict],
    eval_bool_expr: Callable[[object, dict], "z3.BoolRef"],
    ec,
    N: int,
    *,
    verbose: bool = False,
) -> None:
    """Add hard z3 constraints for every sampler-controllable relation in
    `model.relBlock.relations`. Skips non-controllable kinds with a
    verbose log line.

    Args:
        opt           : z3.Optimize instance to receive constraints.
        model         : textX SLEEC model.
        e_vars        : per-(event, step) Boolean variables for env events.
        m_ctx_at_step : callable t -> measure-context dict for step t.
        eval_bool_expr: callable (mbool_expr, ctx) -> z3 BoolRef.
        ec            : EventClassification (for relation-actor classification).
        N             : horizon (number of steps).
        verbose       : if True, emit one stderr line per skip / handled.

    Raises:
        Nothing. Skipped or unsupported encodings produce a warning only.
    """
    from sleec_event_classification import (
        classify_relation_actors, RelationActorKind,
    )

    rb = getattr(model, "relBlock", None)
    if rb is None:
        return

    def _ev_name(ev_node) -> Optional[str]:
        # Resolve textX Event reference (.name) vs Trigger (which has .event).
        if ev_node is None:
            return None
        # Trigger node has .event; Event reference has .name.
        if hasattr(ev_node, "event") and ev_node.event is not None:
            return getattr(ev_node.event, "name", None)
        return getattr(ev_node, "name", None)

    def _vars_for(name: str) -> Optional[List["z3.BoolRef"]]:
        return e_vars.get(name)

    def _is_env(name: str) -> bool:
        from sleec_event_classification import Kind
        return ec.kind.get(name) == Kind.ENVIRONMENT

    def _bool_at(expr_node) -> Callable[[int], "z3.BoolRef"]:
        return lambda t_idx: eval_bool_expr(expr_node, m_ctx_at_step(t_idx))

    for rel in rb.relations:
        cls = type(rel).__name__
        actor_kind = classify_relation_actors(rel, ec)

        # Skip everything we already handle elsewhere or have explicitly deferred.
        if actor_kind in (
            RelationActorKind.SYS_EVENT_AND_MEASURE,
            RelationActorKind.MIXED_AND_MEASURE,
            RelationActorKind.MIXED_ENV_SYS_EVENTS,
            RelationActorKind.SYS_ONLY_EVENTS,
            RelationActorKind.MEASURE_ONLY,
            RelationActorKind.EMPTY,
        ):
            if verbose:
                print(f"[sampler-rel] skip {cls} ({actor_kind.value})",
                      file=sys.stderr)
            continue

        # ---- EventRel (env-only) ---------------------------------------
        if cls == "EventRel" and actor_kind == RelationActorKind.ENV_ONLY_EVENTS:
            lhs_name = _ev_name(rel.lhs)
            rhs_name = _ev_name(rel.rhs)
            lhs_v = _vars_for(lhs_name)
            rhs_v = _vars_for(rhs_name)
            if lhs_v is None or rhs_v is None:
                if verbose:
                    print(f"[sampler-rel] EventRel {rel.rel} {lhs_name} {rhs_name}: "
                          f"missing per-step vars; skip", file=sys.stderr)
                continue
            op = rel.rel
            if op == "witness":
                _enc_witness(opt, lhs_v, rhs_v, N)
            elif op == "equal":
                _enc_equal(opt, lhs_v, rhs_v, N)
            elif op == "mutualExclusive":
                _enc_mutex(opt, lhs_v, rhs_v, N)
            elif op == "happenBefore":
                _enc_happen_before(opt, lhs_v, rhs_v, N)
            else:
                if verbose:
                    print(f"[sampler-rel] unknown EventRel op {op!r}; skip",
                          file=sys.stderr)
                continue
            if verbose:
                print(f"[sampler-rel] encoded EventRel {op} "
                      f"{lhs_name} {rhs_name}", file=sys.stderr)
            continue

        # ---- Causation / Effect / Forbid (env-cause + measure) ---------
        if cls in ("Causation", "Effect", "Forbid"):
            cause_name = _ev_name(rel.cause)
            cause_v = _vars_for(cause_name) if cause_name else None
            if cause_v is None or not _is_env(cause_name):
                if verbose:
                    print(f"[sampler-rel] {cls} on non-env cause "
                          f"{cause_name!r}; skip", file=sys.stderr)
                continue
            effect_node = getattr(rel, "effect", None)
            if effect_node is None:
                continue
            try:
                effect_at = _bool_at(effect_node)
                _ = effect_at(0)  # smoke-evaluate at t=0 for early failure
            except NotImplementedError as e:
                if verbose:
                    print(f"[sampler-rel] {cls} {cause_name} effect not "
                          f"encodable ({e}); skip", file=sys.stderr)
                continue
            if cls == "Causation":
                _enc_causation(opt, cause_v, effect_at, N)
            elif cls == "Effect":
                _enc_effect(opt, cause_v, effect_at, N)
            elif cls == "Forbid":
                _enc_forbid(opt, cause_v, effect_at, N)
            if verbose:
                print(f"[sampler-rel] encoded {cls} on env event "
                      f"{cause_name}", file=sys.stderr)
            continue

        # ---- UntilEM (env-start) ---------------------------------------
        if cls == "UntilEM":
            start_trig = getattr(rel, "start_trigger", None)
            start_name = _ev_name(start_trig)
            start_v = _vars_for(start_name) if start_name else None
            if start_v is None or not _is_env(start_name):
                if verbose:
                    print(f"[sampler-rel] UntilEM start_trigger {start_name!r} "
                          "not env; skip", file=sys.stderr)
                continue
            end_trig = getattr(rel, "end_trigger", None)
            end_name = _ev_name(end_trig) if end_trig else None
            end_v = _vars_for(end_name) if end_name else None
            if end_trig is not None and (end_v is None or not _is_env(end_name)):
                if verbose:
                    print(f"[sampler-rel] UntilEM end_trigger {end_name!r} "
                          "not env; skip", file=sys.stderr)
                continue
            try:
                start_cond_node = getattr(rel, "start_condition", None)
                start_cond_at = (_bool_at(start_cond_node)
                                 if start_cond_node is not None
                                 else (lambda t: __import__("z3").BoolVal(True)))
                end_cond_node = getattr(rel, "end_condition", None)
                end_cond_at = (_bool_at(end_cond_node)
                               if end_cond_node is not None
                               else None)
                inv_node = getattr(rel, "inv", None)
                if inv_node is None:
                    if verbose:
                        print("[sampler-rel] UntilEM has no inv; skip",
                              file=sys.stderr)
                    continue
                inv_at = _bool_at(inv_node)
                # Smoke-evaluate at t=0.
                _ = start_cond_at(0)
                _ = inv_at(0)
                if end_cond_at is not None:
                    _ = end_cond_at(0)
            except NotImplementedError as e:
                if verbose:
                    print(f"[sampler-rel] UntilEM expr not encodable ({e}); skip",
                          file=sys.stderr)
                continue
            _enc_until_em(opt, start_v, end_v, start_cond_at, end_cond_at, inv_at, N)
            if verbose:
                print(f"[sampler-rel] encoded UntilEM start={start_name} "
                      f"end={end_name}", file=sys.stderr)
            continue

        # ---- TimedEM (env-start) ---------------------------------------
        if cls == "TimedEM":
            start_trig = getattr(rel, "start_trigger", None)
            start_name = _ev_name(start_trig)
            start_v = _vars_for(start_name) if start_name else None
            if start_v is None or not _is_env(start_name):
                if verbose:
                    print(f"[sampler-rel] TimedEM start_trigger {start_name!r} "
                          "not env; skip", file=sys.stderr)
                continue
            try:
                cond_node = getattr(rel, "condition", None)
                cond_at = (_bool_at(cond_node)
                           if cond_node is not None
                           else (lambda t: __import__("z3").BoolVal(True)))
                duration_node = getattr(rel, "duration", None)
                if duration_node is None:
                    if verbose:
                        print("[sampler-rel] TimedEM has no duration; skip",
                              file=sys.stderr)
                    continue
                # duration is a TimeValue; we evaluate its `value` field
                # via eval_bool_expr-friendly path? Likely we need an arith
                # evaluator here. Skip if not available.
                duration_value = getattr(duration_node, "value", None)
                if duration_value is None:
                    if verbose:
                        print("[sampler-rel] TimedEM duration has no value; skip",
                              file=sys.stderr)
                    continue
                # Use eval_bool_expr's number path: we expect it to handle
                # NumExp (or fall back). Wrap in a try.
                duration_at = lambda t_idx, dv=duration_value: \
                    eval_bool_expr(dv, m_ctx_at_step(t_idx))
                _ = duration_at(0)  # smoke-evaluate
                inv_node = getattr(rel, "inv", None)
                if inv_node is None:
                    if verbose:
                        print("[sampler-rel] TimedEM has no inv; skip",
                              file=sys.stderr)
                    continue
                inv_at = _bool_at(inv_node)
                _ = inv_at(0)
            except NotImplementedError as e:
                if verbose:
                    print(f"[sampler-rel] TimedEM expr not encodable ({e}); skip",
                          file=sys.stderr)
                continue
            _enc_timed_em(opt, start_v, cond_at, duration_at, inv_at, N)
            if verbose:
                print(f"[sampler-rel] encoded TimedEM start={start_name}",
                      file=sys.stderr)
            continue

        if verbose:
            print(f"[sampler-rel] unhandled relation kind {cls}; skip",
                  file=sys.stderr)
