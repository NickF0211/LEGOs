"""
sleec_proof_witness.py — extract a minimum unrealizability witness from
the FOL* unsat proof produced by LEGOS+, using the SAME structured
machinery as ``check_situational_conflict`` (SleecNorm.py).

Design (mirrors situational-conflict diagnosis; NO regex on proof text):

  1. The realizability query is built so that each SLEEC rule encoding
     is passed as a separate element of ``complete_rules`` to
     ``check_property_refining(..., record_proof=True)``. LEGOS+ then
     assigns each input axiom a stable integer ``id`` (the ``property``
     gets id 0; ``complete_rules[k]`` gets id ``k+1``).

  2. On UNSAT, ``proof_reader.check_and_minimize("proof.txt",
     "simplified.txt")`` returns ``(UNSAT_CORE, derivation)`` where
     ``UNSAT_CORE`` is a set of ``InputRule`` objects each carrying
     ``.id``. We map those ids back to source SLEEC rules through a
     caller-supplied ``id_to_source`` table — exactly the index
     arithmetic ``check_situational_conflict`` performs with
     ``model.ruleBlock.rules[id-1]``.

  3. The essential environment behaviour (which env events / measure
     values matter) is derived STRUCTURALLY by walking the culprit
     rules' own trigger + condition textX ASTs and projecting the
     sampled trace onto the referenced symbols. No proof-text parsing.

  4. The clashing head event(s) are the rule heads that appear with
     BOTH polarities across the culprit rules — a structural property
     of the rule ASTs.

The result is a :class:`Witness` naming the minimal rules + relations,
the minimal env-event/measure trace, and the clashing head event(s).
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class Witness:
    """Structured minimum unrealizability witness."""
    rules: List[str] = field(default_factory=list)
    relations: List[str] = field(default_factory=list)
    env_events: Dict[int, List[str]] = field(default_factory=dict)
    measures: Dict[int, Dict[str, object]] = field(default_factory=dict)
    conflict_events: List[str] = field(default_factory=list)
    # Absolute (start, end) source spans the MINIMIZED proof referenced
    # (from proof_reader.get_high_light over the derivation). These are
    # the exact atoms — events, measures, deadlines — used to derive the
    # contradiction, suitable for precise source highlighting.
    highlights: List[Tuple[int, int]] = field(default_factory=list)

    def is_empty(self) -> bool:
        return not (self.rules or self.relations
                    or self.env_events or self.measures)


# =============================================================================
# 1. Symbol tables (from the textX model — authoritative, not guessed)
# =============================================================================

def event_kinds(model) -> Dict[str, str]:
    """Map each declared event name to its kind: ``"system"``,
    ``"environment"``, or ``""`` (unannotated)."""
    out: Dict[str, str] = {}
    for d in getattr(model, "definitions", []) or []:
        if type(d).__name__ == "Event":
            out[d.name] = (getattr(d, "kind", None) or "")
    return out


def measure_names(model) -> Set[str]:
    """Set of all declared measure names (bool + scalar + numeric)."""
    out: Set[str] = set()
    for d in getattr(model, "definitions", []) or []:
        if type(d).__name__ in ("BoolMeasure", "ScalarMeasure", "NumericMeasure"):
            nm = getattr(d, "name", None)
            if nm:
                out.add(nm)
    return out


def all_event_names(model) -> Set[str]:
    """Set of all declared event names."""
    return {d.name for d in getattr(model, "definitions", []) or []
            if type(d).__name__ == "Event"}


def _response_head_event_names(model) -> Set[str]:
    """Events that appear as a rule response head (system-controllable):
    the system can be forced to produce them, so they are NOT environment
    events even when unannotated."""
    heads: Set[str] = set()
    for r in getattr(model.ruleBlock, "rules", []) or []:
        def visit(n):
            if type(n).__name__ == "Occ":
                h = _occ_head(n)
                if h is not None:
                    heads.add(h[0])
        _walk_textx(getattr(r, "response", None), visit)
    return heads


def environment_event_names(model, trace=None) -> Set[str]:
    """Authoritative set of environment-controlled event names.

    SLEEC specs frequently leave events UNANNOTATED; the checker then
    classifies an event as environment iff it is never produced as a
    rule response head (only the environment can make it happen). We
    therefore resolve the env set as, in order of preference:

      1. ``trace["environment_events"]`` — the exact set the sampler
         used to build this trace (most authoritative);
      2. structural fallback — all declared events minus response heads;
    then always UNION any explicitly ``as environment`` annotated events.
    """
    annotated_env = {n for n, k in event_kinds(model).items()
                     if k == "environment"}
    if trace is not None:
        env = trace.get("environment_events")
        if env:
            return set(env) | annotated_env
    # Structural fallback: never-a-response-head events are environment.
    structural = all_event_names(model) - _response_head_event_names(model)
    return structural | annotated_env


# =============================================================================
# 2. Structured UNSAT-core -> culprit rules/relations
# =============================================================================

def map_unsat_core(
    unsat_core,
    id_to_source: Dict[int, Tuple[str, str]],
) -> Tuple[List[str], List[str]]:
    """Map a structured ``UNSAT_CORE`` (iterable of objects with ``.id``)
    to source rule and relation names via ``id_to_source``.

    ``id_to_source`` maps a proof input id to a ``(kind, name)`` pair,
    where ``kind`` is ``"rule"`` or ``"relation"``. Ids absent from the
    table (e.g.\\ id 0, the bundled trace/structural property) are
    ignored.

    Returns ``(rule_names_sorted, relation_names_sorted)`` with
    duplicates removed and rule order preserving spec order when the
    caller's table is spec-ordered.
    """
    rules: List[str] = []
    relations: List[str] = []
    seen_r: Set[str] = set()
    seen_rel: Set[str] = set()
    for item in unsat_core:
        rid = getattr(item, "id", None)
        if rid is None:
            continue
        src = id_to_source.get(rid)
        if src is None:
            continue
        kind, name = src
        if kind == "rule" and name not in seen_r:
            seen_r.add(name)
            rules.append(name)
        elif kind == "relation" and name not in seen_rel:
            seen_rel.add(name)
            relations.append(name)
    return rules, relations


def sort_rule_names(names: List[str], spec_order: List[str]) -> List[str]:
    """Sort ``names`` by their position in ``spec_order`` (spec order),
    appending any unknown names alphabetically at the end."""
    idx = {n: i for i, n in enumerate(spec_order)}
    known = sorted((n for n in names if n in idx), key=lambda n: idx[n])
    unknown = sorted(n for n in names if n not in idx)
    return known + unknown


# =============================================================================
# 3. Structured AST walks over culprit rules
# =============================================================================

def _is_textx(node) -> bool:
    mod = getattr(node, "__module__", "") or ""
    return mod.startswith("textx") or "sleec" in mod.lower()


def _walk_textx(node, visit):
    """Generic depth-first walk over a textX AST subtree, calling
    ``visit(node)`` on every textX node. Avoids ``parent`` back-edges
    and primitive leaves. Cycle-safe via an id-visited set."""
    seen: Set[int] = set()

    def rec(n):
        if n is None or isinstance(n, (str, int, float, bool, bytes)):
            return
        if not _is_textx(n):
            return
        if id(n) in seen:
            return
        seen.add(id(n))
        visit(n)
        for attr in dir(n):
            if attr.startswith("_") or attr == "parent":
                continue
            try:
                v = getattr(n, attr)
            except Exception:
                continue
            if v is None or isinstance(v, (str, int, float, bool, bytes)):
                continue
            if isinstance(v, list):
                for it in v:
                    rec(it)
            else:
                rec(v)

    rec(node)


def refs_in_trigger_condition(
    rule_node,
    env_names: Set[str],
    all_measure_names: Set[str],
) -> Tuple[Set[str], Set[str]]:
    """Walk a rule's trigger + condition ASTs and collect:

      - ``events``  : event names referenced that are environment events
      - ``measures``: measure names referenced

    Matching is against the model's symbol tables (``env_names``,
    ``all_measure_names``) — a node's ``.name`` is classified only if it
    appears in those declared sets, so we never mis-tag arbitrary
    identifiers.
    """
    events: Set[str] = set()
    measures: Set[str] = set()

    # Trigger event (the rule's primary triggering event).
    trig = getattr(rule_node, "trigger", None)
    trig_ev = getattr(trig, "event", None) if trig is not None else None
    trig_name = getattr(trig_ev, "name", None)
    if isinstance(trig_name, str) and trig_name in env_names:
        events.add(trig_name)

    def visit(n):
        nm = getattr(n, "name", None)
        if isinstance(nm, str):
            if nm in all_measure_names:
                measures.add(nm)
            elif nm in env_names:
                events.add(nm)

    # Walk trigger (for any extra event refs) and condition (measures).
    _walk_textx(getattr(rule_node, "trigger", None), visit)
    _walk_textx(getattr(rule_node, "condition", None), visit)
    # Walk defeater / alternative ('unless ...') guards too: a defeater's
    # guard measures are ESSENTIAL to the conflict — the conflict requires
    # the defeater NOT to fire, which pins those measure values. Response
    # heads inside the defeater are system events, so env_names filtering
    # keeps them out of the env-event set.
    resp = getattr(rule_node, "response", None)
    if resp is not None:
        for d in getattr(resp, "defeater", []) or []:
            _walk_textx(d, visit)
        _walk_textx(getattr(resp, "alternative", None), visit)
    return events, measures


def _occ_head(occ) -> Optional[Tuple[str, bool]]:
    """From an ``Occ`` node, return ``(head_event_name, is_negated)``."""
    if occ is None:
        return None
    trig = getattr(occ, "event", None)
    ev = getattr(trig, "event", None) if trig is not None else None
    nm = getattr(ev, "name", None)
    if not isinstance(nm, str):
        return None
    return (nm, bool(getattr(occ, "neg", False)))


def conflict_heads(rule_nodes) -> List[str]:
    """Return head event names that appear with BOTH positive and
    negative polarity across the given rule ASTs (the clash sites).

    Walks each rule's full response subtree (primary response,
    otherwise/unless branches, defeaters) collecting ``Occ`` heads with
    their polarity.
    """
    pos: Set[str] = set()
    neg: Set[str] = set()

    for rn in rule_nodes:
        def visit(n, _pos=pos, _neg=neg):
            if type(n).__name__ != "Occ":
                return
            h = _occ_head(n)
            if h is None:
                return
            name, is_neg = h
            (_neg if is_neg else _pos).add(name)
        # Walk response + defeaters.
        _walk_textx(getattr(rn, "response", None), visit)
        for d in getattr(rn, "defeaters", []) or []:
            _walk_textx(d, visit)
    return sorted(pos & neg)


# =============================================================================
# 4. Env witness: project the sampled trace onto culprit-rule symbols
# =============================================================================

def build_env_witness(
    culprit_rule_nodes,
    trace,
    env_names: Set[str],
    all_measure_names: Set[str],
    culprit_rule_names: List[str],
) -> Tuple[Dict[int, List[str]], Dict[int, Dict[str, object]]]:
    """Build the minimal env-event / measure witness.

    Essential symbols are exactly those referenced in the culprit
    rules' triggers + conditions. We then project the sampled trace
    onto:

      - the time steps where a culprit rule fires (``trace["rules_fired"]``),
      - the essential env events present at those steps,
      - the essential measure values at those steps.

    Returns ``(env_events_by_time, measures_by_time)``.
    """
    # 1. Collect essential symbols from culprit rule ASTs.
    ess_events: Set[str] = set()
    ess_measures: Set[str] = set()
    for rn in culprit_rule_nodes:
        ev, ms = refs_in_trigger_condition(rn, env_names, all_measure_names)
        ess_events |= ev
        ess_measures |= ms

    # 2. Determine the essential time steps: steps where a culprit rule
    #    fired. Fall back to all steps if rules_fired is unavailable.
    culprit_set = set(culprit_rule_names)
    fired = trace.get("rules_fired") or []
    steps = sorted({t for (rname, t) in fired if rname in culprit_set})
    if not steps:
        steps = sorted(s.get("t") for s in trace.get("per_step", []))

    # 3. Project the trace onto essential symbols at those steps.
    per_step = {s.get("t"): s for s in trace.get("per_step", [])}
    env_by_time: Dict[int, List[str]] = {}
    meas_by_time: Dict[int, Dict[str, object]] = {}
    for t in steps:
        step = per_step.get(t)
        if step is None:
            continue
        present = set(step.get("events", []))
        ev_here = sorted(e for e in ess_events if e in present)
        if ev_here:
            env_by_time[t] = ev_here
        msnap = step.get("measures", {}) or {}
        vals = {m: msnap[m] for m in ess_measures if m in msnap}
        if vals:
            meas_by_time[t] = vals
    return env_by_time, meas_by_time


# =============================================================================
# 5. Top-level assembly
# =============================================================================

def build_witness(
    model,
    unsat_core,
    id_to_source: Dict[int, Tuple[str, str]],
    trace,
    highlights: Optional[List[Tuple[int, int]]] = None,
) -> Witness:
    """Assemble a :class:`Witness` from a structured UNSAT core.

    Parameters
    ----------
    model : textX Specification
        The parsed SLEEC model (provides symbol tables + rule ASTs).
    unsat_core : iterable
        Structured UNSAT core from ``check_and_minimize`` — objects with
        ``.id``.
    id_to_source : dict[int, (kind, name)]
        Maps proof input ids to ``("rule", name)`` / ``("relation", name)``.
    trace : dict
        The sampled trace (``per_step``, ``rules_fired``).
    highlights : list[(start, end)], optional
        Absolute source spans the minimized proof referenced
        (``get_high_light(derivation)``). Stored on the witness for
        precise, proof-driven source highlighting.
    """
    spec_order = [r.name for r in model.ruleBlock.rules]
    rule_by_name = {r.name: r for r in model.ruleBlock.rules}

    rules, relations = map_unsat_core(unsat_core, id_to_source)
    rules = sort_rule_names(rules, spec_order)

    culprit_nodes = [rule_by_name[n] for n in rules if n in rule_by_name]
    # Authoritative env-event set: prefer the sampler's classification
    # (handles unannotated specs where env events are inferred as
    # never-a-response-head), unioned with annotated env events.
    env_names = environment_event_names(model, trace)
    m_names = measure_names(model)

    env_events, measures = build_env_witness(
        culprit_nodes, trace, env_names, m_names, rules
    )
    heads = conflict_heads(culprit_nodes)

    return Witness(
        rules=rules,
        relations=relations,
        env_events=env_events,
        measures=measures,
        conflict_events=heads,
        highlights=sorted(set(highlights or [])),
    )
