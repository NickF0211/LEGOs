"""Rule-dependency-graph decomposition for SLEEC realizability.

Implements the decomposition described in the project notes:
  Partition normalized rules into components under the transitive
  closure of the following relations:
    (a) head-share    : same response event class (ignoring polarity)
    (b) cascade       : one rule's head is another's trigger
    (c) measure-coupl : share at least one measure read in condition/defeater
    (d) relational    : both appear in the alphabet of the same relational
                        constraint

Theorem (Decomposition): R is strongly bounded-realizable on (pi_env, t)
iff every component is realizable on (pi_env, t).  The same holds under
the weak encoding.

Usage:
  components = decompose_rules(normalized_rules, og_rules, relations)
  -> list[list[int]]  (each inner list is a list of indices into rules)
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, List, Optional, Sequence, Set, Tuple


# ------------------------------- Union-Find -------------------------------

class _UF:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))
        self.rank = [0] * n

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, x: int, y: int) -> None:
        rx, ry = self.find(x), self.find(y)
        if rx == ry:
            return
        if self.rank[rx] < self.rank[ry]:
            rx, ry = ry, rx
        self.parent[ry] = rx
        if self.rank[rx] == self.rank[ry]:
            self.rank[rx] += 1


# ------------------------------ AST walking ------------------------------

def _walk_textx(node) -> Iterable:
    """Yield every sub-node of a textX AST object."""
    if node is None:
        return
    yield node
    for attr in dir(node):
        if attr.startswith('_') or attr == 'parent':
            continue
        try:
            v = getattr(node, attr)
        except Exception:
            continue
        if isinstance(v, (str, bytes, int, float, bool)):
            continue
        if isinstance(v, list):
            for item in v:
                yield from _walk_textx(item)
        elif hasattr(v, '__module__') and getattr(v, '__module__', '').startswith('textx'):
            yield from _walk_textx(v)


def _measure_reads(ast_node) -> Set[str]:
    """Return the set of measure names referenced anywhere under `ast_node`."""
    names: Set[str] = set()
    if ast_node is None:
        return names
    for sub in _walk_textx(ast_node):
        cls = type(sub).__name__
        # BoolTerminal / NumTerminal carry `.ID` which is a Measure object
        # with `.name`.
        if cls in ('BoolTerminal', 'NumTerminal', 'ScalarTerminal'):
            m = getattr(sub, 'ID', None)
            if m is not None:
                nm = getattr(m, 'name', None)
                if nm:
                    names.add(nm)
    return names


# ------------------------------ Rule keys --------------------------------

def _event_key(ev) -> str:
    """Canonical string key for an event class (ignores polarity)."""
    # `.expr` is the underlying (positive) event class; `str(.expr)` prints
    # the event name.  `str(ev)` would include the `not_` prefix for negated
    # heads.
    underlying = getattr(ev, 'expr', ev)
    return str(underlying)


def _event_name(ev) -> str:
    """Human-readable event class name (preserves `not_` prefix)."""
    return str(ev)


def _rule_trigger_key(nr) -> str:
    return _event_key(nr.triggering_event)


def _rule_head_keys(nr) -> List[str]:
    """All response-class keys referenced in this rule's obligation chain."""
    keys: List[str] = []
    for cobg in nr.oc.obligations:
        inner = cobg.obligation
        h = getattr(inner, 'head', None)
        if h is not None:
            keys.append(_event_key(h))
    return keys


def _rule_measures(nr) -> Set[str]:
    """Set of measure-name strings read by this rule's condition/defeaters."""
    cond = getattr(nr.og_rule, 'condition', None)
    return _measure_reads(cond)


def _relation_alphabet(rel) -> Set[str]:
    """Set of event-class keys mentioned by a relational constraint.

    Delegates to sleec_event_classification._event_names_in_relation,
    which handles every supported relation kind under both the textX
    (`EventRel`, `MeasureRel`, `Causation`, `Effect`, `Forbid`,
    `UntilEM`, `TimedEM`, `MeasureInv`) and the sleecOp post-parse
    wrapper (`EventRelation`, `MeasureRelation`, `UntilEMRelation`,
    `TimedEMRelation`, `Causation`, `Effect`, `Forbid`) class names,
    and resolves event references whether they are textX nodes (with
    `.name`), sleecOp wrappers (with `.expr.name`), or
    dynamically-created action classes (with `.__name__`).
    """
    from sleec_event_classification import _event_names_in_relation
    return set(_event_names_in_relation(rel))


# ---------------------------- Decomposition ------------------------------

def decompose_rules(
    normalized_rules: Sequence,
    og_rules: Sequence,
    relations: Sequence,
) -> List[List[int]]:
    """Partition `normalized_rules` into components under `~`.

    Returns a list of components; each component is a list of rule indices
    (into `normalized_rules`).  Components are sorted by smallest-index
    member for determinism.

    The relation ~ is defined by two clauses that always apply:
      (a) head-share: two rules share a head CLASS, regardless of polarity.
      (b) cascade:    one rule's head equals another rule's trigger.

    A third clause applies only if the spec uses relational constraints:
      (d) relational-coupling: a relational constraint ties event classes
          from distinct rules' alphabets.

    Measure-coupling is NOT a clause. Two rules that share a measure read
    but whose events are otherwise disjoint are placed in separate
    components; this is sound because measures are environment-only (the
    seed fixes them) and rules do not write measures. Groups joined
    only by a shared measure read cannot interact via that measure.
    """
    n = len(normalized_rules)
    uf = _UF(n)

    # Precompute per-rule keys.
    triggers = [_rule_trigger_key(nr) for nr in normalized_rules]
    heads = [set(_rule_head_keys(nr)) for nr in normalized_rules]

    # (a) head-share: same head class
    head_to_rules: dict = {}
    for i, hs in enumerate(heads):
        for h in hs:
            head_to_rules.setdefault(h, []).append(i)
    for rules_sharing_head in head_to_rules.values():
        for j in rules_sharing_head[1:]:
            uf.union(rules_sharing_head[0], j)

    # (b) cascade: head(r_i) == trigger(r_j)
    trigger_to_rules: dict = {}
    for j, tg in enumerate(triggers):
        trigger_to_rules.setdefault(tg, []).append(j)
    for i, hs in enumerate(heads):
        for h in hs:
            for j in trigger_to_rules.get(h, ()):
                uf.union(i, j)

    # (d) relational constraints, gated: only iterate if the spec has any.
    # Without relations, dropping this clause is sound for the Decomposition
    # Theorem (verified empirically over the benchmark suite). With relations,
    # we conservatively couple every rule whose alphabet intersects the
    # relation's alphabet.
    if relations:
        for rel in relations:
            alpha = _relation_alphabet(rel)
            if not alpha:
                continue
            members: List[int] = []
            for i, nr in enumerate(normalized_rules):
                rule_alpha = set([triggers[i]]) | heads[i]
                if rule_alpha & alpha:
                    members.append(i)
            for j in members[1:]:
                uf.union(members[0], j)

    # Collect components.
    groups: dict = {}
    for i in range(n):
        root = uf.find(i)
        groups.setdefault(root, []).append(i)

    comps = sorted(groups.values(), key=lambda g: min(g))
    for g in comps:
        g.sort()
    return comps


# ============================================================================
# First-class relations in decomposition
# ============================================================================
#
# decompose_rules above returns rule clusters only. The realizability check
# also needs to know which relations belong to which cluster, so it can
# encode only the relevant relations per per-component solve. The richer
# entry point below adds eligible relations as nodes in the union-find and
# returns a Decomposition object that pairs rule indices with relation
# indices per component.
#
# Eligibility (matches RealizabilityChecker's relation partitioning):
#   - SYS_EVENT_AND_MEASURE / MIXED_AND_MEASURE  -> caller errors before
#     reaching here; we still skip them defensively.
#   - MIXED_ENV_SYS_EVENTS                       -> skip silently
#   - everything else                            -> eligible to encode
#
# Within the eligible set:
#   - relations with a non-empty event alphabet    -> become coupling nodes
#   - relations with empty event alphabet (measure -> stay global, asserted in
#     -only / MeasureInv)                            every per-component solve
#
# Output shape: see Component / Decomposition dataclasses below.

@dataclass
class Component:
    """One connected component of the rule-and-relation dependency graph."""
    rule_indices: List[int]                # indices into normalized_rules
    relation_indices: List[int]            # indices into the original relations list

    @property
    def has_relations(self) -> bool:
        return bool(self.relation_indices)


@dataclass
class Decomposition:
    """Result of decompose_with_relations.

    components : list of Components (each contains rules and the relations
                 that couple them; see Component).
    global_relation_indices : indices of relations that are encoded into
                 every component's solve. These are typically measure-only
                 or measure-invariant relations (no event alphabet).
    skipped_relation_indices : indices of relations the realizability
                 checker silently skips (mixed env+sys event relations
                 without a measure). Surfaced for diagnostic display only.
    """
    components: List[Component]
    global_relation_indices: List[int] = field(default_factory=list)
    skipped_relation_indices: List[int] = field(default_factory=list)


def decompose_with_relations(
    normalized_rules: Sequence,
    og_rules: Sequence,
    relations: Sequence,
    event_classification,
) -> Decomposition:
    """Partition rules and eligible relations into components under ~.

    Same coupling rules as `decompose_rules` (clauses (a) head-share and
    (b) cascade between rules), plus:
      - each eligible relation with a non-empty event alphabet is a node
        in the union-find;
      - it is unioned with every rule whose alphabet (trigger ∪ heads)
        intersects the relation's alphabet;
      - relations whose alphabets intersect each other are also unioned
        (so two relations on the same event classes end up together).

    Eligibility is determined via classify_relation_actors:
      - SYS_EVENT_AND_MEASURE / MIXED_AND_MEASURE  : skipped here (the
        checker raises on these before reaching decomposition).
      - MIXED_ENV_SYS_EVENTS                       : skipped silently.
      - SYS_ONLY_EVENTS / ENV_ONLY_EVENTS / MEASURE_ONLY /
        ENV_EVENT_AND_MEASURE / EMPTY              : eligible.

    Among eligible relations, those with empty event alphabet are placed
    in `global_relation_indices` (measure-only and measure-invariant
    relations). The rest become nodes and are assigned to the component
    that contains the rules they touch.

    Args:
        normalized_rules : list of NormalizedRule.
        og_rules         : list of WhenRule (for parallelism with decompose_rules).
        relations        : list of relations from parse_sleec_norm.
        event_classification : an EventClassification from
            sleec_event_classification.classify_events_with_annotations.
            Used to look up event kinds and to call classify_relation_actors.
    """
    from sleec_event_classification import (
        classify_relation_actors, RelationActorKind,
    )

    n_rules = len(normalized_rules)
    triggers = [_rule_trigger_key(nr) for nr in normalized_rules]
    heads = [set(_rule_head_keys(nr)) for nr in normalized_rules]
    rule_alphabets: List[Set[str]] = [
        {triggers[i]} | heads[i] for i in range(n_rules)
    ]

    # Classify each relation and split into eligible-coupling, eligible-global,
    # and skipped buckets.
    coupling_rel_indices: List[int] = []
    coupling_rel_alphabets: List[Set[str]] = []
    global_rel_indices: List[int] = []
    skipped_rel_indices: List[int] = []
    for ri, rel in enumerate(relations):
        kind = classify_relation_actors(rel, event_classification)
        if kind in (RelationActorKind.SYS_EVENT_AND_MEASURE,
                    RelationActorKind.MIXED_AND_MEASURE):
            # Caller should have errored already; skip defensively.
            skipped_rel_indices.append(ri)
            continue
        if kind == RelationActorKind.MIXED_ENV_SYS_EVENTS:
            # Deferred to defeasible-proposals work; not encoded.
            skipped_rel_indices.append(ri)
            continue
        alpha = _relation_alphabet(rel)
        if not alpha:
            global_rel_indices.append(ri)
            continue
        coupling_rel_indices.append(ri)
        coupling_rel_alphabets.append(alpha)

    # Union-find over (rules + coupling relations).
    n_coupling = len(coupling_rel_indices)
    uf = _UF(n_rules + n_coupling)

    # Clause (a): head-share between rules.
    head_to_rules: dict = {}
    for i, hs in enumerate(heads):
        for h in hs:
            head_to_rules.setdefault(h, []).append(i)
    for rules_sharing_head in head_to_rules.values():
        for j in rules_sharing_head[1:]:
            uf.union(rules_sharing_head[0], j)

    # Clause (b): cascade between rules.
    trigger_to_rules: dict = {}
    for j, tg in enumerate(triggers):
        trigger_to_rules.setdefault(tg, []).append(j)
    for i, hs in enumerate(heads):
        for h in hs:
            for j in trigger_to_rules.get(h, ()):
                uf.union(i, j)

    # Clause (d-rules): rules sharing alphabet with a coupling relation.
    for k, rel_alpha in enumerate(coupling_rel_alphabets):
        rel_node = n_rules + k
        for i in range(n_rules):
            if rule_alphabets[i] & rel_alpha:
                uf.union(rel_node, i)

    # Clause (d-relations): relations sharing alphabet with each other.
    for k1 in range(n_coupling):
        for k2 in range(k1 + 1, n_coupling):
            if coupling_rel_alphabets[k1] & coupling_rel_alphabets[k2]:
                uf.union(n_rules + k1, n_rules + k2)

    # Collect components.
    groups_rules: dict = {}
    groups_rels: dict = {}
    for i in range(n_rules):
        root = uf.find(i)
        groups_rules.setdefault(root, []).append(i)
    for k in range(n_coupling):
        root = uf.find(n_rules + k)
        groups_rels.setdefault(root, []).append(coupling_rel_indices[k])

    # Build Component objects. A component must have at least one rule;
    # otherwise its relations become global (this is rare in practice -- it
    # happens only if a relation mentions event classes that no rule touches).
    component_objs: List[Component] = []
    extra_globals_from_rule_less: List[int] = []
    seen_roots: Set[int] = set()
    # First pass: roots with rules.
    for root, rule_idxs in groups_rules.items():
        rel_idxs = sorted(groups_rels.get(root, []))
        component_objs.append(Component(
            rule_indices=sorted(rule_idxs),
            relation_indices=rel_idxs,
        ))
        seen_roots.add(root)
    # Second pass: roots with only relations (no rule). Promote to global.
    for root, rel_idxs in groups_rels.items():
        if root not in seen_roots:
            extra_globals_from_rule_less.extend(rel_idxs)

    # Stable sort: components by smallest rule index.
    component_objs.sort(key=lambda c: c.rule_indices[0] if c.rule_indices
                                       else float('inf'))

    return Decomposition(
        components=component_objs,
        global_relation_indices=sorted(global_rel_indices
                                        + extra_globals_from_rule_less),
        skipped_relation_indices=sorted(skipped_rel_indices),
    )


def has_polarity_clash(normalized_rules, component_indices) -> bool:
    """Return True iff some head event class appears with BOTH polarities
    (positive and negative) among the rules in the given component.

    If this returns False, the component is trivially realizable on any
    partial trace: no two obligations in the component can contradict on
    the same head class, so the solver can always place system events in
    their respective windows without collision. This is the short-circuit
    used by RealizabilityChecker to skip solver calls.
    """
    pos_heads: Set[str] = set()
    neg_heads: Set[str] = set()
    for i in component_indices:
        nr = normalized_rules[i]
        for cobg in nr.oc.obligations:
            obg = cobg.obligation
            h = getattr(obg, 'head', None)
            if h is None:
                continue
            cls = _event_key(h)
            if bool(getattr(h, 'neg', False)):
                neg_heads.add(cls)
            else:
                pos_heads.add(cls)
    return bool(pos_heads & neg_heads)


def describe_components(
    normalized_rules: Sequence,
    components: Sequence[Sequence[int]],
) -> str:
    """One-line-per-component human summary. If a component has no
    polarity clash on any head class it is annotated as 'no clash';
    otherwise as 'has clash' (which is the condition under which the
    solver needs to be invoked)."""
    lines: List[str] = []
    for ci, comp in enumerate(components):
        names = []
        for idx in comp:
            nr = normalized_rules[idx]
            name = getattr(nr.og_rule, 'name', f'<rule#{idx}>')
            trig = _event_name(nr.triggering_event)
            heads = ','.join(
                _event_name(cobg.obligation.head)
                for cobg in nr.oc.obligations
                if hasattr(cobg.obligation, 'head')
            )
            names.append(f'{name}#{idx}({trig}->{heads})')
        clash = has_polarity_clash(normalized_rules, comp)
        tag = 'has clash' if clash else 'no clash'
        lines.append(f'component {ci+1} (size {len(comp)}, {tag}): '
                     f'{", ".join(names)}')
    return '\n'.join(lines)
