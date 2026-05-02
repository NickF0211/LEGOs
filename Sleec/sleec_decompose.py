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

from typing import Iterable, List, Sequence, Set, Tuple


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
    """Set of event-class keys mentioned by a relational constraint."""
    keys: Set[str] = set()
    for attr in ('lhs', 'rhs', 'start_trigger', 'end_trigger'):
        v = getattr(rel, attr, None)
        if v is not None:
            keys.add(_event_key(v))
    return keys


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
    """
    n = len(normalized_rules)
    uf = _UF(n)

    # Precompute per-rule keys.
    triggers = [_rule_trigger_key(nr) for nr in normalized_rules]
    heads = [set(_rule_head_keys(nr)) for nr in normalized_rules]
    measures = [_rule_measures(nr) for nr in normalized_rules]

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

    # (c) measure-coupling
    measure_to_rules: dict = {}
    for i, ms in enumerate(measures):
        for m in ms:
            measure_to_rules.setdefault(m, []).append(i)
    for rules_on_measure in measure_to_rules.values():
        for j in rules_on_measure[1:]:
            uf.union(rules_on_measure[0], j)

    # (d) relational constraints: group all rules whose alphabets intersect
    # the relation's alphabet.
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


def describe_components(
    normalized_rules: Sequence,
    components: Sequence[Sequence[int]],
) -> str:
    """One-line-per-component human summary."""
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
        lines.append(f'component {ci+1} (size {len(comp)}): {", ".join(names)}')
    return '\n'.join(lines)
