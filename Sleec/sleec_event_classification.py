"""Event-kind classification with annotation support and conflict detection.

Pipeline (see Sleec/docs/event_kind_annotations_design.md):
  1. Seed each declared event from its `as system|environment` annotation.
  2. Seed `SYSTEM` from rule responses (events that appear in any
     primary, otherwise, else, or defeater consequence).
  3. Propagate `SYSTEM` through relations: any unannotated event that
     co-occurs in a multi-event relation with a sys event becomes sys.
  4. Default any remaining `UNKNOWN` to `ENVIRONMENT`.

Conflicts (errors) are recorded when:
  - An event annotated as environment appears in a rule's response
    (`ANNOTATED_ENV_BUT_RESPONSE`).
  - An event annotated as environment co-occurs with a system event in a
    relation (`ANNOTATED_ENV_BUT_SYS_RELATION`).
  - A multi-event relation mixes sys and env (`CROSS_KIND_RELATION`,
    typically subsumed by the prior two but emitted as a safety net).

Warnings:
  - An event annotated as system never appears as a rule response
    (`ANNOTATED_SYS_BUT_NEVER_RESPONSE`).

Public API:
  - classify_events_with_annotations(model) -> EventClassification
  - format_conflicts(ec) -> str
  - EventClassificationError(ec) — exception carrying an EventClassification

The model passed in is the textX AST root produced by sleecParser.parse_sleec.
"""

from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Sequence, Set, Tuple


# -------------------------- isXinstance compatibility --------------------------

def _is(node, cls_name: str) -> bool:
    """Match the `isXinstance(node, "ClsName")` pattern used elsewhere in this
    codebase, but without importing from sleecParser to avoid an import cycle."""
    if node is None:
        return False
    return type(node).__name__ == cls_name


# ------------------------------- Data classes -------------------------------

class Kind(Enum):
    SYSTEM = "system"
    ENVIRONMENT = "environment"
    UNKNOWN = "unknown"


class ReasonSource(Enum):
    ANNOTATION = "annotation"
    RULE_RESPONSE = "rule_response"
    RELATION_PROPAGATION = "relation_propagation"
    DEFAULT = "default"


@dataclass
class Reason:
    source: ReasonSource
    detail: str
    kind: Kind
    tx_position: Optional[Tuple[int, int]] = None  # (start, end) char offsets


class ConflictCode(Enum):
    ANNOTATED_ENV_BUT_RESPONSE = "annotated_env_but_response"
    ANNOTATED_ENV_BUT_SYS_RELATION = "annotated_env_but_sys_relation"
    CROSS_KIND_RELATION = "cross_kind_relation"
    ANNOTATED_SYS_BUT_NEVER_RESPONSE = "annotated_sys_but_never_response"


@dataclass
class Conflict:
    code: ConflictCode
    event_names: List[str]
    detail: str
    reasons: List[Reason] = field(default_factory=list)
    is_warning: bool = False


@dataclass
class EventClassification:
    kind: Dict[str, Kind] = field(default_factory=dict)
    reasons: Dict[str, List[Reason]] = field(default_factory=lambda: defaultdict(list))
    conflicts: List[Conflict] = field(default_factory=list)

    @property
    def errors(self) -> List[Conflict]:
        return [c for c in self.conflicts if not c.is_warning]

    @property
    def warnings(self) -> List[Conflict]:
        return [c for c in self.conflicts if c.is_warning]

    @property
    def has_errors(self) -> bool:
        return any(not c.is_warning for c in self.conflicts)

    @property
    def has_warnings(self) -> bool:
        return any(c.is_warning for c in self.conflicts)


class EventClassificationError(Exception):
    """Raised when classification finds blocking conflicts. Carries the
    full EventClassification so callers can format diagnostics or recover."""
    def __init__(self, classification: EventClassification):
        self.classification = classification
        super().__init__(format_conflicts(classification))


# ====================== Relation actor classification =====================
#
# Once the event kinds are known, every relation can be tagged by which
# actor kinds participate in it. The realizability checker uses this to
# decide whether a relation should be (a) encoded into the FOL* query,
# (b) reported as an unsupported case, or (c) silently skipped.

class RelationActorKind(Enum):
    SYS_ONLY_EVENTS = "sys_only_events"          # encode in checker
    ENV_ONLY_EVENTS = "env_only_events"          # skip (sampler's job)
    MIXED_ENV_SYS_EVENTS = "mixed_env_sys_events"  # skip (deferred to defeasible)
    SYS_EVENT_AND_MEASURE = "sys_event_and_measure"  # ERROR (not yet supported)
    ENV_EVENT_AND_MEASURE = "env_event_and_measure"  # skip (sampler's job, partly)
    MIXED_AND_MEASURE = "mixed_and_measure"      # ERROR (not yet supported)
    MEASURE_ONLY = "measure_only"                # skip (sampler enforces these)
    EMPTY = "empty"


def _relation_involves_measure(rel) -> bool:
    """True iff `rel` mentions a measure (expression or invariant)."""
    cls = type(rel).__name__
    # textX: MeasureRel / MeasureInv. sleecOp: MeasureRelation.
    if cls in ("MeasureRel", "MeasureInv", "MeasureRelation"):
        return True
    # Causation / Effect / Forbid: have an `effect` field (an MBoolExpr in textX,
    # a lambda over measures in the sleecOp wrapper).
    if cls in ("Causation", "Effect", "Forbid"):
        return getattr(rel, "effect", None) is not None
    # UntilEM / TimedEM: have an `inv` (textX) or `response` (sleecOp wrapper).
    if cls in ("UntilEM", "UntilEMRelation", "TimedEM", "TimedEMRelation"):
        return (getattr(rel, "inv", None) is not None
                or getattr(rel, "response", None) is not None)
    return False


def classify_relation_actors(rel, ec: EventClassification) -> RelationActorKind:
    """Return a single tag describing which actor kinds participate in
    `rel`, given the event-kind classification `ec`."""
    event_names = _event_names_in_relation(rel)
    has_measure = _relation_involves_measure(rel)

    sys_evs = [n for n in event_names if ec.kind.get(n) == Kind.SYSTEM]
    env_evs = [n for n in event_names if ec.kind.get(n) == Kind.ENVIRONMENT]
    has_sys = bool(sys_evs)
    has_env = bool(env_evs)

    if not has_sys and not has_env and not has_measure:
        return RelationActorKind.EMPTY
    if not has_sys and not has_env:
        return RelationActorKind.MEASURE_ONLY
    if has_sys and has_env and has_measure:
        return RelationActorKind.MIXED_AND_MEASURE
    if has_sys and has_env:
        return RelationActorKind.MIXED_ENV_SYS_EVENTS
    if has_sys and has_measure:
        return RelationActorKind.SYS_EVENT_AND_MEASURE
    if has_env and has_measure:
        return RelationActorKind.ENV_EVENT_AND_MEASURE
    if has_sys:
        return RelationActorKind.SYS_ONLY_EVENTS
    if has_env:
        return RelationActorKind.ENV_ONLY_EVENTS
    return RelationActorKind.EMPTY


@dataclass
class RelationClassificationError(Exception):
    """Raised when the realizability checker encounters a relation kind it
    cannot handle yet (currently: any relation that mixes system events
    with measures). Carries the offending relations + their actor kinds
    so callers can format diagnostics."""
    offenders: List[Tuple[object, RelationActorKind]]

    def __post_init__(self):
        # Build an Exception message from the offenders.
        lines = ["one or more relations couple system events with measures, "
                 "which is not yet supported by the realizability check:"]
        for rel, kind in self.offenders:
            cls = type(rel).__name__
            event_names = _event_names_in_relation(rel)
            try:
                pos = (rel._tx_position, rel._tx_position_end)
            except AttributeError:
                pos = None
            ev_str = ", ".join(event_names) if event_names else "(no events)"
            pos_str = f" at chars {pos[0]}..{pos[1]}" if pos else ""
            lines.append(f"  - {cls} ({kind.value}) involving "
                         f"event(s) [{ev_str}] + measure expression{pos_str}")
        super().__init__("\n".join(lines))


# ------------------------ Response-event collection ------------------------

def _collect_response_event_names_from_rule(rule_node) -> Set[str]:
    """Collect every event class name appearing in `rule_node`'s response.

    Walks Response / InnerResponse alternatives, otherwise/else branches,
    and defeater consequences. Polarity (the `not` in `Occ.neg`) does not
    matter for classification.
    """
    bucket: Set[str] = set()

    def walk(node):
        if node is None:
            return
        # Occ: { event: Trigger, neg: bool, ... }
        # Trigger: { event: [Event] }    so deref once more.
        if _is(node, "Occ") and getattr(node, "event", None) is not None:
            trig = node.event
            if hasattr(trig, "event") and trig.event is not None:
                ev = trig.event
                if hasattr(ev, "name") and ev.name is not None:
                    bucket.add(ev.name)
            return

        # Response / InnerResponse / ExtendedResponse / Alternative tree.
        # Walk all child fields generically.
        for attr in dir(node):
            if attr.startswith("_") or attr == "parent":
                continue
            try:
                v = getattr(node, attr)
            except Exception:
                continue
            if v is None or isinstance(v, (str, int, float, bool, bytes)):
                continue
            if isinstance(v, list):
                for item in v:
                    if hasattr(item, "__module__") and \
                       getattr(item, "__module__", "").startswith("textx"):
                        walk(item)
            elif hasattr(v, "__module__") and \
                 getattr(v, "__module__", "").startswith("textx"):
                walk(v)

    walk(rule_node.response if hasattr(rule_node, "response") else None)
    # Also scan defeaters.
    for d in getattr(rule_node, "defeaters", []) or []:
        walk(getattr(d, "response", None))
        walk(getattr(d, "alternative", None))
    return bucket


# ---------------------- Relation event extraction ----------------------

def _event_class_name(ev) -> Optional[str]:
    """Best-effort extract of the event class name from any of the shapes
    relations can carry: textX Event reference (.name), sleecOp wrapper
    (.expr.name), or dynamically-created action class (.__name__)."""
    if ev is None:
        return None
    # textX Event reference.
    if hasattr(ev, "name") and isinstance(ev.name, str):
        return ev.name
    # sleecOp wrapper (e.g., Event class with neg/expr attrs).
    expr = getattr(ev, "expr", None)
    if expr is not None and hasattr(expr, "name") and isinstance(expr.name, str):
        return expr.name
    # Dynamically-created action class — used by sleecOp.{EventRelation,
    # Causation, Effect, Forbid}.
    if isinstance(ev, type) and hasattr(ev, "__name__"):
        return ev.__name__
    return None


def _event_names_in_relation(rel) -> List[str]:
    """Return the list of event class names that participate in `rel`.

    Each relation kind exposes its events differently:
      - EventRel / EventRelation:     rel.lhs, rel.rhs    (event refs / classes)
      - Causation, Effect, Forbid:    rel.cause            (event ref / class)
      - UntilEM / UntilEMRelation:    rel.start_trigger, rel.end_trigger (triggers
                                       or classes; deref `.event` for textX nodes)
      - TimedEM / TimedEMRelation:    rel.start_trigger
      - MeasureRel / MeasureInv:      no events
    """
    names: List[str] = []
    cls = type(rel).__name__

    if cls in ("EventRel", "EventRelation"):
        for side in ("lhs", "rhs"):
            ev = getattr(rel, side, None)
            n = _event_class_name(ev)
            if n is not None:
                names.append(n)
    elif cls in ("Causation", "Effect", "Forbid"):
        ev = getattr(rel, "cause", None)
        n = _event_class_name(ev)
        if n is not None:
            names.append(n)
    elif cls in ("UntilEM", "UntilEMRelation", "TimedEM", "TimedEMRelation"):
        for trig_attr in ("start_trigger", "end_trigger"):
            trig = getattr(rel, trig_attr, None)
            if trig is None:
                continue
            # textX Trigger has an `event` field; sleecOp may store the class
            # directly on `start_trigger`.
            ev = getattr(trig, "event", trig)
            n = _event_class_name(ev)
            if n is not None:
                names.append(n)
    return names


# ---------------------------- Main entrypoint ----------------------------

def classify_events_with_annotations(model) -> EventClassification:
    """Run the four-step classification + conflict detection. Returns an
    EventClassification with one entry per declared event."""
    ec = EventClassification()

    # ---- Step 0: enumerate declared events -----------------------------------
    declared: List[Tuple[str, object]] = []  # (name, ast_node)
    for d in getattr(model, "definitions", []) or []:
        if _is(d, "Event"):
            declared.append((d.name, d))
            ec.kind[d.name] = Kind.UNKNOWN

    # ---- Step 1: seed kinds from annotations --------------------------------
    annotated_as_sys: Set[str] = set()
    for name, node in declared:
        kind_str = getattr(node, "kind", None)
        if not kind_str:  # None or empty string from textX
            continue
        if kind_str == "system":
            ec.kind[name] = Kind.SYSTEM
            annotated_as_sys.add(name)
            ec.reasons[name].append(Reason(
                source=ReasonSource.ANNOTATION,
                detail="declared as system",
                kind=Kind.SYSTEM,
                tx_position=(node._tx_position, node._tx_position_end),
            ))
        elif kind_str == "environment":
            ec.kind[name] = Kind.ENVIRONMENT
            ec.reasons[name].append(Reason(
                source=ReasonSource.ANNOTATION,
                detail="declared as environment",
                kind=Kind.ENVIRONMENT,
                tx_position=(node._tx_position, node._tx_position_end),
            ))

    # ---- Step 2: seed SYSTEM from rule responses ----------------------------
    response_uses: Dict[str, List[Tuple[str, Tuple[int, int]]]] = defaultdict(list)
    rb = getattr(model, "ruleBlock", None)
    if rb is not None:
        for r in rb.rules:
            rule_name = getattr(r, "name", "<unnamed rule>")
            position = (r._tx_position, r._tx_position_end)
            for ev_name in _collect_response_event_names_from_rule(r):
                response_uses[ev_name].append((rule_name, position))

    for ev_name, occurrences in response_uses.items():
        if ev_name not in ec.kind:
            # event not declared -- defensive; sleecParser should reject this earlier
            continue
        existing = ec.kind[ev_name]
        for rule_name, position in occurrences:
            r_response = Reason(
                source=ReasonSource.RULE_RESPONSE,
                detail=f"appears in response of rule '{rule_name}'",
                kind=Kind.SYSTEM,
                tx_position=position,
            )
            if existing == Kind.UNKNOWN:
                ec.kind[ev_name] = Kind.SYSTEM
                existing = Kind.SYSTEM
                ec.reasons[ev_name].append(r_response)
            elif existing == Kind.SYSTEM:
                ec.reasons[ev_name].append(r_response)
            elif existing == Kind.ENVIRONMENT:
                # Annotation says env, rule says sys: hard conflict.
                ec.conflicts.append(Conflict(
                    code=ConflictCode.ANNOTATED_ENV_BUT_RESPONSE,
                    event_names=[ev_name],
                    detail=(f"event '{ev_name}' is declared as environment "
                            f"but used as a response in rule '{rule_name}'"),
                    reasons=list(ec.reasons[ev_name]) + [r_response],
                ))

    # ---- Step 3: propagate SYSTEM through relations ------------------------
    relations_with_events: List[Tuple[str, List[str], Tuple[int, int]]] = []
    rel_block = getattr(model, "relBlock", None)
    if rel_block is not None:
        for rel in rel_block.relations:
            event_names = _event_names_in_relation(rel)
            if len(event_names) >= 2:
                rel_label = type(rel).__name__
                # Try to get a more descriptive label for EventRel.
                if rel_label == "EventRel":
                    rel_label = f"EventRel `{getattr(rel, 'rel', '?')} " \
                                f"{event_names[0]} {event_names[1]}`"
                relations_with_events.append((
                    rel_label,
                    event_names,
                    (rel._tx_position, rel._tx_position_end),
                ))

    worklist: deque = deque(name for name, k in ec.kind.items() if k == Kind.SYSTEM)
    while worklist:
        cur = worklist.popleft()
        for rel_label, names, pos in relations_with_events:
            if cur not in names:
                continue
            for other in names:
                if other == cur or other not in ec.kind:
                    continue
                existing = ec.kind[other]
                propagation_reason = Reason(
                    source=ReasonSource.RELATION_PROPAGATION,
                    detail=f"co-occurs with system event '{cur}' in {rel_label}",
                    kind=Kind.SYSTEM,
                    tx_position=pos,
                )
                if existing == Kind.UNKNOWN:
                    ec.kind[other] = Kind.SYSTEM
                    ec.reasons[other].append(propagation_reason)
                    worklist.append(other)
                elif existing == Kind.SYSTEM:
                    # Already sys; record provenance unless we already did
                    # for this exact (rel, neighbour) pair.
                    if not any(
                        r.source == ReasonSource.RELATION_PROPAGATION and
                        r.tx_position == pos and r.detail == propagation_reason.detail
                        for r in ec.reasons[other]
                    ):
                        ec.reasons[other].append(propagation_reason)
                elif existing == Kind.ENVIRONMENT:
                    # Annotation says env, relation forces sys: conflict.
                    if not any(
                        c.code == ConflictCode.ANNOTATED_ENV_BUT_SYS_RELATION
                        and other in c.event_names
                        and any(r.tx_position == pos for r in c.reasons)
                        for c in ec.conflicts
                    ):
                        ec.conflicts.append(Conflict(
                            code=ConflictCode.ANNOTATED_ENV_BUT_SYS_RELATION,
                            event_names=[other],
                            detail=(f"event '{other}' is declared as "
                                    f"environment but appears in {rel_label} "
                                    f"with system event '{cur}'"),
                            reasons=list(ec.reasons[other]) + [propagation_reason],
                        ))

    # ---- Step 4: default remaining UNKNOWN to ENVIRONMENT ------------------
    for name in list(ec.kind.keys()):
        if ec.kind[name] == Kind.UNKNOWN:
            ec.kind[name] = Kind.ENVIRONMENT
            ec.reasons[name].append(Reason(
                source=ReasonSource.DEFAULT,
                detail="no annotation, no rule response, no relation propagation",
                kind=Kind.ENVIRONMENT,
            ))

    # ---- Step 5: cross-kind relation safety check --------------------------
    for rel_label, names, pos in relations_with_events:
        kinds_in_rel = {ec.kind.get(n, Kind.UNKNOWN) for n in names}
        if Kind.SYSTEM in kinds_in_rel and Kind.ENVIRONMENT in kinds_in_rel:
            # Skip if we already reported via Step 3 (annotated_env_but_sys_relation).
            already = any(
                c.code == ConflictCode.ANNOTATED_ENV_BUT_SYS_RELATION
                and any(r.tx_position == pos for r in c.reasons)
                for c in ec.conflicts
            )
            if not already:
                ec.conflicts.append(Conflict(
                    code=ConflictCode.CROSS_KIND_RELATION,
                    event_names=names,
                    detail=(f"{rel_label} mixes system and environment events: "
                            + ", ".join(f"'{n}' ({ec.kind[n].value})"
                                        for n in names)),
                    reasons=[r for n in names for r in ec.reasons[n]],
                ))

    # ---- Step 6: warning for sys annotated but never used as response ------
    for name in ec.kind:
        if (name in annotated_as_sys
                and ec.kind[name] == Kind.SYSTEM
                and not any(r.source == ReasonSource.RULE_RESPONSE
                            for r in ec.reasons[name])):
            ec.conflicts.append(Conflict(
                code=ConflictCode.ANNOTATED_SYS_BUT_NEVER_RESPONSE,
                event_names=[name],
                detail=(f"event '{name}' is annotated as system but is never "
                        "produced as a rule response (modeller may be wrong)"),
                reasons=list(ec.reasons[name]),
                is_warning=True,
            ))

    return ec


# --------------------------- Diagnostic formatting --------------------------

def format_conflicts(ec: EventClassification) -> str:
    """Render every conflict in `ec` as a human-readable diagnostic block."""
    if not ec.conflicts:
        return "[event-classification] no conflicts"
    lines: List[str] = []
    for c in ec.conflicts:
        prefix = "WARNING" if c.is_warning else "CONFLICT"
        lines.append(f"[event-classification] {prefix} ({c.code.value}): "
                     f"{c.detail}")
        for r in c.reasons:
            pos = ""
            if r.tx_position is not None:
                pos = f" (chars {r.tx_position[0]}..{r.tx_position[1]})"
            lines.append(f"    - claims kind={r.kind.value} via "
                         f"{r.source.value}: {r.detail}{pos}")
    return "\n".join(lines)


def format_classification(ec: EventClassification) -> str:
    """Render the per-event kind decisions and their dominant reason."""
    if not ec.kind:
        return "[event-classification] no events declared"
    lines = ["[event-classification] event kinds:"]
    for name in sorted(ec.kind):
        kind = ec.kind[name].value
        # Dominant reason: pick the strongest source in priority order.
        priority = (ReasonSource.ANNOTATION, ReasonSource.RULE_RESPONSE,
                    ReasonSource.RELATION_PROPAGATION, ReasonSource.DEFAULT)
        chosen = None
        for src in priority:
            for r in ec.reasons[name]:
                if r.source == src:
                    chosen = r
                    break
            if chosen is not None:
                break
        detail = chosen.detail if chosen else "(no provenance)"
        lines.append(f"    {name:30s} -> {kind:11s}  ({detail})")
    return "\n".join(lines)
