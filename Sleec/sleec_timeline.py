"""Obligation timeline visualization for SLEEC bounded realizability.

Given the normalized rules, a sampled partial trace, and the set of
culprit rule names, this module produces a monospaced grid that shows:

    - Row per environment event class (seed-driven).
    - Row per measure field (seed-driven).
    - Divider.
    - Row per (head class, polarity) that is required by any fired rule,
      showing which rule-id(s) demand that head in the cell's time slot.
    - A final "conflict" row flagging cells where a required head and a
      forbidden head coincide.

The builder returns:
    grid_text:    str
    highlight:    list[(start, end, tag)]  where tag ∈ {
                       'culprit_rule',    # rule name inside a [R*]
                       'trigger_event',   # env event or measure name
                       'conflict',        # cell where + and - clash
                   }

The frontend inserts `grid_text` using the same tag-aware rendering
loop as `check_situational_conflict`.
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Sequence, Set, Tuple


# ---------- Data types -----------------------------------------------------

Span = Tuple[int, int, str]     # (start, end, tag_name)


def _const_int(x) -> int:
    """Extract an int from SleecNorm.Constant-or-int."""
    if hasattr(x, 'val'):
        return int(x.val)
    return int(x)


def _rule_obligations(nr) -> List[Tuple[str, bool, int, int]]:
    """Return [(head_class_str, is_negative, start, end), ...] for this rule.

    `head_class_str` is the underlying (positive) event class name.
    `is_negative` is True iff the obligation is a negated head (not_X).
    `start`, `end` are the window bounds (non-negative integers).
    """
    out = []
    for cobg in nr.oc.obligations:
        obg = cobg.obligation
        head = getattr(obg, 'head', None)
        tw = getattr(obg, 'deadline', None)
        if head is None or tw is None:
            continue
        cls = str(getattr(head, 'expr', head))
        neg = bool(getattr(head, 'neg', False))
        out.append((cls, neg, _const_int(tw.start), _const_int(tw.end)))
    return out


# ---------- Main builder ---------------------------------------------------

def build_timeline(
    normalized_rules,
    trace: dict,
    culprit_names: Set[str],
    *,
    col_width: int = 8,
    verdict_status: Optional[str] = None,
) -> Tuple[str, List[Span]]:
    """Build a textual grid + highlight spans.

    Args:
        normalized_rules: the list of NormalizedRule objects.
        trace: the AbstractTraceSampler output dict, keys:
            N, environment_events, bool_measures, num_measures,
            scalar_measures, per_step ([{t, events, measures}]),
            rules_fired ([(rule_name, t), ...]).
        culprit_names: set of rule names belonging to the failing
            dependency-graph component (empty if realizable).
        col_width: characters per time-step column.
        verdict_status: optional verdict produced by the realizability
            checker. Used to tailor the wording of the per-conflict
            explanation lines:
              - "unrealizable" -> "this conflict is realized in the verdict"
              - "realizable"   -> "the solver scheduled around this"
              - None           -> no parenthetical (the timeline's
                                  "Reading:" legend already explains ⚠)
            Only affects the explanation text; structural output is the
            same regardless of value.
    """
    N = trace["N"]
    per_step = trace["per_step"]
    env_events = list(trace.get("environment_events", []))
    bool_measures = list(trace.get("bool_measures", []))
    num_measures = list(trace.get("num_measures", []))
    scalar_measures = list(trace.get("scalar_measures", []))
    rules_fired = trace.get("rules_fired", [])

    # Map rule_name -> NormalizedRule(s) (may be multiple for defeater normalization).
    name_to_rules: Dict[str, List] = {}
    for nr in normalized_rules:
        nm = getattr(nr.og_rule, "name", None)
        if nm is None:
            continue
        name_to_rules.setdefault(nm, []).append(nr)

    # Map (trigger_class_str) -> list of rule_name that fires on it.
    # Used to transitively propagate firings when one rule's positive head
    # becomes another's trigger.
    trigger_class_to_rules: Dict[str, List[str]] = {}
    for nr in normalized_rules:
        nm = getattr(nr.og_rule, "name", None)
        if nm is None:
            continue
        te = nr.triggering_event
        cls = str(getattr(te, "expr", te))
        trigger_class_to_rules.setdefault(cls, []).append(nm)

    # (head_class, is_neg, time) -> list of rule_name
    cells: Dict[Tuple[str, bool, int], List[str]] = {}
    head_classes_pos: Set[str] = set()
    head_classes_neg: Set[str] = set()

    # Work queue of (rule_name, time) firings.  Start with seed firings.
    queue: List[Tuple[str, int]] = list(rules_fired)
    seen: Set[Tuple[str, int]] = set()
    CASCADE_BUDGET = 200   # guard against runaway transitive closure
    while queue and len(seen) < CASCADE_BUDGET:
        rule_name, tau = queue.pop(0)
        if (rule_name, tau) in seen:
            continue
        seen.add((rule_name, tau))
        for nr in name_to_rules.get(rule_name, ()):
            for cls, neg, s, e in _rule_obligations(nr):
                if neg:
                    head_classes_neg.add(cls)
                else:
                    head_classes_pos.add(cls)
                # Expand the window.
                for t in range(tau + s, tau + e + 1):
                    cells.setdefault((cls, neg, t), []).append(rule_name)
                    # Cascade: a positive obligation placed at time t may
                    # itself be the trigger of some rule r'.  Add (r', t)
                    # to the queue so its obligations are also displayed.
                    if not neg:
                        for cascaded in trigger_class_to_rules.get(cls, ()):
                            if (cascaded, t) not in seen:
                                queue.append((cascaded, t))

    # Also count the maximum time any obligation reaches (to extend the
    # grid past N if needed). Capped at N + 5 for readability.
    max_time = N
    for (_, _, t) in cells:
        if t > max_time:
            max_time = t
    max_time = min(max_time, N + 5)

    # ---- Build the grid text line by line.
    buf: List[str] = []
    spans: List[Span] = []

    def emit(text: str) -> None:
        buf.append(text)

    def emit_tagged(text: str, tag: str) -> None:
        start = sum(len(x) for x in buf)
        buf.append(text)
        spans.append((start, start + len(text), tag))

    # Compute row_label_w dynamically: every label needs to fit
    # within "PREFIX  LABEL  " (prefix is "ENV ", "SYS ", or "WARN").
    # Without this, a long event name (e.g., callEmergencyServices, 21
    # chars) overflows the label slot and runs straight into the first
    # cell, breaking column alignment.
    candidate_labels: List[str] = []
    candidate_labels.extend(f"ENV  {e}" for e in env_events)
    candidate_labels.extend(
        f"ENV  {m}" for m in (bool_measures + num_measures
                              + scalar_measures))
    candidate_labels.extend(f"SYS  {cls}" for cls in head_classes_pos)
    candidate_labels.extend(f"SYS  ¬{cls}" for cls in head_classes_neg)
    # The conflict-row label depends on whether the verdict is known.
    # UNREAL specs: the conflict is proven. REAL specs: the solver dodged
    # what would otherwise be a conflict. Without a verdict: it's a
    # potential clash flagged by static analysis.
    if verdict_status == "unrealizable":
        conflict_row_label = "CONFLICT (proven)"
        conflict_word = "conflict"
    elif verdict_status == "realizable":
        conflict_row_label = "(avoided) WARN"
        conflict_word = "potential conflict"
    else:
        conflict_row_label = "WARN potential conflict"
        conflict_word = "potential conflict"
    candidate_labels.append(conflict_row_label)
    if candidate_labels:
        row_label_w = max(len(s) for s in candidate_labels) + 2
    else:
        row_label_w = 22
    # Cell width: at minimum col_width, but stretch to fit the widest
    # rule cluster like "[R1,R2,R3]" (avoids ellipsis-cropping unless a
    # cell really is huge).
    widest_cell = 4  # minimum: "[R3] "
    for cell_set in cells.values():
        names = list(dict.fromkeys(cell_set))
        # Length of "[R1,R2,...]" string before any truncation.
        rendered_len = 2 + sum(len(n) for n in names) + max(0, len(names) - 1)
        if rendered_len > widest_cell:
            widest_cell = rendered_len
    col_w = max(col_width, widest_cell + 1)  # +1 for visual separator

    def header(title: str) -> None:
        emit(f"\n-- {title} --\n")

    def time_row() -> None:
        emit(" " * row_label_w)
        for t in range(1, max_time + 1):
            mark_over = t > N
            # Put a · around times past the horizon so reader sees the overshoot.
            col_label = f"t={t}{'·' if mark_over else ''}"
            col = col_label.ljust(col_w)
            emit(col)
        emit("\n")

    def ruler() -> None:
        emit("-" * row_label_w)
        for t in range(1, max_time + 1):
            emit("-" * col_w)
        emit("\n")

    header("Obligation timeline")
    time_row()
    ruler()

    # ENV events
    for ev in env_events:
        emit(f"ENV  ")
        emit_tagged(ev.ljust(row_label_w - 5), "trigger_event")
        for t in range(1, max_time + 1):
            present = any(
                step["t"] == t and ev in step.get("events", set())
                for step in per_step
            )
            cell = "● ".ljust(col_w) if present else " " * col_w
            emit(cell)
        emit("\n")

    # Measures (condensed: one row per measure)
    for m in bool_measures + num_measures + scalar_measures:
        emit(f"ENV  ")
        emit_tagged(m.ljust(row_label_w - 5), "trigger_event")
        for t in range(1, max_time + 1):
            val = ""
            for step in per_step:
                if step["t"] == t:
                    mv = step.get("measures", {})
                    if m in mv:
                        v = mv[m]
                        if isinstance(v, bool):
                            val = "T" if v else "F"
                        elif isinstance(v, int):
                            val = str(v)
                        else:
                            val = str(v)[:col_w - 2]
                    break
            emit(val.ljust(col_w) if val else " " * col_w)
        emit("\n")

    ruler()

    # SYS positive obligations
    for cls in sorted(head_classes_pos):
        emit(f"SYS  ")
        emit(cls.ljust(row_label_w - 5))
        for t in range(1, max_time + 1):
            occupants = cells.get((cls, False, t), [])
            if not occupants:
                emit(" " * col_w)
            else:
                # Render [R1,R2] truncated to fit col_w.
                tag_cell(emit, emit_tagged, occupants, culprit_names, col_w)
        emit("\n")

    # SYS negative obligations
    for cls in sorted(head_classes_neg):
        emit(f"SYS  ")
        emit(("¬" + cls).ljust(row_label_w - 5))
        for t in range(1, max_time + 1):
            occupants = cells.get((cls, True, t), [])
            if not occupants:
                emit(" " * col_w)
            else:
                tag_cell(emit, emit_tagged, occupants, culprit_names, col_w)
        emit("\n")

    # Conflict row: a cell has a potential conflict iff there are both
    # positive and negative obligations at the same (cls, t). NOTE this
    # is an over-approximation — the solver may still find a witness
    # because (a) the cascade shown here is worst-case, not solver-
    # verified; (b) rule conditions / defeaters may prevent firings
    # that we pessimistically included.
    conflict_classes = head_classes_pos & head_classes_neg
    if conflict_classes:
        ruler()
        emit(conflict_row_label.ljust(row_label_w))
        for t in range(1, max_time + 1):
            conflicts_here = [
                cls for cls in conflict_classes
                if cells.get((cls, False, t)) and cells.get((cls, True, t))
            ]
            if conflicts_here:
                label = "⚠ ".ljust(col_w)
                emit_tagged(label, "conflict")
            else:
                emit(" " * col_w)
        emit("\n")
        # Explanation lines.
        for cls in sorted(conflict_classes):
            conflicting_times = sorted({
                t
                for t in range(1, max_time + 1)
                if cells.get((cls, False, t)) and cells.get((cls, True, t))
            })
            if not conflicting_times:
                continue
            # Tailor the explanation to the verdict status (if known).
            # When the verdict is not provided, drop the parenthetical
            # entirely — the timeline's "Reading:" legend already explains
            # what ⚠ means, and a generic "may or may not" hedge here adds
            # nothing.
            if verdict_status == "unrealizable":
                tail = "  (this conflict is realized; see UNREALIZABLE verdict above)"
            elif verdict_status == "realizable":
                tail = "  (the solver scheduled around this; see REALIZABLE verdict above)"
            else:
                tail = ""
            emit(f"     {conflict_word} on {cls} @ t ∈ "
                 f"{_range_str(conflicting_times)}{tail}\n")

    return "".join(buf), spans


def tag_cell(emit, emit_tagged, occupants: Iterable[str],
             culprit_names: Set[str], col_w: int) -> None:
    """Render a cell listing a set of rule names, tagging culprit names
    with the `culprit_rule` tag. Fits into `col_w` characters (may be
    truncated with an ellipsis)."""
    parts = list(dict.fromkeys(occupants))
    # Render "[R1,R2]" with each R tagged if culprit.
    emit("[")
    written = 1
    budget = col_w - 2  # minus brackets
    for i, name in enumerate(parts):
        piece = name if i == 0 else "," + name
        if written + len(piece) > budget:
            # truncate with …
            emit("…")
            written += 1
            break
        if i > 0:
            emit(",")
            written += 1
        if name in culprit_names:
            emit_tagged(name, "culprit_rule")
        else:
            emit(name)
        written += len(name)
    emit("]")
    written += 1
    if written < col_w:
        emit(" " * (col_w - written))


def _range_str(ts: List[int]) -> str:
    """Compact representation of a list of integers: [1, 2, 3, 5] -> '1..3, 5'."""
    if not ts:
        return "∅"
    out = []
    run_start = ts[0]
    prev = ts[0]
    for t in ts[1:]:
        if t == prev + 1:
            prev = t
            continue
        out.append(f"{run_start}..{prev}" if run_start != prev else f"{run_start}")
        run_start = t
        prev = t
    out.append(f"{run_start}..{prev}" if run_start != prev else f"{run_start}")
    return "{" + ", ".join(out) + "}"
