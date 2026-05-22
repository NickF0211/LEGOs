import sys
from os.path import dirname, join
sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))

import idlelib.colorizer as ic
import idlelib.percolator as ip
import re
import tkinter as tk
from tkinter import simpledialog, messagebox
from sleecParser import check_input_red, check_input_conflict, check_input_concerns, check_input_purpose
from SleecNorm import check_situational_conflict
import tkinter.scrolledtext as scrolledtext

# Local module: trace sampler + realizability checker (bounded-weak).
import sleecRealizibilityCheck as _rlz


def read_model_file(file_path):
    with open(file_path, 'r') as file:
        return file.read()


def check_concern():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_concerns(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        new_text.insert(tk.INSERT, response)
    new_text.pack(expand=True, fill=tk.BOTH)


def check_situational():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_situational_conflict(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
        new_text.insert(tk.INSERT, '\n')
    else:
        new_text.insert(tk.INSERT, response)
    new_text.pack(expand=True, fill=tk.BOTH)


def check_redundancy():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_red(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.pack(expand=True, fill=tk.BOTH)


def check_conflict():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_conflict(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.pack(expand=True, fill=tk.BOTH)


def check_purpose():
    cur_text = aText.get("1.0", 'end-1c')
    result, response, hl = check_input_purpose(cur_text)
    new_text.delete('1.0', 'end-1c')
    if result:
        cur_index = 0
        sorted_hl = sorted(hl, key=lambda k: k[0], reverse=True)
        while sorted_hl:
            cur_start, cur_end = sorted_hl.pop()
            if cur_start >= cur_index:
                new_text.insert(tk.INSERT, response[cur_index: cur_start])
                new_text.insert(tk.INSERT, response[cur_start: cur_end], "hl")
                cur_index = cur_end
        if cur_index < len(response):
            new_text.insert(tk.INSERT, response[cur_index:])
    else:
        new_text.insert(tk.INSERT, response)
    new_text.pack(expand=True, fill=tk.BOTH)


def _format_partial_trace(trace):
    """Render a sampled partial trace dict into a human-readable block."""
    lines = []
    all_ms = (trace.get("bool_measures", []) +
              trace.get("num_measures", []) +
              trace.get("scalar_measures", []))
    lines.append(f"Environment events: {', '.join(trace['environment_events']) or '(none)'}")
    if all_ms:
        lines.append(f"Measures:           {', '.join(all_ms)}")
    lines.append(f"Rule firings:       {trace['num_rule_firings']} / "
                 f"{trace['num_soft_clauses']} soft clauses satisfied")
    lines.append("")
    for step in trace["per_step"]:
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
        lines.append(f"  t={t}: {events_str}{sep}{measures_str}")
    if trace.get("rules_fired"):
        lines.append("\nTriggered (rule, step):")
        for name, t in trace["rules_fired"]:
            lines.append(f"  - {name} @ t={t}")
    return "\n".join(lines)


def _range_str(ts):
    """Compact representation of a sorted int list: [1,2,3,5] -> '1..3, 5'."""
    if not ts:
        return "∅"
    out = []
    run_start = ts[0]
    prev = ts[0]
    for t in ts[1:]:
        if t == prev + 1:
            prev = t
            continue
        out.append(f"{run_start}..{prev}" if run_start != prev
                   else f"{run_start}")
        run_start = t
        prev = t
    out.append(f"{run_start}..{prev}" if run_start != prev
               else f"{run_start}")
    return ", ".join(out)


def _summarize_trace(trace):
    """Compact trace summary for the top-of-output view.

    If every step carries the same env events and the same measure
    valuations, collapse to a single 't=1..N: <events> | <measures>' line.
    Otherwise fall back to per-step listing.
    """
    per_step = trace.get("per_step", [])
    if not per_step:
        return "(empty trace)"
    # Canonical signature per step.
    sigs = []
    for step in per_step:
        ev = tuple(sorted(step.get("events", [])))
        ms = tuple(sorted(step.get("measures", {}).items()))
        sigs.append((ev, ms))
    uniform = all(s == sigs[0] for s in sigs)
    N = len(per_step)

    def _fmt_step(events, measures):
        ev_str = ", ".join(events) if events else "(no env event)"
        m_pairs = []
        for m, v in measures:
            if isinstance(v, bool):
                m_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                m_pairs.append(f"{m}={v}")
        m_str = ", ".join(m_pairs)
        sep = "  | " if m_str else ""
        return f"{ev_str}{sep}{m_str}"

    if uniform:
        ev, ms = sigs[0]
        # Split the events and measures onto their own lines so the
        # measure valuations are visible even when the env event list
        # is long.
        ev_str = ", ".join(ev) if ev else "(no env event)"
        m_pairs = []
        for m, v in ms:
            if isinstance(v, bool):
                m_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                m_pairs.append(f"{m}={v}")
        lines = [f"  t=1..{N}  (all steps identical)"]
        lines.append(f"    env events:  {ev_str}")
        if m_pairs:
            lines.append(f"    measures:    {', '.join(m_pairs)}")
        else:
            lines.append("    measures:    (none declared)")
        return "\n".join(lines)
    # Non-uniform: per-step.
    out = []
    for step in per_step:
        ev = sorted(step.get("events", []))
        ms = sorted(step.get("measures", {}).items())
        out.append(f"  t={step['t']}: {_fmt_step(ev, ms)}")
    return "\n".join(out)


def _summarize_firings(rules_fired):
    """Group 'rules_fired' list by rule and list time ranges.

    Input: [('r2', 1), ('r3', 1), ('r2', 2), ...]
    Output: ['r2 fires at t ∈ {1..5}', 'r3 fires at t ∈ {1..5}']
    """
    by_rule = {}
    for name, t in rules_fired:
        by_rule.setdefault(name, []).append(t)
    out = []
    for name in sorted(by_rule):
        times = sorted(set(by_rule[name]))
        out.append(f"  {name} fires at t ∈ {{{_range_str(times)}}}")
    return out


def check_realizability():
    """Prompt for horizon N, sample a partial trace, run the bounded-strong
    realizability check with per-component decomposition, and render the
    trace, the component structure, and the verdict in the output pane.

    Uses the same (response, hl) pattern as check_situational / check_conflict:
    the full response is built as a single string while tagged spans
    (start, end, tag) are recorded; at the end we render with
    insert(text, tag) in order.
    """
    cur_text = aText.get("1.0", 'end-1c')
    if not cur_text.strip():
        messagebox.showerror("Realizability check", "The editor is empty.")
        return

    N = simpledialog.askinteger(
        "Bounded realizability check",
        "Enter the horizon N (number of discrete steps, >= 1):",
        parent=lord, minvalue=1, initialvalue=5,
    )
    if N is None:
        return  # user cancelled

    new_text.delete('1.0', 'end-1c')
    new_text.pack(expand=True, fill=tk.BOTH)

    # ---- String-builder helpers. Each `span(text, tag=None)` appends to
    # the response and records the start/end offsets for that tag.
    parts = []          # list of (text, tag)  — tag is None for plain text
    def append(text, tag=None):
        parts.append((text, tag))
    def render():
        for text, tag in parts:
            if tag is None:
                new_text.insert(tk.INSERT, text)
            else:
                new_text.insert(tk.INSERT, text, tag)

    try:
        # Parse the current editor text.
        from sleecParser import parse_sleec
        model, *_ = parse_sleec(cur_text, read_file=False)

        # 0. Compute the rule dependency graph up front.
        from SleecNorm import parse_sleec_norm
        from sleec_decompose import decompose_rules
        _rlz._reset_sleecnorm_state()
        _m, _rules, _Am, _Acts, _og_rules, _c, _relations = \
            parse_sleec_norm(cur_text, read_file=False)
        components = decompose_rules(_rules, _og_rules, _relations)
        component_info = []
        for ci, comp in enumerate(components, start=1):
            names = sorted({
                getattr(_rules[i].og_rule, "name", f"<rule#{i}>")
                for i in comp
            })
            component_info.append((ci, names))

        # 1. Sample a partial trace.
        sampler = _rlz.AbstractTraceSampler(model, N=N, verbose=False)
        trace = sampler.next_trace()
        if trace is None:
            append(f"No partial trace can be sampled at N={N} "
                   "(measure invariants or relations exclude every "
                   "candidate).\n")
            render()
            return

        # 2. Run the realizability check.
        checker = _rlz.RealizabilityChecker(
            model, N=N, model_str=cur_text, decompose=True,
        )
        verdict = checker.check(trace, verbose=False)

        failing_names = set(verdict.culprit_rules) \
            if verdict.status == "unrealizable" else set()
        failing_component_idx = None
        for ci, names in component_info:
            if failing_names and failing_names.issubset(set(names)):
                failing_component_idx = ci
                break

        # Compute the trigger event classes of every culprit rule — used
        # to tint trigger-event occurrences wherever they appear in the
        # rendered output.
        culprit_triggers = set()
        if failing_names:
            for nr in _rules:
                nm = getattr(nr.og_rule, "name", None)
                if nm in failing_names:
                    te = nr.triggering_event
                    culprit_triggers.add(str(getattr(te, "expr", te)))

        # 3. Build the response — summary first, details below.
        #    Order: banner -> why (UNREAL only) -> trace summary ->
        #    --- Details --- -> timeline -> decomposition -> full firings.

        # 3a. Verdict banner (top of output).
        header_bar = "=" * 72 + "\n"
        if verdict.status == "realizable":
            append(header_bar)
            append(f"  REALIZABLE  (N={N})\n")
            append(header_bar)
            append("\nEvery sampled partial trace admits an extension that "
                   "satisfies all SLEEC rules within their time bounds.\n")
            append(f"\nComponents checked: {len(component_info)}  "
                   f"({', '.join(f'G{ci}' for ci, _ in component_info)})\n")
        else:
            banner = "!" * 72 + "\n"
            append(banner, "hl")
            append(f"  UNREALIZABLE  (N={N})\n", "hl")
            append(banner, "hl")
            append("\n")

            # 3b. "Why" paragraph + inline culprit rule sources.
            # _append_culprit_source_block renders the header, clash-head
            # summary line, and each rule's source with tagged sub-spans.
            _append_culprit_source_block(
                append, cur_text, _rules, failing_names
            )
            # Cite the failing component.
            if failing_component_idx is not None:
                append("\nFailing rules: {")
                for i, name in enumerate(sorted(failing_names)):
                    if i:
                        append(", ")
                    append(name, "culprit_rule")
                append(f"}}  (component G{failing_component_idx} of "
                       f"{len(component_info)})\n")

        # 3c. Compact partial-trace summary (single section, not repeated).
        append("\n── Partial trace that "
               + ("triggered the clash" if verdict.status == "unrealizable"
                  else "was analyzed")
               + f" (N={N}) ──\n")
        compact = _summarize_trace(trace)
        # Tag culprit trigger events in the compact summary.
        _append_with_two_tag_highlights(
            append, compact,
            rule_names=set(),
            event_names=culprit_triggers,
        )
        append("\n")

        # 3d. Fired rules summary (grouped by rule).
        fires = trace.get("rules_fired") or []
        if fires:
            append("\nRules fired on this trace:\n")
            grouped = _summarize_firings(fires)
            for line in grouped:
                # Tag rule names in each line if culprit.
                _append_with_two_tag_highlights(
                    append, line + "\n",
                    rule_names=failing_names,
                    event_names=set(),
                )

        # 3e. Details section (below the fold).
        append("\n" + "─" * 72 + "\n")
        append("── Details  (timeline, decomposition, full firings) ──\n")
        append("─" * 72 + "\n")

        # 3e-i. Obligation timeline.
        try:
            from sleec_timeline import build_timeline
            tl_text, tl_spans = build_timeline(
                _rules, trace, failing_names, col_width=8,
            )
            _append_with_spans(append, tl_text, tl_spans)
        except Exception as _e:
            append(f"\n[timeline render skipped: {_e}]\n")

        # 3e-ii. Decomposition breakdown.
        append("\n\n-- Rule decomposition --\n")
        append(f"Spec decomposes into {len(component_info)} component(s):\n")
        for ci, names in component_info:
            marker = "  <-- failing" if ci == failing_component_idx else ""
            append(f"  G{ci} ({len(names)} rule"
                   f"{'s' if len(names) != 1 else ''}): {{")
            for i, name in enumerate(names):
                if i:
                    append(", ")
                if name in failing_names:
                    append(name, "culprit_rule")
                else:
                    append(name)
            append("}" + marker + "\n")

        # 3e-iii. Full triggered-rule list (step-by-step).
        if fires:
            append("\n-- Full firing list --\n")
            for name, t in fires:
                line = f"  - {name} @ t={t}\n"
                _append_with_two_tag_highlights(
                    append, line,
                    rule_names=failing_names,
                    event_names=set(),
                )

        render()

    except Exception as exc:
        # Friendly handling for the two known "expected" diagnostic exceptions:
        # show only the message body, no traceback.
        cls_name = type(exc).__name__
        if cls_name == "EventClassificationError":
            from sleec_event_classification import format_conflicts
            new_text.insert(
                tk.INSERT,
                "Event-classification conflict — the realizability check "
                "cannot proceed.\n\n",
                "hl",
            )
            new_text.insert(
                tk.INSERT,
                format_conflicts(exc.classification) + "\n\n"
                "Adjust the affected `event NAME as system|environment` "
                "annotations or rule body, then retry.\n",
            )
            return
        if cls_name == "RelationClassificationError":
            new_text.insert(
                tk.INSERT,
                "Unsupported relation kind — the realizability check "
                "cannot proceed.\n\n",
                "hl",
            )
            new_text.insert(tk.INSERT, str(exc) + "\n\n"
                "Relations that couple system events with measure "
                "expressions are not yet supported by the realizability "
                "check. Either remove the relation or restrict the event "
                "to environment.\n")
            return
        # Unexpected exception — show the traceback for debugging.
        import traceback
        tb = traceback.format_exc()
        new_text.insert(
            tk.INSERT,
            f"ERROR while running realizability check:\n{exc}\n\n{tb}",
        )


def _append_culprit_source_block(append, model_str, rules, failing_names):
    """Mirror check_situational_conflict's output pattern: embed the source
    text of every culprit rule verbatim, then tag sub-spans (trigger and
    response) so the user sees exactly which part of which rule is at
    fault. Additionally, any event-class name appearing as a head of
    culprit rules with BOTH positive and negative polarity is tagged with
    the 'conflict' tag inside the rendered rule text — i.e. the user sees
    the clashing head highlighted in bright red in each rule where it
    appears.

    Parameters
    ----------
    append : callable(text, tag=None)
        Chunk appender provided by the main render loop.
    model_str : str
        The original editor source. Used to slice out rule bodies verbatim.
    rules : list[NormalizedRule]
        All normalized rules (from parse_sleec_norm).
    failing_names : set[str]
        Names of rules in the failing dependency-graph component.
    """
    if not failing_names:
        return

    # Deduplicate AST rule nodes, preserving spec order.
    seen_nodes = []
    seen_ids = set()
    for nr in rules:
        name = getattr(nr.og_rule, "name", None)
        if name not in failing_names:
            continue
        if id(nr.og_rule) in seen_ids:
            continue
        seen_ids.add(id(nr.og_rule))
        seen_nodes.append(nr.og_rule)

    # Compute the set of head classes that appear with BOTH polarities
    # across the culprit rules — these are the "clashing" heads.
    pos_heads, neg_heads = set(), set()
    for nr in rules:
        if getattr(nr.og_rule, "name", None) not in failing_names:
            continue
        for cobg in nr.oc.obligations:
            h = getattr(cobg.obligation, "head", None)
            if h is None:
                continue
            cls = str(getattr(h, "expr", h))
            if bool(getattr(h, "neg", False)):
                neg_heads.add(cls)
            else:
                pos_heads.add(cls)
    clash_heads = pos_heads & neg_heads

    append("\n-- Culprit rules (source form) --\n")
    if clash_heads:
        append("Head event(s) with both required and forbidden obligations: ")
        for i, h in enumerate(sorted(clash_heads)):
            if i:
                append(", ")
            append(h, "conflict")
        append("\n\n")

    for rule_node in seen_nodes:
        s = rule_node._tx_position
        e = rule_node._tx_position_end
        rule_src = model_str[s:e]

        # Find sub-positions for trigger and response relative to the rule.
        def sub_span(node):
            if node is None:
                return None
            return (node._tx_position - s, node._tx_position_end - s)

        trig_span = sub_span(getattr(rule_node, "trigger", None))
        cond_span = sub_span(getattr(rule_node, "condition", None))
        resp_span = sub_span(getattr(rule_node, "response", None))

        # Emit the rule text with sub-span highlights:
        # - Trigger  -> 'trigger_event' (pale yellow)
        # - Condition -> 'trigger_event' (same; the condition involves the
        #    same environment observation as the trigger)
        # - Response -> 'culprit_rule' (bold red), except occurrences of a
        #    clash_head word inside the response, which are tagged
        #    'conflict' (bright red).
        import re
        chunks = []  # list of (rel_start, rel_end, tag) relative to rule_src

        if trig_span:
            chunks.append((trig_span[0], trig_span[1], "trigger_event"))
        if cond_span:
            chunks.append((cond_span[0], cond_span[1], "trigger_event"))
        if resp_span:
            # Default: whole response as culprit_rule.
            rs, re_ = resp_span
            # Inside the response, locate each occurrence of a clash_head word.
            if clash_heads:
                pattern = r"\b(" + "|".join(
                    re.escape(h) for h in sorted(clash_heads, key=len, reverse=True)
                ) + r")\b"
                last = rs
                for m in re.finditer(pattern, rule_src[rs:re_]):
                    ms = rs + m.start()
                    me = rs + m.end()
                    if ms > last:
                        chunks.append((last, ms, "culprit_rule"))
                    chunks.append((ms, me, "conflict"))
                    last = me
                if last < re_:
                    chunks.append((last, re_, "culprit_rule"))
            else:
                chunks.append((rs, re_, "culprit_rule"))

        # Sort and merge; tolerate overlap by preferring later chunks (conflict wins).
        chunks = sorted(chunks, key=lambda c: (c[0], c[1]))

        # Emit rule banner + rule source with spans.
        rule_name = getattr(rule_node, "name", "?")
        append("  ")
        append(rule_name, "culprit_rule")
        append(":\n")
        append("    ")
        # Indent every embedded newline to keep the block readable.
        indented_src = rule_src.replace("\n", "\n    ")
        # Translate chunks to offsets in the indented string. Since our
        # chunks all refer to the non-indented rule_src and we prepend "    "
        # only once plus replace "\n" with "\n    ", we need a map. Keep
        # it simple: if the rule source has no newlines, chunks stay the
        # same. SLEEC rules are usually single-line; handle that common
        # case explicitly.
        if "\n" not in rule_src:
            _emit_tagged_substring(append, indented_src, chunks)
        else:
            # Fall back to untagged when the rule spans multiple lines;
            # we still preserve the indentation.
            append(indented_src)
        append("\n\n")


def _emit_tagged_substring(append, text, chunks):
    """Write `text` through `append`, tagging the substrings given by
    chunks = [(start, end, tag), ...] in order. Chunks must be disjoint
    and sorted by start."""
    cursor = 0
    for (s, e, tag) in chunks:
        if s < cursor:
            # Overlap — skip defensively.
            continue
        if s > cursor:
            append(text[cursor:s])
        append(text[s:e], tag)
        cursor = e
    if cursor < len(text):
        append(text[cursor:])


def _append_with_spans(append, text, spans):
    """Insert `text` via `append`, but chunked according to (start, end, tag)
    spans (each tag is applied to the substring text[start:end]).
    Spans may be unordered; they must not overlap."""
    if not spans:
        append(text)
        return
    # Sort spans by start.
    spans = sorted(spans, key=lambda s: s[0])
    cursor = 0
    for start, end, tag in spans:
        if start < cursor:
            # Overlap — skip defensively; mark remaining as plain.
            continue
        if start > cursor:
            append(text[cursor:start])
        append(text[start:end], tag)
        cursor = end
    if cursor < len(text):
        append(text[cursor:])


def _append_with_highlights(append, text, names, tag):
    """Append `text` to the builder, tagging every whole-word occurrence
    of any name in `names` with `tag`. Zero highlights if `names` is empty.
    """
    import re
    if not names:
        append(text)
        return
    # Build a single alternation regex; use word boundaries to match whole
    # identifiers only.
    pattern = r"\b(" + "|".join(re.escape(n) for n in sorted(names)) + r")\b"
    cursor = 0
    for m in re.finditer(pattern, text):
        if m.start() > cursor:
            append(text[cursor:m.start()])
        append(m.group(0), tag)
        cursor = m.end()
    if cursor < len(text):
        append(text[cursor:])


def _append_with_two_tag_highlights(append, text, rule_names, event_names):
    """Tag rule-name occurrences with 'culprit_rule' and event-name
    occurrences with 'trigger_event', in a single left-to-right pass.
    Names are matched as whole words via \\b ... \\b.
    """
    import re
    patterns = []
    tagmap = {}
    for n in sorted(rule_names or ()):
        patterns.append((n, "culprit_rule"))
        tagmap[n] = "culprit_rule"
    for n in sorted(event_names or ()):
        # Event names win over rule-name matches only if both collide —
        # shouldn't happen, but be deterministic about it.
        if n not in tagmap:
            patterns.append((n, "trigger_event"))
            tagmap[n] = "trigger_event"
    if not patterns:
        append(text)
        return
    alt = "|".join(re.escape(n) for n, _ in patterns)
    pat = re.compile(r"\b(" + alt + r")\b")
    cursor = 0
    for m in pat.finditer(text):
        if m.start() > cursor:
            append(text[cursor:m.start()])
        append(m.group(0), tagmap[m.group(0)])
        cursor = m.end()
    if cursor < len(text):
        append(text[cursor:])



sample_text = read_model_file("test.sleec")

# sample_text = "First line of text \nSecond line of text \nThird line of text"

lord = tk.Tk()
lord.title("SLEEC-D")

KEYWORD = r"\b(?P<KEYWORD>event|measure|constant|when|then|within|minutes|hours|seconds|unless|otherwise|boolean|numeric|scale|not|and|or|def_start|def_end|rule_end|rule_start|concern_start|concern_end|purpose_start|purpose_end|True|False|def_start|def_end|eventually|else|exists|while|meanwhile|invariant|witness|coincide|conflict|happenBefore|relation_start|relation_end|negate|imply|iff|negate|causation|effect|until|for|includes|forbid|mutualExclusive)\b"

# KEYWORD   = r"\b(?P<KEYWORD>False|None|True|and|as|assert|async|await|break|class|continue|def|del|elif|else|except|finally|for|from|global|if|import|in|is|lambda|nonlocal|not|or|pass|raise|return|try|while|with|yield)\b"
EXCEPTION = r"([^.'\"\\#]\b|^)(?P<EXCEPTION>ArithmeticError|AssertionError|AttributeError|BaseException|BlockingIOError|BrokenPipeError|BufferError|BytesWarning|ChildProcessError|ConnectionAbortedError|ConnectionError|ConnectionRefusedError|ConnectionResetError|DeprecationWarning|EOFError|Ellipsis|EnvironmentError|Exception|FileExistsError|FileNotFoundError|FloatingPointError|FutureWarning|GeneratorExit|IOError|ImportError|ImportWarning|IndentationError|IndexError|InterruptedError|IsADirectoryError|KeyError|KeyboardInterrupt|LookupError|MemoryError|ModuleNotFoundError|NameError|NotADirectoryError|NotImplemented|NotImplementedError|OSError|OverflowError|PendingDeprecationWarning|PermissionError|ProcessLookupError|RecursionError|ReferenceError|ResourceWarning|RuntimeError|RuntimeWarning|StopAsyncIteration|StopIteration|SyntaxError|SyntaxWarning|SystemError|SystemExit|TabError|TimeoutError|TypeError|UnboundLocalError|UnicodeDecodeError|UnicodeEncodeError|UnicodeError|UnicodeTranslateError|UnicodeWarning|UserWarning|ValueError|Warning|WindowsError|ZeroDivisionError)\b"
BUILTIN = r"([^.'\"\\#]\b|^)(?P<BUILTIN>abs|all|any|ascii|bin|breakpoint|callable|chr|classmethod|compile|complex|copyright|credits|delattr|dir|divmod|enumerate|eval|exec|exit|filter|format|frozenset|getattr|globals|hasattr|hash|help|hex|id|input|isinstance|issubclass|iter|len|license|locals|map|max|memoryview|min|next|oct|open|ord|pow|print|quit|range|repr|reversed|round|set|setattr|slice|sorted|staticmethod|sum|type|vars|zip)\b"
DOCSTRING = r"(?P<DOCSTRING>(?i:r|u|f|fr|rf|b|br|rb)?'''[^'\\]*((\\.|'(?!''))[^'\\]*)*(''')?|(?i:r|u|f|fr|rf|b|br|rb)?\"\"\"[^\"\\]*((\\.|\"(?!\"\"))[^\"\\]*)*(\"\"\")?)"
STRING = r"(?P<STRING>(?i:r|u|f|fr|rf|b|br|rb)?'[^'\\\n]*(\\.[^'\\\n]*)*'?|(?i:r|u|f|fr|rf|b|br|rb)?\"[^\"\\\n]*(\\.[^\"\\\n]*)*\"?)"
TYPES = r"\b(?P<TYPES>bool|bytearray|bytes|dict|float|int|list|str|tuple|object)\b"
NUMBER = r"\b(?P<NUMBER>((0x|0b|0o|#)[\da-fA-F]+)|((\d*\.)?\d+))\b"
CLASSDEF = r"(?<=\bclass)[ \t]+(?P<CLASSDEF>\w+)[ \t]*[:\(]"  # recolor of DEFINITION for class definitions
DECORATOR = r"(^[ \t]*(?P<DECORATOR>@[\w\d\.]+))"
INSTANCE = r"\b(?P<INSTANCE>super|self|cls)\b"
COMMENT = r"(?P<COMMENT>//[^\n]*)"
SYNC = r"(?P<SYNC>\n)"

PROG = rf"{KEYWORD}|{BUILTIN}|{EXCEPTION}|{TYPES}|{COMMENT}|{DOCSTRING}|{STRING}|{SYNC}|{INSTANCE}|{DECORATOR}|{NUMBER}|{CLASSDEF}"
IDPROG = r"(?<!class)\s+(\w+)"

TAGDEFS = {
    'COMMENT': {'foreground': "#013220", 'background': None, 'font': "Helvetica 14 bold"},
    # 'TYPES'      : {'foreground': CLOUD2    , 'background': None},
    'NUMBER': {'foreground': "#ffa500", 'font': "Helvetica 14 bold"},
    # 'BUILTIN'    : {'foreground': OVERCAST  , 'background': None},
    # 'STRING'     : {'foreground': PUMPKIN   , 'background': None},
    # 'DOCSTRING'  : {'foreground': STORMY    , 'background': None},
    # 'EXCEPTION'  : {'foreground': CLOUD2    , 'background': None, 'font':FONTBOLD},
    # 'DEFINITION' : {'foreground': SAILOR    , 'background': None, 'font':FONTBOLD},
    # 'DECORATOR'  : {'foreground': CLOUD2    , 'background': None, 'font':FONTITAL},
    # 'INSTANCE'   : {'foreground': CLOUD     , 'background': None, 'font':FONTITAL},
    'KEYWORD': {'foreground': '#8e44ad', 'font': "Helvetica 14 bold"},
    # 'CLASSDEF'   : {'foreground': PURPLE    , 'background': None, 'font':FONTBOLD},
}

cd = ic.ColorDelegator()
cd.prog = re.compile(PROG, re.S | re.M)
cd.idprog = re.compile(IDPROG, re.S)
cd.tagdefs = {**cd.tagdefs, **TAGDEFS}

cd1 = ic.ColorDelegator()
cd1.prog = re.compile(PROG, re.S | re.M)
cd1.idprog = re.compile(IDPROG, re.S)
cd1.tagdefs = {**cd.tagdefs, **TAGDEFS}

# width = lord.winfo_screenwidth()
# height = lord.winfo_screenheight()
# lord_width = width // 3 * 2
# lord_height = height
# lord.geometry('%sx%s' % (lord_width, lord_height))

scrollbar = tk.Scrollbar(lord)

aText = scrolledtext.ScrolledText(font=("Georgia", "14"))
aText.pack(expand=True, fill=tk.BOTH)
aText.insert(tk.INSERT, sample_text)
ip.Percolator(aText).insertfilter(cd)

new_text = scrolledtext.ScrolledText(font=("Georgia", "14"))
new_text.tag_config("hl", background="yellow")
# Realizability-specific tags. `culprit_rule` marks rule names inside the
# failing dependency-graph component; `trigger_event` marks env event and
# measure names tied to those culprit rules.
new_text.tag_config("culprit_rule", background="#ffb3b3",
                    font=("Georgia", 14, "bold"))
new_text.tag_config("trigger_event", background="#fff4a3")
# Cells in the obligation timeline where a positive and a negative
# obligation collide — the visual root cause of unrealizability.
new_text.tag_config("conflict", background="#ff4d4d", foreground="white",
                    font=("Georgia", 14, "bold"))
# new_text.pack(expand=True, fill=tk.BOTH)
ip.Percolator(new_text).insertfilter(cd1)

aButton = tk.Button(lord, text="check redundancy", command=check_redundancy)
aButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

bButton = tk.Button(lord, text="check conflicts", command=check_conflict)
bButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

bButton = tk.Button(lord, text="check concern", command=check_concern)
bButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

bButton = tk.Button(lord, text="check purpose", command=check_purpose)
bButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

bButton = tk.Button(lord, text="check situational conflict", command=check_situational)
bButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

rlzButton = tk.Button(lord, text="check realizability (bounded strong)",
                      command=check_realizability)
rlzButton.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

aText.tag_config("bt", background="yellow")
lord.mainloop()
