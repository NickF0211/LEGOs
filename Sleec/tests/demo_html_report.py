"""Generate an HTML report demonstrating the SLEEC bounded realizability
checker on a curated set of example specs.

Output: /tmp/sleec_realizability_report.html (self-contained, no JS).

For each spec the report shows:
  - the spec source
  - the realizability verdict
  - the sampled adversarial partial trace
  - the rule-firing pattern
  - the dependency-graph decomposition
  - on UNREAL, the culprit rules in source form with the clashing head
    highlighted

Designed to be openable in any browser without external dependencies.
"""

import html
import os
import re
import sys
import time
from typing import List, Optional, Tuple

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)


# ---------------- Specs to demo ----------------

SPECS = [
    {
        "label": "demo.sleec — paper's motivating example",
        "path": os.path.join(SLEEC, "demo.sleec"),
        "N": 5,
        "decompose": True,
        "note": "The R1/R2/R3 cascade: emergencyArrived triggers R3 which "
                "produces callEmergencyServices, which triggers R1 demanding "
                "leaveRoom; meanwhile R2 forbids leaveRoom whenever userDeaf=T. "
                "Strong bounded realizability detects the head clash.",
    },
    {
        "label": "test.sleec — patient-fallen scenario",
        "path": os.path.join(SLEEC, "test.sleec"),
        "N": 5,
        "decompose": True,
        "note": "Three-rule cluster around CallSupport / ProvideCompanionship; "
                "PatientFallen triggers contradictory obligations.",
    },
    {
        "label": "annotated/demo.sleec — same spec with explicit annotations",
        "path": os.path.join(SLEEC, "experiments/annotated/demo.sleec"),
        "N": 5,
        "decompose": True,
        "note": "Demonstrates the new `event NAME as system|environment` "
                "syntax. Same verdict as demo.sleec.",
    },
    {
        "label": "realistic_alarm.sleec — home alarm with 4 relations",
        "path": os.path.join(SLEEC, "experiments/relation_specs/realistic_alarm.sleec"),
        "N": 5,
        "decompose": True,
        "note": "Multi-component spec with mutEx, happenBefore, causation, "
                "forbid relations. The sampler respects them: Disarm is "
                "absent (mutex), RecoverFromBreach is delayed (happenBefore).",
    },
    {
        "label": "realistic_unreal.sleec — env relations + sys head clash",
        "path": os.path.join(SLEEC, "experiments/relation_specs/realistic_unreal.sleec"),
        "N": 4,
        "decompose": True,
        "note": "witness Wake Sense forces co-occurrence; mutex Sense Sleep "
                "keeps Sleep absent. Phase II then detects R1 (Wake → "
                "GoActive) clashing with R2 (Sense → ¬GoActive).",
    },
    {
        "label": "edge_chain_happenBefore.sleec — chained ordering",
        "path": os.path.join(SLEEC, "experiments/relation_specs/edge_chain_happenBefore.sleec"),
        "N": 4,
        "decompose": True,
        "note": "happenBefore A B AND happenBefore B C creates a cascade: "
                "B can only fire after A, C only after B. Sampler "
                "produces the staircase trace.",
    },
    {
        "label": "all_kinds_combined.sleec — 7 relations of every encodable kind",
        "path": os.path.join(SLEEC, "experiments/relation_specs/all_kinds_combined.sleec"),
        "N": 4,
        "decompose": True,
        "note": "Stress test: witness, mutEx, happenBefore, causation, "
                "includes, forbid, UntilEM all in one spec.",
    },
]


# ---------------- Driver ----------------

def run_one(spec):
    """Run sampler + checker on one spec; return a dict of results."""
    import sleecRealizibilityCheck as srlc
    from sleecParser import parse_sleec, read_model_file
    from sleec_event_classification import (
        classify_events_with_annotations, format_classification,
    )

    path = spec["path"]
    N = spec["N"]
    decompose = spec["decompose"]
    out = {"spec": spec, "ok": False}
    try:
        srlc._reset_sleecnorm_state()
        model_str = read_model_file(path)
        model, *_ = parse_sleec(path, read_file=True)
    except Exception as e:
        out["error"] = f"parse failed: {e}"
        return out
    try:
        ec = classify_events_with_annotations(model)
        out["classification"] = format_classification(ec)
        if ec.has_errors:
            out["error"] = "event-classification conflict (run aborted)"
            return out
    except Exception as e:
        out["error"] = f"classification failed: {e}"
        return out

    t0 = time.time()
    try:
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
        trace = sampler.next_trace()
    except Exception as e:
        out["error"] = f"sampler failed: {e}"
        return out
    if trace is None:
        out["error"] = "sampler returned no trace"
        return out

    out["trace"] = trace
    try:
        checker = srlc.RealizabilityChecker(
            model, N=N, model_str=model_str, mode="strong", decompose=decompose,
        )
        verdict = checker.check(trace)
    except Exception as e:
        out["error"] = f"checker failed: {e}"
        return out
    out["verdict"] = verdict
    out["seconds"] = time.time() - t0
    out["model_str"] = model_str
    out["model"] = model
    out["ok"] = True
    return out


# ---------------- HTML rendering ----------------

CSS = """
body { font-family: -apple-system, "SF Pro Text", "Helvetica Neue", Arial, sans-serif;
       max-width: 1100px; margin: 24px auto; padding: 0 16px;
       color: #222; line-height: 1.4; }
h1 { font-size: 28px; margin-bottom: 0.2em; }
h1 .sub { font-size: 14px; color: #666; font-weight: normal; }
h2 { font-size: 20px; margin-top: 36px; padding-bottom: 6px;
     border-bottom: 1px solid #ddd; }
h3 { font-size: 15px; margin-top: 18px; color: #333; }
table.summary { border-collapse: collapse; margin: 16px 0; font-size: 14px; }
table.summary th, table.summary td { padding: 6px 10px; border: 1px solid #ddd;
                                      text-align: left; }
table.summary th { background: #f4f4f4; }
.pill { display: inline-block; padding: 2px 10px; border-radius: 10px;
        font-size: 12px; font-weight: 600; }
.pill.real { background: #d4edda; color: #155724; }
.pill.unreal { background: #f8d7da; color: #721c24; }
.pill.error { background: #fff3cd; color: #856404; }
pre { background: #f9f9f9; padding: 10px 12px; border: 1px solid #e0e0e0;
      border-radius: 4px; font-size: 12px; overflow-x: auto;
      white-space: pre; line-height: 1.35; }
.spec-source pre { background: #fff8dc; }
.trace pre { background: #f0f4ff; }
.timeline pre { background: #f0f8f0; }
.note { font-style: italic; color: #555; margin: 8px 0 12px 0; }
.metadata { font-size: 13px; color: #444; margin: 4px 0; }
.hl-trigger { background: #fff4a3; padding: 0 2px; border-radius: 2px; }
.hl-culprit { background: #ffb3b3; padding: 0 2px; border-radius: 2px;
              font-weight: 600; }
.hl-conflict { background: #ff4d4d; color: #fff; padding: 0 4px;
               border-radius: 2px; font-weight: 600; }
.section { margin: 12px 0; }
.toc { background: #f4f4f4; padding: 12px 18px; border-radius: 4px;
       margin: 12px 0 24px 0; }
.toc a { text-decoration: none; color: #06c; }
.toc a:hover { text-decoration: underline; }
"""


def esc(s):
    return html.escape(str(s))


def render_pill(verdict):
    cls = {"realizable": "real", "unrealizable": "unreal"}.get(
        verdict, "error")
    label = {"realizable": "REALIZABLE",
             "unrealizable": "UNREALIZABLE"}.get(verdict, verdict.upper())
    return f'<span class="pill {cls}">{esc(label)}</span>'


def highlight_event_names_in_source(src, kinds):
    """Wrap each event name in a span with the appropriate class.
    `kinds` is a dict event_name -> 'system' / 'environment' (from ec).
    We tint sys events as culprit-red, env events as trigger-yellow.
    """
    # Sort by descending name length to avoid partial-name shadowing.
    if not kinds:
        return esc(src)
    names = sorted(kinds.keys(), key=len, reverse=True)
    out = esc(src)
    for n in names:
        cls = "hl-culprit" if kinds[n] == "system" else "hl-trigger"
        # whole-word replace, keep escape on the inserted markup
        pattern = re.compile(rf"\b{re.escape(esc(n))}\b")
        out = pattern.sub(
            f'<span class="{cls}">{esc(n)}</span>',
            out,
        )
    return out


def trace_summary(trace):
    """Compact rendering of a trace dict."""
    per_step = trace["per_step"]
    if not per_step:
        return "(empty trace)"
    sigs = []
    for s in per_step:
        ev = tuple(sorted(s.get("events", [])))
        ms = tuple(sorted(s.get("measures", {}).items()))
        sigs.append((ev, ms))
    uniform = all(s == sigs[0] for s in sigs)
    if uniform:
        ev, ms = sigs[0]
        ev_str = ", ".join(ev) if ev else "(no env event)"
        m_pairs = []
        for m, v in ms:
            if isinstance(v, bool):
                m_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                m_pairs.append(f"{m}={v}")
        m_str = ", ".join(m_pairs) if m_pairs else "(none)"
        return f"  t=1..{trace['N']} (all steps identical)\n" \
               f"    env events:  {ev_str}\n" \
               f"    measures:    {m_str}"
    out = []
    for s in per_step:
        ev = sorted(s.get("events", []))
        ms = sorted(s.get("measures", {}).items())
        ev_str = ", ".join(ev) if ev else "(no env event)"
        m_pairs = []
        for m, v in ms:
            if isinstance(v, bool):
                m_pairs.append(f"{m}={'T' if v else 'F'}")
            else:
                m_pairs.append(f"{m}={v}")
        sep = "  | " if m_pairs else ""
        out.append(f"  t={s['t']}: {ev_str}{sep}{', '.join(m_pairs)}")
    return "\n".join(out)


def firings_summary(trace):
    fires = trace.get("rules_fired") or []
    by_rule = {}
    for name, t in fires:
        by_rule.setdefault(name, []).append(t)
    out = []
    for name in sorted(by_rule):
        ts = sorted(set(by_rule[name]))
        # compact range
        if not ts:
            continue
        ranges = []
        cur_start = ts[0]
        prev = ts[0]
        for x in ts[1:]:
            if x == prev + 1:
                prev = x
                continue
            ranges.append(f"{cur_start}..{prev}" if cur_start != prev
                          else f"{cur_start}")
            cur_start = x; prev = x
        ranges.append(f"{cur_start}..{prev}" if cur_start != prev
                      else f"{cur_start}")
        out.append(f"  {name} fires at t ∈ {{{', '.join(ranges)}}}")
    if not out:
        out.append("  (no env-triggered rules fired)")
    return "\n".join(out)


def render_one(result, anchor_id):
    spec = result["spec"]
    label = spec["label"]
    note = spec["note"]
    out = []
    out.append(f'<h2 id="{anchor_id}">{esc(label)}</h2>')
    out.append(f'<div class="metadata">'
               f'<b>file:</b> <code>{esc(spec["path"].replace(SLEEC + "/", ""))}</code> '
               f'&nbsp;&middot;&nbsp; <b>horizon:</b> N={spec["N"]} '
               f'&nbsp;&middot;&nbsp; <b>mode:</b> strong '
               f'&nbsp;&middot;&nbsp; <b>decompose:</b> {spec["decompose"]}'
               f'</div>')
    out.append(f'<div class="note">{esc(note)}</div>')

    if not result["ok"]:
        out.append(f'<div class="metadata"><b>verdict:</b> '
                   f'{render_pill("error")} {esc(result.get("error", ""))}</div>')
        return "\n".join(out)

    verdict = result["verdict"]
    out.append(f'<div class="metadata"><b>verdict:</b> '
               f'{render_pill(verdict.status)}'
               f'&nbsp;&middot;&nbsp; <b>wall-clock:</b> {result["seconds"]:.2f}s</div>')

    # Spec source with event-name highlighting.
    from sleec_event_classification import (
        classify_events_with_annotations, Kind,
    )
    ec = classify_events_with_annotations(result["model"])
    kinds = {n: ec.kind[n].value for n in ec.kind}
    src_html = highlight_event_names_in_source(result["model_str"], kinds)
    out.append('<div class="section spec-source">'
               '<h3>Spec source <small style="font-weight:normal;color:#888">'
               '(env events <span class="hl-trigger">yellow</span>, '
               'sys events <span class="hl-culprit">red</span>)</small></h3>'
               f'<pre>{src_html}</pre></div>')

    # Trace.
    out.append('<div class="section trace">'
               '<h3>Sampled adversarial partial trace</h3>'
               f'<pre>{esc(trace_summary(result["trace"]))}</pre></div>')

    # Firings.
    out.append('<div class="section">'
               '<h3>Rules fired on this trace</h3>'
               f'<pre>{esc(firings_summary(result["trace"]))}</pre></div>')

    # Decomposition + culprits.
    if verdict.status == "unrealizable":
        culprits = ", ".join(verdict.culprit_rules) or "(none reported)"
        out.append('<div class="section">'
                   f'<h3>Failing component (UNREAL)</h3>'
                   f'<pre>Culprit rules: <span class="hl-culprit">{esc(culprits)}</span>\n'
                   f'(Run with --decompose to localize: only this component\n'
                   f'needs to change to make the spec realizable.)</pre></div>')
    else:
        out.append('<div class="section">'
                   '<h3>Realizability holds</h3>'
                   f'<pre>Every sampled adversarial partial trace at horizon\n'
                   f'N={spec["N"]} admits a system extension that satisfies\n'
                   f'every triggered SLEEC rule.</pre></div>')

    return "\n".join(out)


def slugify(s):
    return re.sub(r"[^a-z0-9]+", "-", s.lower()).strip("-")[:60]


def render_report(results):
    """Top-level HTML."""
    body = []
    # TOC
    toc = []
    for i, r in enumerate(results):
        anchor = f"spec-{i}-" + slugify(r["spec"]["label"])
        r["_anchor"] = anchor
        toc.append(f'<li><a href="#{anchor}">{esc(r["spec"]["label"])}</a> '
                   f'{render_pill(r["verdict"].status if r["ok"] else "error")}</li>')
    body.append('<div class="toc"><b>Contents</b><ul>'
                + "\n".join(toc) + "</ul></div>")
    # Summary table
    body.append('<table class="summary">')
    body.append('<tr><th>Spec</th><th>N</th><th>Verdict</th><th>Time</th>'
                '<th>Components</th><th>Rules fired</th></tr>')
    for r in results:
        spec = r["spec"]
        if r["ok"]:
            v = r["verdict"]
            comp_count = "n/a"
            try:
                from sleec_event_classification import classify_events_with_annotations
                from sleec_decompose import decompose_with_relations
                from SleecNorm import parse_sleec_norm
                import sleecRealizibilityCheck as srlc
                srlc._reset_sleecnorm_state()
                _m, rules_, _A, _Acts, og_rules_, _c, relations_ = \
                    parse_sleec_norm(r["model_str"], read_file=False)
                ec = classify_events_with_annotations(_m)
                d = decompose_with_relations(rules_, og_rules_, relations_, ec)
                comp_count = str(len(d.components))
            except Exception:
                pass
            body.append(
                f'<tr><td><a href="#{r["_anchor"]}">{esc(spec["label"])}</a></td>'
                f'<td>{spec["N"]}</td>'
                f'<td>{render_pill(v.status)}</td>'
                f'<td>{r["seconds"]:.2f}s</td>'
                f'<td>{comp_count}</td>'
                f'<td>{len(r["trace"]["rules_fired"])}</td></tr>'
            )
        else:
            body.append(
                f'<tr><td>{esc(spec["label"])}</td>'
                f'<td>{spec["N"]}</td>'
                f'<td>{render_pill("error")}</td>'
                f'<td>—</td><td>—</td><td>—</td></tr>'
            )
    body.append('</table>')

    # Per-spec sections
    for r in results:
        body.append(render_one(r, r["_anchor"]))

    timestamp = time.strftime("%Y-%m-%d %H:%M %Z", time.localtime())
    head = (
        f"<h1>SLEEC bounded realizability — demo report"
        f"<br><span class='sub'>Generated {esc(timestamp)} · "
        f"strong semantics, decomposition on, "
        f"AbstractTraceSampler</span></h1>"
    )

    return f"""<!doctype html>
<html><head><meta charset="utf-8">
<title>SLEEC realizability demo</title>
<style>{CSS}</style></head>
<body>
{head}
{''.join(body)}
</body></html>
"""


# ---------------- Main ----------------

def main():
    print("Running realizability checks ...", file=sys.stderr)
    results = []
    for spec in SPECS:
        print(f"  - {spec['label']} ...", file=sys.stderr, end=" ", flush=True)
        if not os.path.isfile(spec["path"]):
            print("MISSING", file=sys.stderr)
            results.append({"spec": spec, "ok": False, "error": "file missing"})
            continue
        r = run_one(spec)
        if r["ok"]:
            print(f"{r['verdict'].status} ({r['seconds']:.2f}s)", file=sys.stderr)
        else:
            print(f"ERROR: {r.get('error', '?')}", file=sys.stderr)
        results.append(r)
    out_path = "/tmp/sleec_realizability_report.html"
    html_doc = render_report(results)
    with open(out_path, "w") as fh:
        fh.write(html_doc)
    print(f"\nReport: {out_path}", file=sys.stderr)
    return out_path


if __name__ == "__main__":
    p = main()
    # On macOS, open in default browser.
    try:
        import subprocess
        subprocess.run(["open", p], check=False)
    except Exception:
        pass
