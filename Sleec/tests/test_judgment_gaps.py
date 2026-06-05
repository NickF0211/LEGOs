"""Tests addressing the gaps I flagged after reading the actual UI output.

Three areas:
  1. Phase I + Phase II consistency on relation specs: the trace the
     sampler produces should not be Phase-II-rejected purely because of
     a relation (only because of rule head clashes).
  2. Encoder-necessity (adversarial) for UntilEM: design a spec where
     MaxSAT would prefer m=False (because a rule fires on `{not m}`),
     but UntilEM forces m=True in a window. With the encoder, MaxSAT
     should be forced into the window to pick m=True; without it,
     MaxSAT would pick m=False and violate the relation.
  3. Cascade vs sampler-fired: in a realistic-alarm-style spec where a
     sys-triggered rule (R2) cascades from a sys-event response (R1's
     AlarmTriggered), R2 is NOT in `rules_fired` but the timeline
     correctly shows R2's obligations on the cascaded sys event.
"""

import os
import sys
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)


def _parse(spec):
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from sleecParser import parse_sleec
    model, *_ = parse_sleec(spec, read_file=False)
    return model


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


# ---------------------------------------------------------------------------
# 1. Phase I / Phase II consistency on relation specs
# ---------------------------------------------------------------------------

class TestPhaseConsistency(unittest.TestCase):
    """For every spec under experiments/relation_specs/, sample a trace
    via Phase I and dispatch to Phase II. Both phases encode the same
    relations; they should agree on whether the trace is satisfiable
    (modulo rule head clashes which are the realizability question)."""

    def _run(self, spec_path, N, expect_status):
        import sleecRealizibilityCheck as srlc
        from sleecParser import parse_sleec, read_model_file
        srlc._reset_sleecnorm_state()
        model_str = read_model_file(spec_path)
        model, *_ = parse_sleec(spec_path, read_file=True)
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
        trace = sampler.next_trace()
        self.assertIsNotNone(trace, f"sampler unexpectedly returned None for {spec_path}")
        checker = srlc.RealizabilityChecker(model, N=N, model_str=model_str)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, expect_status,
            f"phase-II verdict on {os.path.basename(spec_path)}: "
            f"expected {expect_status}, got {verdict.status}; trace={trace['per_step']}")

    def test_all_realistic_real(self):
        for spec in ("realistic_alarm.sleec", "realistic_robot.sleec",
                     "all_kinds_combined.sleec",
                     "edge_chain_happenBefore.sleec",
                     "edge_self_mutex.sleec",
                     "contradictory_env.sleec",
                     "combined_three.sleec"):
            with self.subTest(spec=spec):
                path = os.path.join(SLEEC, "experiments/relation_specs", spec)
                self._run(path, N=4, expect_status="realizable")

    def test_realistic_unreal(self):
        path = os.path.join(SLEEC, "experiments/relation_specs",
                            "realistic_unreal.sleec")
        self._run(path, N=4, expect_status="unrealizable")


# ---------------------------------------------------------------------------
# 2. Encoder necessity (adversarial) for UntilEM
# ---------------------------------------------------------------------------

class TestUntilEMEncoderAdversarial(unittest.TestCase):
    """Adversarial spec: MaxSAT prefers m=False (rule fires when not {m}).
    UntilEM forces m=True in the window. With the encoder, sampler is
    pinned. Without it, sampler would pick m=False and violate the
    relation."""

    SPEC = textwrap.dedent("""
        def_start
            event Wake
            event Sleep
            event Resp as system
            measure m: boolean
        def_end
        rule_start
            R1 when Wake then Resp within 0 seconds
            R2 when Wake and (not {m}) then Resp within 0 seconds
        rule_end
        relation_start
            when Wake then {m} until Sleep
        relation_end
    """)
    # Without the relation, MaxSAT picks m=False at every step:
    #   - R1 fires regardless of m.
    #   - R2 fires only when m=False.
    #   So m=False at every step gives 2 firings/step.
    # With the relation, when Wake fires (every step) and Sleep doesn't,
    # m must be True from t_start to horizon. So R2 cannot fire.
    # Expected sampler behavior: m=True at every step where Wake fires
    # without an intervening Sleep. R2 fires only at steps where Sleep
    # closed the UntilEM window.

    def test_encoder_pins_m_inside_window(self):
        """With encoder ON: traces must respect UntilEM's invariant.
        Pick a trace; verify that for every t_start with Wake@t_start,
        m@t' is True at every t' in [t_start, t_end-1] where t_end is
        the next Sleep@t' (or N+1 if no Sleep)."""
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(self.SPEC), N=4, verbose=False)
        # collect a few traces
        traces = []
        for _ in range(4):
            t = sampler.next_trace()
            if t is None:
                break
            traces.append(t)
            if not sampler.block(t):
                break
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t_start in range(1, 5):
                evs = _events_at(tr, t_start)
                if "Wake" not in evs:
                    continue
                t_end = 5  # past horizon
                for tp in range(t_start, 5):
                    if "Sleep" in _events_at(tr, tp):
                        t_end = tp
                        break
                for tp in range(t_start, t_end):
                    ms = _measures_at(tr, tp)
                    self.assertEqual(
                        ms.get("m"), True,
                        f"UntilEM violated on trace {tr['per_step']}: "
                        f"Wake@{t_start}, no Sleep until {t_end}, but m@{tp}={ms.get('m')}",
                    )

    def test_encoder_disabled_admits_violation(self):
        """Demonstrate that without the encoder, MaxSAT does pick m=False
        and violate UntilEM. Confirms the encoder is genuinely doing work."""
        import sleecRealizibilityCheck as srlc
        import sleec_sampler_relations as ssr

        original = ssr.add_relation_constraints
        try:
            ssr.add_relation_constraints = lambda *a, **kw: None  # disable
            sampler = srlc.AbstractTraceSampler(_parse(self.SPEC), N=4, verbose=False)
            tr = sampler.next_trace()
        finally:
            ssr.add_relation_constraints = original

        self.assertIsNotNone(tr)
        # Find a step where Wake fires, no preceding Sleep, but m=False.
        violation_seen = False
        for t_start in range(1, 5):
            evs = _events_at(tr, t_start)
            if "Wake" not in evs:
                continue
            for tp in range(t_start, 5):
                if "Sleep" in _events_at(tr, tp):
                    break
                ms = _measures_at(tr, tp)
                if ms.get("m") is False:
                    violation_seen = True
                    break
            if violation_seen:
                break
        self.assertTrue(violation_seen,
            f"expected encoder-disabled sampler to violate UntilEM "
            f"(MaxSAT favors m=False to fire R2); "
            f"trace={tr['per_step']}")


# ---------------------------------------------------------------------------
# 3. Cascade vs sampler-fired
# ---------------------------------------------------------------------------

class TestCascadeVsFired(unittest.TestCase):
    """Sampler-fired = rule whose trigger is an env event AND the env
    trigger is True AND condition holds. Cascade-derived = rule whose
    trigger is a sys event that another rule's response would produce.
    The first goes in trace['rules_fired']; the second is only visible
    in the obligation timeline.
    """

    SPEC = textwrap.dedent("""
        def_start
            event EnvTrig
            event SysAct as system
            event SysReact as system
        def_end
        rule_start
            R1 when EnvTrig then SysAct within 0 seconds
            R2 when SysAct then SysReact within 0 seconds
        rule_end
    """)
    # R1 has an env trigger -> goes into rule_soft and rules_fired.
    # R2 has a sys trigger (SysAct) -> NOT in rule_soft, NOT in rules_fired.
    # Phase II will cascade R2 because R1 produces SysAct.

    def test_only_env_triggered_in_rules_fired(self):
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(self.SPEC), N=3, verbose=False)
        tr = sampler.next_trace()
        fired = {name for (name, _t) in tr["rules_fired"]}
        self.assertIn("R1", fired,
            "env-triggered R1 must be in rules_fired")
        self.assertNotIn("R2", fired,
            "sys-triggered R2 must NOT be in rules_fired (sampler doesn't "
            "track sys-triggered rules)")

    def test_timeline_contains_sys_triggered_via_cascade(self):
        """The obligation timeline's cascade closure should include R2's
        obligation on SysReact, even though R2 isn't in rules_fired."""
        import sleecRealizibilityCheck as srlc
        from SleecNorm import parse_sleec_norm
        from sleec_timeline import build_timeline

        srlc._reset_sleecnorm_state()
        model, rules, _A, _Acts, _og, _c, _r = parse_sleec_norm(
            self.SPEC, read_file=False
        )
        sampler = srlc.AbstractTraceSampler(model, N=3, verbose=False)
        tr = sampler.next_trace()

        text, _spans = build_timeline(rules, tr, set(), col_width=10)
        # The timeline should mention both SysAct (R1's head) and SysReact
        # (R2's head, only reachable via cascade).
        self.assertIn("SysAct", text,
            f"timeline missing SysAct row:\n{text}")
        self.assertIn("SysReact", text,
            f"timeline missing SysReact row (R2 cascaded from R1):\n{text}")


if __name__ == "__main__":
    unittest.main()
