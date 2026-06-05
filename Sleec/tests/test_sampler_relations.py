"""Tests for sleec_sampler_relations.add_relation_constraints.

For each encodable env-side relation kind, build a small spec where
the relation pins the sampler's choice. Verify that every trace the
sampler returns satisfies the relation's semantics. The samplers'
MaxSAT objective tries to fire as many rules as possible, so without
the relation the sampler would happily produce a violating trace; with
the relation, it must respect the constraint.
"""

import os
import sys
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER):
    if p not in sys.path:
        sys.path.insert(0, p)


def _parse(spec):
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from sleecParser import parse_sleec
    model, *_ = parse_sleec(spec, read_file=False)
    return model


def _collect_traces(sampler, max_iter=4):
    """Pull at most max_iter traces, blocking between each. Returns list."""
    out = []
    for _ in range(max_iter):
        t = sampler.next_trace()
        if t is None:
            break
        out.append(t)
        if not sampler.block(t):
            break
    return out


def _events_at(trace, t):
    """Return set of env event names present at SLEEC time t."""
    for step in trace["per_step"]:
        if step["t"] == t:
            return set(step["events"])
    return set()


def _measures_at(trace, t):
    for step in trace["per_step"]:
        if step["t"] == t:
            return dict(step["measures"])
    return {}


class TestEventRelations(unittest.TestCase):
    """witness, equal, mutualExclusive, happenBefore between env events."""

    def test_witness_lhs_implies_rhs(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event Resp as system
            def_end
            rule_start
                R1 when A then Resp within 0 seconds
            rule_end
            relation_start
                witness A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                if "A" in evs:
                    self.assertIn("B", evs,
                        f"witness violated at t={t}: A present without B")

    def test_mutex_lhs_and_rhs_never_co_occur(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event Resp as system
            def_end
            rule_start
                R1 when A then Resp within 0 seconds
                R2 when B then Resp within 0 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                self.assertFalse("A" in evs and "B" in evs,
                    f"mutualExclusive violated at t={t}: {evs}")

    def test_equal_lhs_and_rhs_co_occur_at_every_step(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event Resp as system
            def_end
            rule_start
                R1 when A then Resp within 0 seconds
            rule_end
            relation_start
                equal A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                self.assertEqual("A" in evs, "B" in evs,
                    f"equal violated at t={t}: A={'A' in evs}, B={'B' in evs}")

    def test_happen_before_no_rhs_at_t_1(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event Resp as system
            def_end
            rule_start
                R1 when B then Resp within 0 seconds
            rule_end
            relation_start
                happenBefore A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            # B at t must be preceded by A at some t' < t.
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                if "B" in evs:
                    earlier = set()
                    for tprime in range(1, t):
                        earlier.update(_events_at(tr, tprime))
                    self.assertIn("A", earlier,
                        f"happenBefore violated: B@t={t} without earlier A; "
                        f"trace={tr['per_step']}")


class TestCausationEffectForbid(unittest.TestCase):
    """Causation, Effect (includes), Forbid with env-event cause."""

    def test_causation_effect_implies_cause(self):
        # effect_expr {m} holding at t implies cause E at t.
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp as system
                measure m: boolean
            def_end
            rule_start
                R1 when E then Resp within 0 seconds
            rule_end
            relation_start
                causation E {m}
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                ms = _measures_at(tr, t)
                if ms.get("m") is True:
                    self.assertIn("E", evs,
                        f"causation violated at t={t}: m=True but E missing")

    def test_effect_cause_implies_effect(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp as system
                measure m: boolean
            def_end
            rule_start
                R1 when E then Resp within 0 seconds
            rule_end
            relation_start
                includes E {m}
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                ms = _measures_at(tr, t)
                if "E" in evs:
                    self.assertEqual(ms.get("m"), True,
                        f"includes violated at t={t}: E present but m={ms.get('m')}")

    def test_forbid_cause_implies_not_effect(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp as system
                measure m: boolean
            def_end
            rule_start
                R1 when E then Resp within 0 seconds
            rule_end
            relation_start
                forbid E {m}
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t in (1, 2, 3):
                evs = _events_at(tr, t)
                ms = _measures_at(tr, t)
                if "E" in evs:
                    self.assertNotEqual(ms.get("m"), True,
                        f"forbid violated at t={t}: E present and m=True")


class TestExtendedModalities(unittest.TestCase):
    """UntilEM and TimedEM with env-event start trigger."""

    def test_until_em_invariant_holds_until_end(self):
        # When E1 fires, m must hold from then until E2 fires (or to horizon).
        spec = textwrap.dedent("""
            def_start
                event E1
                event E2
                event Resp as system
                measure m: boolean
            def_end
            rule_start
                R1 when E1 then Resp within 0 seconds
            rule_end
            relation_start
                when E1 then {m} until E2
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=3, verbose=False)
        traces = _collect_traces(sampler, max_iter=4)
        self.assertGreater(len(traces), 0)
        for tr in traces:
            for t_start in (1, 2, 3):
                if "E1" not in _events_at(tr, t_start):
                    continue
                # find next E2 after t_start
                t_end = 4  # > horizon means "never"
                for t_prime in range(t_start, 4):
                    if "E2" in _events_at(tr, t_prime):
                        t_end = t_prime
                        break
                # m must hold for every t' in [t_start, t_end - 1]
                for t_prime in range(t_start, t_end):
                    ms = _measures_at(tr, t_prime)
                    self.assertEqual(
                        ms.get("m"), True,
                        f"UntilEM violated: E1@{t_start}, E2@{t_end} but "
                        f"m={ms.get('m')} at t={t_prime} (trace={tr['per_step']})",
                    )

    def test_timed_em_encoder_direct(self):
        """The textX grammar resolves `when ... then ... [for|until] ...`
        ambiguously, preferring UntilEM. We therefore test the bounded
        TimedEM encoder _enc_timed_em directly: build z3 vars by hand,
        construct expressions for cond/duration/inv, run the encoder,
        and confirm the optimizer picks values consistent with the
        relation."""
        import z3
        from sleec_sampler_relations import _enc_timed_em

        N = 4
        opt = z3.Optimize()
        # E1 presence per step.
        e1 = [z3.Bool(f"E1_{t}") for t in range(1, N + 1)]
        # m presence per step.
        m = [z3.Bool(f"m_{t}") for t in range(1, N + 1)]

        # cond = True (no condition); duration = 2 (constant); inv = m.
        cond_at = lambda t_idx: z3.BoolVal(True)
        duration_at = lambda t_idx: z3.IntVal(2)
        inv_at = lambda t_idx: m[t_idx]

        _enc_timed_em(opt, e1, cond_at, duration_at, inv_at, N)

        # Force E1@1 to fire so the implication has bite.
        opt.add(e1[0])
        # Set m=False at t=2 so the implication fails iff TimedEM bound
        # actually requires m at t=2.
        opt.add(z3.Not(m[1]))

        # Expect UNSAT: TimedEM says m must hold over [1, 1+2-1] = [1, 2].
        self.assertEqual(opt.check(), z3.unsat,
            "TimedEM encoder should make m@2 required given E1@1 + duration=2")

        # Now relax: only force E1@1, no constraint on m. Should be SAT
        # with m@1 and m@2 both True.
        opt2 = z3.Optimize()
        e1b = [z3.Bool(f"E1b_{t}") for t in range(1, N + 1)]
        mb = [z3.Bool(f"mb_{t}") for t in range(1, N + 1)]
        _enc_timed_em(
            opt2, e1b,
            lambda t_idx: z3.BoolVal(True),
            lambda t_idx: z3.IntVal(2),
            lambda t_idx: mb[t_idx],
            N,
        )
        opt2.add(e1b[0])
        self.assertEqual(opt2.check(), z3.sat)
        model_z3 = opt2.model()
        self.assertTrue(bool(model_z3.eval(mb[0], model_completion=True)),
                        "m@1 must be True")
        self.assertTrue(bool(model_z3.eval(mb[1], model_completion=True)),
                        "m@2 must be True")

if __name__ == "__main__":
    unittest.main()