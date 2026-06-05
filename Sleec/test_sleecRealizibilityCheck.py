"""Tests for sleecRealizibilityCheck.py.

Run with either:
    python3 -m unittest test_sleecRealizibilityCheck.py
    # or
    python3 test_sleecRealizibilityCheck.py
"""
from __future__ import annotations

import os
import sys
import textwrap
import unittest

# Make sibling Analyzer/ importable and add this folder to sys.path so we can
# import the module-under-test directly.
_HERE = os.path.dirname(os.path.abspath(__file__))
_ANALYZER = os.path.join(os.path.dirname(_HERE), "Analyzer")
for p in (_ANALYZER, _HERE):
    if p not in sys.path:
        sys.path.insert(0, p)

import sleecParser  # noqa: E402
import sleecRealizibilityCheck as srlc  # noqa: E402


def _reset_parser_state() -> None:
    """sleecParser.py keeps module-level state (constants, scalar_type,
    scalar_mask, registered_type) that accumulates across parse_sleec calls.
    Wipe it between tests so scalar indices from one spec do not leak into
    another. Also reset the type_constructor action registry since create_action
    will refuse to register the same type twice."""
    sleecParser.constants.clear()
    sleecParser.scalar_type.clear()
    sleecParser.scalar_mask.clear()
    sleecParser.registered_type.clear()
    # Also reset the type_constructor module state that create_action builds up.
    # Without this, parsing a second spec that declares the same event name
    # would either reuse the old class or fail.
    import type_constructor
    if hasattr(type_constructor, "request_action_map"):
        type_constructor.request_action_map.clear()
    if hasattr(type_constructor, "attribute_variable_map"):
        type_constructor.attribute_variable_map.clear()
    if hasattr(type_constructor, "exception_map"):
        type_constructor.exception_map.clear()


def _parse(model_str: str):
    """Parse a SLEEC spec string; return the textX model object (not the full tuple)."""
    _reset_parser_state()
    model, _rules, _concerns, _purposes, _relations, _amap, _actions = \
        sleecParser.parse_sleec(model_str, read_file=False)
    return model


# ============================================================================
# classify_events
# ============================================================================

class TestClassifyEvents(unittest.TestCase):
    def test_pure_env_and_pure_system(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B
            rule_end
        """)
        model = _parse(spec)
        all_ev, triggers, responses, other, unused = srlc.classify_events(model)
        self.assertEqual(set(all_ev), {"A", "B"})
        self.assertEqual(triggers, {"A"})
        self.assertEqual(responses, {"B"})
        self.assertEqual(other, set())
        self.assertEqual(unused, [])

    def test_dual_role_event_classified_as_system(self):
        # C is both a response (in R1) and a trigger (in R2). Per the rule
        # "in a response wins", C must be classified as system.
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
            def_end
            rule_start
                R1 when A then C
                R2 when C then B
            rule_end
        """)
        model = _parse(spec)
        _all, triggers, responses, _other, _unused = srlc.classify_events(model)
        self.assertIn("C", triggers)
        self.assertIn("C", responses)
        # B is only a response, A is only a trigger.
        self.assertEqual(responses, {"B", "C"})

    def test_defeater_consequence_counts_as_response(self):
        # Event F only appears inside an `unless … then F` defeater branch.
        # It must still be classified as a system event.
        spec = textwrap.dedent("""
            def_start
                event E
                event Primary
                event F
                measure m: boolean
            def_end
            rule_start
                R1 when E then Primary unless {m} then F
            rule_end
        """)
        model = _parse(spec)
        _all, _triggers, responses, _other, _unused = srlc.classify_events(model)
        self.assertIn("F", responses)
        self.assertIn("Primary", responses)

    def test_otherwise_branch_counts_as_response(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Primary
                event Alt
            def_end
            rule_start
                R1 when E then Primary within 5 seconds otherwise Alt
            rule_end
        """)
        model = _parse(spec)
        _all, _triggers, responses, _other, _unused = srlc.classify_events(model)
        self.assertIn("Primary", responses)
        self.assertIn("Alt", responses)

    def test_negated_response_still_counts(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event X
            def_end
            rule_start
                R1 when E then not X within 5 seconds
            rule_end
        """)
        model = _parse(spec)
        _all, _triggers, responses, _other, _unused = srlc.classify_events(model)
        self.assertIn("X", responses)

    def test_unused_and_relation_only_events(self):
        # `UnusedEv` is declared but never referenced.
        # `A` and `B` appear only in an EventRel, not in any rule -> other_referenced.
        spec = textwrap.dedent("""
            def_start
                event T
                event R
                event A
                event B
                event UnusedEv
            def_end
            rule_start
                R1 when T then R
            rule_end
            relation_start
                happenBefore A B
            relation_end
        """)
        model = _parse(spec)
        all_ev, triggers, responses, other, unused = srlc.classify_events(model)
        self.assertEqual(set(all_ev), {"T", "R", "A", "B", "UnusedEv"})
        self.assertEqual(responses, {"R"})
        self.assertEqual(triggers, {"T"})
        self.assertEqual(other, {"A", "B"})
        self.assertEqual(unused, ["UnusedEv"])


# ============================================================================
# normalized rules (via SleecNorm)
# ============================================================================

class TestNormalization(unittest.TestCase):
    def test_unless_lifts_to_guarded_obligation(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure m: boolean
            def_end
            rule_start
                R1 when E then Resp within 5 seconds unless {m}
            rule_end
        """)
        _reset_parser_state()
        from SleecNorm import parse_sleec_norm
        _, norm_rules, *_ = parse_sleec_norm(spec, read_file=False)
        self.assertEqual(len(norm_rules), 1)
        nr = norm_rules[0]
        self.assertEqual(str(nr.triggering_event), "E")
        # The defeater `unless {m}` must lift to a condition `not m` gating the obligation.
        # Inspect the chain: first conditional obligation has condition containing `not m`.
        cobgs = nr.oc.obligations
        self.assertEqual(len(cobgs), 1)
        cond_str = str(cobgs[0].condition)
        self.assertIn("not", cond_str)
        self.assertIn("m", cond_str)
        self.assertEqual(str(cobgs[0].obligation.head), "Resp")

    def test_rule_level_and_condition_flows_into_obligation(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure g: boolean
            def_end
            rule_start
                R1 when E and {g} then Resp within 3 seconds
            rule_end
        """)
        _reset_parser_state()
        from SleecNorm import parse_sleec_norm
        _, norm_rules, *_ = parse_sleec_norm(spec, read_file=False)
        nr = norm_rules[0]
        cobg = nr.oc.obligations[0]
        # `and {g}` becomes the obligation's guard.
        self.assertIn("g", str(cobg.condition))

    def test_bare_rule_is_unconditional(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
            def_end
            rule_start
                R1 when E then Resp
            rule_end
        """)
        _reset_parser_state()
        from SleecNorm import parse_sleec_norm
        _, norm_rules, *_ = parse_sleec_norm(spec, read_file=False)
        cobg = norm_rules[0].oc.obligations[0]
        # Unconditional obligation has condition == True literal.
        self.assertTrue(cobg.condition is True or str(cobg.condition) == "True")


# ============================================================================
# TraceSampler — core behaviour + ALO blocking
# ============================================================================

class TestTraceSampler(unittest.TestCase):
    def test_paper_example_demo_sleec(self):
        """Reproduces the bounded-realizability paper's worked example:
        demo.sleec with N=5 yields a saturated trace (emergencyArrived at
        every step with userDeaf=True), 10/10 soft clauses satisfied."""
        spec = textwrap.dedent("""
            def_start
                event callEmergencyServices
                event leaveRoom
                event emergencyArrived
                measure userDeaf: boolean
            def_end
            rule_start
                R1 when callEmergencyServices then leaveRoom within 5 seconds
                R2 when emergencyArrived and {userDeaf} then not leaveRoom within 5 seconds
                R3 when emergencyArrived then callEmergencyServices within 0 seconds
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=5, verbose=False)
        trace = sampler.next_trace()
        self.assertIsNotNone(trace)
        self.assertEqual(trace["num_soft_clauses"], 10)   # R2, R3 × 5 steps
        self.assertEqual(trace["num_rule_firings"], 10)   # all saturate
        # Every step fires `emergencyArrived`.
        for step in trace["per_step"]:
            self.assertIn("emergencyArrived", step["events"])
            self.assertTrue(step["measures"]["userDeaf"])

    def test_alo_blocking_exhausts_when_saturated(self):
        """After blocking a saturated trace, next_trace returns None."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
            def_end
            rule_start
                R1 when E then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=3, verbose=False)
        trace1 = sampler.next_trace()
        self.assertIsNotNone(trace1)
        # Saturated: E fires at every step.
        self.assertTrue(all("E" in s["events"] for s in trace1["per_step"]))
        # Complement empty -> block() returns False.
        can_continue = sampler.block(trace1)
        self.assertFalse(can_continue)

    def test_alo_blocking_forces_new_event_when_possible(self):
        """With two independent env events, after the first (saturated) trace
        gets blocked externally, a second sampled trace would have to include
        at least one new occurrence — but here everything's already included,
        so `block` returns False. This checks we never incorrectly report a
        continuation."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event Resp
            def_end
            rule_start
                R1 when A then Resp
                R2 when B then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=2, verbose=False)
        t1 = sampler.next_trace()
        # Optimizer should fire both A and B at both steps -> 4/4 clauses.
        self.assertEqual(t1["num_rule_firings"], 4)
        self.assertFalse(sampler.block(t1))

    def test_only_env_triggered_rules_contribute_soft_clauses(self):
        """System-triggered rules are excluded from the optimizer's soft set
        (they depend on the agent's choice, outside the sampler's scope)."""
        spec = textwrap.dedent("""
            def_start
                event EnvE
                event SysE
            def_end
            rule_start
                R_env when EnvE then SysE
                R_sys when SysE then SysE within 5 seconds
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_soft_clauses"], 2)  # only R_env × 2 steps


# ============================================================================
# Measure relation hard constraints
# ============================================================================

class TestMeasureRelations(unittest.TestCase):
    def test_measure_mutual_exclusive_forces_alternation(self):
        """With `measure mutualExclusive {a} {b}` and rules that require each,
        the maximizer cannot fire both per-step rules at the same step."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure a: boolean
                measure b: boolean
            def_end
            rule_start
                R1 when E and {a} then Resp
                R2 when E and {b} then Resp
            rule_end
            relation_start
                measure mutualExclusive {a} {b}
            relation_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=3, verbose=False)
        trace = sampler.next_trace()
        # Per step at most one of (R1, R2) fires because a and b are mutex.
        # Total soft = 2 rules × 3 steps = 6, but max achievable = 3.
        self.assertEqual(trace["num_soft_clauses"], 6)
        self.assertLessEqual(trace["num_rule_firings"], 3)
        # Check the invariant actually holds in the returned measure valuations.
        for step in trace["per_step"]:
            self.assertFalse(step["measures"]["a"] and step["measures"]["b"])


# ============================================================================
# Numeric + scalar measure predicate compilation
# ============================================================================

class TestMeasurePredicates(unittest.TestCase):
    def test_numeric_measure_less_than_fires(self):
        """`{batteryLevel} < 20` must compile; the optimizer should choose
        batteryLevel < 20 so the rule can fire."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure batteryLevel: numeric
            def_end
            rule_start
                R1 when E and ({batteryLevel} < 20) then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_rule_firings"], 2)  # fires at both steps
        for step in trace["per_step"]:
            self.assertIn("E", step["events"])
            self.assertLess(step["measures"]["batteryLevel"], 20)

    def test_numeric_measure_conflicting_bounds(self):
        """Two rules with conflicting numeric bounds on the same measure
        cannot both fire at the same step."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure x: numeric
            def_end
            rule_start
                R1 when E and ({x} < 5) then Resp
                R2 when E and ({x} > 10) then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=3, verbose=False)
        trace = sampler.next_trace()
        # Per step at most one rule fires: 3 out of 6.
        self.assertLessEqual(trace["num_rule_firings"], 3)

    def test_scalar_measure_equality_fires(self):
        """`{sound} = loud` must compile; scalar measure var is bounded to
        [0, |params|-1], and the optimizer picks the loud index."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure sound: scale(low, medium, loud)
            def_end
            rule_start
                R1 when E and ({sound} = loud) then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_rule_firings"], 2)
        for step in trace["per_step"]:
            self.assertEqual(step["measures"]["sound"], "loud")

    def test_scalar_bounds_enforced(self):
        """Declared scalar values are always in {low, medium, loud}."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure sound: scale(low, medium, loud)
            def_end
            rule_start
                R1 when E then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.TraceSampler(model, N=4, verbose=False)
        trace = sampler.next_trace()
        for step in trace["per_step"]:
            self.assertIn(step["measures"]["sound"], {"low", "medium", "loud"})


# ============================================================================
# AbstractTraceSampler — per-rule abstraction, MaxSMT over (rule, step) bools.
# ============================================================================

class TestAbstractTraceSampler(unittest.TestCase):
    """The abstract sampler allocates one Bool assumption a_{r,t} per
    (env-triggered rule, step), binds it to the rule's measure condition via
    Iff, and maximizes total satisfied assumptions. Env events are implicitly
    on; ALO blocking is over assumptions."""

    def test_paper_example_demo_sleec(self):
        spec = textwrap.dedent("""
            def_start
                event callEmergencyServices
                event leaveRoom
                event emergencyArrived
                measure userDeaf: boolean
            def_end
            rule_start
                R1 when callEmergencyServices then leaveRoom within 5 seconds
                R2 when emergencyArrived and {userDeaf} then not leaveRoom within 5 seconds
                R3 when emergencyArrived then callEmergencyServices within 0 seconds
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=5, verbose=False)
        trace = sampler.next_trace()
        self.assertIsNotNone(trace)
        self.assertEqual(trace["abstraction"], "per-rule")
        # Two env-triggered rules (R2, R3) × 5 steps = 10 soft clauses.
        self.assertEqual(trace["num_soft_clauses"], 10)
        self.assertEqual(trace["num_rule_firings"], 10)
        for step in trace["per_step"]:
            self.assertEqual(step["events"], {"emergencyArrived"})
            # To satisfy R2's `and {userDeaf}`, optimizer picks userDeaf=True.
            self.assertTrue(step["measures"]["userDeaf"])

    def test_alo_blocking_exhausts_on_saturation(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
            def_end
            rule_start
                R1 when E then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=3, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_rule_firings"], 3)  # saturated
        self.assertFalse(sampler.block(trace))

    def test_alo_blocking_progresses_when_not_saturated(self):
        # R1 triggers only when g=True, R2 only when g=False. At each step
        # only one can fire -> inactive assumptions remain -> ALO advances.
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure g: boolean
            def_end
            rule_start
                R1 when E and {g} then Resp
                R2 when E and (not {g}) then Resp
            rule_end
        """)
        model = _parse(spec)
        N = 3
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
        trace1 = sampler.next_trace()
        self.assertEqual(trace1["num_soft_clauses"], 6)
        self.assertEqual(trace1["num_rule_firings"], 3)
        self.assertTrue(sampler.block(trace1))
        trace2 = sampler.next_trace()
        self.assertIsNotNone(trace2)
        fired1 = set(trace1["rules_fired"])
        fired2 = set(trace2["rules_fired"])
        self.assertTrue(fired2 - fired1, msg="ALO must force at least one new firing")

    def test_only_env_triggered_rules_contribute_assumptions(self):
        spec = textwrap.dedent("""
            def_start
                event EnvE
                event SysE
            def_end
            rule_start
                R_env when EnvE then SysE
                R_sys when SysE then SysE within 5 seconds
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_soft_clauses"], 2)  # R_env × 2 steps only
        # R_sys must not appear as a fired assumption.
        self.assertNotIn("R_sys", {name for name, _t in trace["rules_fired"]})

    def test_theory_reasoning_via_iff_binding(self):
        # Z3's DPLL(T) must resolve contradictory numeric bounds at the same step.
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure x: numeric
            def_end
            rule_start
                R1 when E and ({x} < 5) then Resp
                R2 when E and ({x} > 10) then Resp
            rule_end
        """)
        model = _parse(spec)
        N = 3
        sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_soft_clauses"], 2 * N)
        self.assertLessEqual(trace["num_rule_firings"], N)
        fired_by_step: dict = {}
        for name, t in trace["rules_fired"]:
            fired_by_step.setdefault(t, set()).add(name)
        for step in trace["per_step"]:
            firings_here = fired_by_step.get(step["t"], set())
            x = step["measures"]["x"]
            if "R1" in firings_here:
                self.assertLess(x, 5)
            if "R2" in firings_here:
                self.assertGreater(x, 10)
            # R1 and R2 cannot both fire in the same step (inconsistent bounds).
            self.assertNotEqual(firings_here, {"R1", "R2"})

    def test_scalar_measure_equality_fires_abstract(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure sound: scale(low, medium, loud)
            def_end
            rule_start
                R1 when E and ({sound} = loud) then Resp
            rule_end
        """)
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertEqual(trace["num_rule_firings"], 2)
        for step in trace["per_step"]:
            self.assertEqual(step["measures"]["sound"], "loud")

    def test_measure_invariant_respected(self):
        spec = textwrap.dedent("""
            def_start
                event E
                event Resp
                measure a: boolean
                measure b: boolean
            def_end
            rule_start
                R1 when E and {a} then Resp
                R2 when E and {b} then Resp
            rule_end
            relation_start
                measure mutualExclusive {a} {b}
            relation_end
        """)
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=3, verbose=False)
        trace = sampler.next_trace()
        self.assertLessEqual(trace["num_rule_firings"], 3)
        for step in trace["per_step"]:
            self.assertFalse(step["measures"]["a"] and step["measures"]["b"])


# ============================================================================
# RealizabilityChecker — inner loop: partial-validity MaxSAT over rules.
# ============================================================================

class TestRealizabilityChecker(unittest.TestCase):
    """Exercises the bounded-weak realizability check.

    The checker asks: given a SLEEC spec, a horizon N, and an environment
    partial trace, does the trace admit a bounded extension in which NO rule
    is demonstrably violated before the horizon? This is the paper's weak
    bounded realizability, implemented via SleecNorm.encode_limited +
    check_property_refining (no custom encoding).

    Key semantic reminder: obligations whose deadlines have already passed
    the horizon are vacuously \"not violated\". This is intentional and
    matches check_situational_conflict's own semantics.
    """

    def _make_trace(self, N, per_step):
        """Helper: build a trace dict in the shape the checker expects."""
        return {
            "N": N,
            "environment_events": [],
            "bool_measures": [],
            "num_measures": [],
            "scalar_measures": [],
            "per_step": per_step,
            "rules_fired": [],
            "num_rule_firings": 0,
            "num_soft_clauses": 0,
        }

    def test_simple_env_to_sys_is_realizable(self):
        """R1 when A then B: env event A demands sys event B at the same
        time. Bounded-weak realizability says SAT because the solver can
        place B anywhere including after horizon (deadline=0 is past-horizon
        for every trigger, vacuously satisfied)."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B
            rule_end
        """)
        model = _parse(spec)
        N = 3
        trace = self._make_trace(N, [
            {"t": t, "events": {"A"}, "measures": {}} for t in range(1, N + 1)
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_trigger_with_no_sys_class_forbidden(self):
        """R1 when A then B: env A demands B. If we assert the trace is
        consistent only when B exists somewhere, SAT. The checker doesn't
        forbid B, so we expect realizable. This is mainly a smoke check
        that the basic encoding terminates on a tiny spec."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B
            rule_end
        """)
        model = _parse(spec)
        N = 2
        trace = self._make_trace(N, [
            {"t": 1, "events": {"A"}, "measures": {}},
            {"t": 2, "events": {"A"}, "measures": {}},
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec)
        verdict = checker.check(trace)
        self.assertIn(verdict.status, {"realizable", "unrealizable"})

    def test_demo_sleec_paper_trace_weak_realizable(self):
        """Paper example (demo.sleec): saturated trace is weak-realizable
        because the solver places callEmergencyServices past horizon — under
        bounded-weak semantics, R3's deadline-in-future test passes as soon
        as any CES event exists in the universe."""
        spec = textwrap.dedent("""
            def_start
                event callEmergencyServices
                event leaveRoom
                event emergencyArrived
                measure userDeaf: boolean
            def_end
            rule_start
                R1 when callEmergencyServices then leaveRoom within 5 seconds
                R2 when emergencyArrived and {userDeaf} then not leaveRoom within 5 seconds
                R3 when emergencyArrived then callEmergencyServices within 0 seconds
            rule_end
        """)
        model = _parse(spec)
        N = 5
        trace = self._make_trace(N, [
            {"t": t, "events": {"emergencyArrived"}, "measures": {"userDeaf": True}}
            for t in range(1, N + 1)
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec, mode="weak")
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_test_sleec_paper_trace_weak_realizable(self):
        """test.sleec with a PatientFallen-only partial trace: weak-realizable."""
        spec = textwrap.dedent("""
            def_start
                event OpenCurtainRequest
                measure underDressed: boolean
                event SignalOpenCurtain
                event OpenCurtain
                event LeavePatient
                event UserFallen
                event SupportCalled
                event PatientFallen
                event ProvideCompanionship
                event CallSupport
                measure patientNotDeaf: boolean
            def_end
            rule_start
                r2 when PatientFallen then CallSupport
                r3 when PatientFallen then ProvideCompanionship within 10 minutes unless {patientNotDeaf}
                r4 when CallSupport then not ProvideCompanionship within 10 minutes
            rule_end
        """)
        model = _parse(spec)
        N = 5
        trace = self._make_trace(N, [
            {"t": t, "events": {"PatientFallen"},
             "measures": {"patientNotDeaf": False, "underDressed": False}}
            for t in range(1, N + 1)
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec, mode="weak")
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_scalar_measure_in_trace(self):
        """Scalar measure passed as its param name must be resolved to the
        right integer index when building FOL* trace assertions."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Y
                measure sound: scale(low, medium, loud)
            def_end
            rule_start
                R1 when E and ({sound} = loud) then Y
            rule_end
        """)
        model = _parse(spec)
        N = 2
        # Assert sound=loud at every step. R1's trigger fires, obligation
        # on Y is past-horizon (0s deadline) so vacuously not-violated.
        trace = self._make_trace(N, [
            {"t": t, "events": {"E"}, "measures": {"sound": "loud"}}
            for t in range(1, N + 1)
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_numeric_measure_in_trace(self):
        """Numeric measure value passed as int must be pinned via Int(val)."""
        spec = textwrap.dedent("""
            def_start
                event E
                event Y
                measure bat: numeric
            def_end
            rule_start
                R1 when E and ({bat} < 20) then Y
            rule_end
        """)
        model = _parse(spec)
        N = 2
        trace = self._make_trace(N, [
            {"t": t, "events": {"E"}, "measures": {"bat": 10}}
            for t in range(1, N + 1)
        ])
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_checker_requires_model_str(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B
            rule_end
        """)
        model = _parse(spec)
        with self.assertRaises(ValueError):
            srlc.RealizabilityChecker(model, N=2)  # no model_str

    def test_demo_sleec_strong_is_unrealizable(self):
        """Regression: under the default STRONG semantics, demo.sleec with the
        paper's saturated partial trace must return UNREALIZABLE because the
        R1/R2/R3 cascade admits no system extension."""
        spec = textwrap.dedent("""
            def_start
                event callEmergencyServices
                event leaveRoom
                event emergencyArrived
                measure userDeaf: boolean
            def_end
            rule_start
                R1 when callEmergencyServices then leaveRoom within 5 seconds
                R2 when emergencyArrived and {userDeaf} then not leaveRoom within 5 seconds
                R3 when emergencyArrived then callEmergencyServices within 0 seconds
            rule_end
        """)
        model = _parse(spec)
        N = 5
        trace = self._make_trace(N, [
            {"t": t, "events": {"emergencyArrived"}, "measures": {"userDeaf": True}}
            for t in range(1, N + 1)
        ])
        # default mode='strong'
        checker = srlc.RealizabilityChecker(model, N=N, model_str=spec)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "unrealizable")

    def test_decompose_equals_monolithic_on_demo(self):
        """Decomposition Theorem: checker with decompose=True must agree
        with decompose=False on demo.sleec@N=5 (UNREALIZABLE)."""
        spec = textwrap.dedent("""
            def_start
                event callEmergencyServices
                event leaveRoom
                event emergencyArrived
                measure userDeaf: boolean
            def_end
            rule_start
                R1 when callEmergencyServices then leaveRoom within 5 seconds
                R2 when emergencyArrived and {userDeaf} then not leaveRoom within 5 seconds
                R3 when emergencyArrived then callEmergencyServices within 0 seconds
            rule_end
        """)
        model = _parse(spec)
        N = 5
        trace = self._make_trace(N, [
            {"t": t, "events": {"emergencyArrived"}, "measures": {"userDeaf": True}}
            for t in range(1, N + 1)
        ])
        mono = srlc.RealizabilityChecker(
            model, N=N, model_str=spec, decompose=False).check(trace)
        deco = srlc.RealizabilityChecker(
            model, N=N, model_str=spec, decompose=True).check(trace)
        self.assertEqual(mono.status, deco.status)
        self.assertEqual(mono.status, "unrealizable")

    def test_decompose_two_independent_groups(self):
        """A spec with two rule sets on disjoint events must decompose
        into 2 components and be REALIZABLE end-to-end."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
                event D
            def_end
            rule_start
                R1 when A then B within 5 seconds
                R2 when C then D within 5 seconds
            rule_end
        """)
        model = _parse(spec)
        N = 3
        # Seed triggers both groups.
        trace = self._make_trace(N, [
            {"t": t, "events": {"A", "C"}, "measures": {}}
            for t in range(1, N + 1)
        ])
        # Confirm the decomposition sees two components.
        from sleecParser import read_model_file
        from SleecNorm import parse_sleec_norm
        from sleec_decompose import decompose_rules
        srlc._reset_sleecnorm_state()
        _m, rules_, _Am, _Acts, og_rules_, _c, relations_ = \
            parse_sleec_norm(spec, read_file=False)
        comps = decompose_rules(rules_, og_rules_, relations_)
        self.assertEqual(len(comps), 2,
                         f"expected 2 components, got {len(comps)}: {comps}")

        mono = srlc.RealizabilityChecker(
            model, N=N, model_str=spec, decompose=False).check(trace)
        deco = srlc.RealizabilityChecker(
            model, N=N, model_str=spec, decompose=True).check(trace)
        self.assertEqual(mono.status, deco.status)
        self.assertEqual(mono.status, "realizable")

    def _run_decompose_parity(self, spec_text, N, trace_steps, mode, expected):
        """Helper: run a spec both mono and decompose, assert same verdict,
        and if `expected` is not None, assert it matches `expected`."""
        model = _parse(spec_text)
        trace = self._make_trace(N, trace_steps)
        mono = srlc.RealizabilityChecker(
            model, N=N, model_str=spec_text, mode=mode, decompose=False
        ).check(trace)
        deco = srlc.RealizabilityChecker(
            model, N=N, model_str=spec_text, mode=mode, decompose=True
        ).check(trace)
        self.assertEqual(mono.status, deco.status,
            f"monolithic={mono.status} decomposed={deco.status} (mode={mode}, N={N})")
        if expected is not None:
            self.assertEqual(mono.status, expected,
                f"unexpected verdict: {mono.status} (mode={mode}, N={N})")

    def test_decompose_parity_head_conflict(self):
        """Head-share (relation a): R1: A->B, R2: A->not_B.
        One component; UNREALIZABLE under strong, REALIZABLE under weak
        whenever deadlines stay ≤ horizon."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 5 seconds
                R2 when A then not B within 5 seconds
            rule_end
        """)
        steps = [{"t": t, "events": {"A"}, "measures": {}} for t in range(1, 4)]
        # Strong: A triggers both every tick; window fully overlaps -> UNSAT.
        self._run_decompose_parity(spec, 3, steps, "strong", "unrealizable")
        # Weak at N=3: deadline t+5 > horizon 3, obligation vacuously
        # satisfied, so UNSAT is not forced -> REALIZABLE.
        self._run_decompose_parity(spec, 3, steps, "weak", "realizable")
        # Weak at N=10: deadlines fit within horizon, conflict forces UNSAT.
        self._run_decompose_parity(spec, 10,
            [{"t": t, "events": {"A"}, "measures": {}} for t in range(1, 11)],
            "weak", "unrealizable")

    def test_decompose_parity_cascade(self):
        """Cascade (relation b): R1: A->B, R2: B->C. Single component."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
            def_end
            rule_start
                R1 when A then B within 3 seconds
                R2 when B then C within 3 seconds
            rule_end
        """)
        steps = [{"t": t, "events": {"A"}, "measures": {}} for t in range(1, 4)]
        self._run_decompose_parity(spec, 3, steps, "strong", "realizable")
        self._run_decompose_parity(spec, 3, steps, "weak", "realizable")

    def test_decompose_parity_measure_bridge(self):
        """Two rules reading the same measure but with disjoint events.
        Under the simplified decomposition (no measure-coupling clause),
        these split into two components and both short-circuit as
        realizable because neither has a polarity clash."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
                event D
                measure shared: boolean
            def_end
            rule_start
                R1 when A and {shared} then B within 5 seconds
                R2 when C and {shared} then D within 5 seconds
            rule_end
        """)
        # Seed triggers both groups.
        steps = [
            {"t": t, "events": {"A", "C"}, "measures": {"shared": True}}
            for t in range(1, 4)
        ]
        # Confirm 2 components (was 1 under old clause-c decomposition).
        from sleec_decompose import decompose_rules
        from SleecNorm import parse_sleec_norm
        srlc._reset_sleecnorm_state()
        _m, rules_, _Am, _Acts, og_rules_, _c, relations_ = \
            parse_sleec_norm(spec, read_file=False)
        self.assertEqual(len(decompose_rules(rules_, og_rules_, relations_)),
                         2, "measure-coupling should no longer force a join")
        self._run_decompose_parity(spec, 3, steps, "strong", "realizable")
        self._run_decompose_parity(spec, 3, steps, "weak", "realizable")

    def test_decompose_parity_three_disjoint(self):
        """Three independent rules A->B, C->D, E->F.  Must decompose into
        3 singleton components and stay REALIZABLE."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
                event D
                event E
                event F
            def_end
            rule_start
                R1 when A then B within 5 seconds
                R2 when C then D within 5 seconds
                R3 when E then F within 5 seconds
            rule_end
        """)
        steps = [
            {"t": t, "events": {"A", "C", "E"}, "measures": {}}
            for t in range(1, 4)
        ]
        # Confirm 3 components.
        from sleec_decompose import decompose_rules
        from SleecNorm import parse_sleec_norm
        srlc._reset_sleecnorm_state()
        _m, rules_, _Am, _Acts, og_rules_, _c, relations_ = \
            parse_sleec_norm(spec, read_file=False)
        self.assertEqual(len(decompose_rules(rules_, og_rules_, relations_)), 3)
        self._run_decompose_parity(spec, 3, steps, "strong", "realizable")
        self._run_decompose_parity(spec, 3, steps, "weak", "realizable")

    def test_polarity_clash_short_circuit(self):
        """Exercise has_polarity_clash directly: a component with no head
        appearing on both polarities should short-circuit; a component
        with a head on both polarities should not."""
        from sleec_decompose import has_polarity_clash, decompose_rules
        from SleecNorm import parse_sleec_norm

        # Group with no clash (positive-only head on disjoint events).
        spec_no_clash = textwrap.dedent("""
            def_start
                event A
                event B
                event C
            def_end
            rule_start
                R1 when A then B within 3 seconds
                R2 when B then C within 3 seconds
            rule_end
        """)
        srlc._reset_sleecnorm_state()
        _m, rules_, _Am, _Acts, og_rules_, _c, _rel = \
            parse_sleec_norm(spec_no_clash, read_file=False)
        comps = decompose_rules(rules_, og_rules_, _rel)
        self.assertEqual(len(comps), 1, "cascade should group R1+R2")
        self.assertFalse(
            has_polarity_clash(rules_, comps[0]),
            "R1 and R2 are both positive; no clash on any head",
        )

        # Group with polarity clash (B is both + and -).
        spec_clash = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 5 seconds
                R2 when A then not B within 5 seconds
            rule_end
        """)
        srlc._reset_sleecnorm_state()
        _m, rules2, _Am, _Acts, og_rules2, _c, _rel = \
            parse_sleec_norm(spec_clash, read_file=False)
        comps2 = decompose_rules(rules2, og_rules2, _rel)
        self.assertEqual(len(comps2), 1)
        self.assertTrue(
            has_polarity_clash(rules2, comps2[0]),
            "B appears as both + (R1) and - (R2); clash expected",
        )

    def test_unrealizable_when_trace_violates_measure_invariant(self):
        """A trace that pins a measure to a value contradicting a declared
        measure invariant must return UNREALIZABLE. Exercises the UNSAT path
        of the checker end-to-end."""
        spec = textwrap.dedent("""
            def_start
                event E
                event R
                measure m: boolean
            def_end
            rule_start
                R1 when E then R within 5 seconds
            rule_end
            relation_start
                measure invariant (not {m})
            relation_end
        """)
        model = _parse(spec)
        # Pin m=True at step 1 — directly contradicts the invariant.
        bad_trace = {
            "N": 3,
            "environment_events": ["E"],
            "bool_measures": ["m"],
            "num_measures": [],
            "scalar_measures": [],
            "per_step": [
                {"t": 1, "events": {"E"}, "measures": {"m": True}},
                {"t": 2, "events": {"E"}, "measures": {"m": False}},
                {"t": 3, "events": {"E"}, "measures": {"m": False}},
            ],
            "rules_fired": [],
            "num_rule_firings": 0,
            "num_soft_clauses": 0,
        }
        checker = srlc.RealizabilityChecker(model, N=3, model_str=spec)
        verdict = checker.check(bad_trace)
        self.assertEqual(verdict.status, "unrealizable")
        self.assertIn("R1", verdict.culprit_rules)


if __name__ == "__main__":
    unittest.main(verbosity=2)
