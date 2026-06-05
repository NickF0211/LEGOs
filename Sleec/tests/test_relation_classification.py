"""Tests for the relation actor classification + Phase II partition.

Covers:
  - sys+measure relations (Causation/Effect/Forbid/UntilEM/TimedEM with
    sys event) raise RelationClassificationError when checked.
  - sys-only EventRel between two annotated sys events is encoded
    (does not error).
  - env-only and measure-only relations are encoded (backward compat).
  - mixed env+sys EventRel is silently skipped (no error, deferred).
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


def _parse(spec_text):
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from sleecParser import parse_sleec
    model, *_ = parse_sleec(spec_text, read_file=False)
    return model


def _make_trace(N, steps):
    return {
        "N": N,
        "environment_events": [],
        "bool_measures": [],
        "num_measures": [],
        "scalar_measures": [],
        "per_step": steps,
        "rules_fired": [],
        "num_rule_firings": 0,
        "num_soft_clauses": 0,
    }


class TestRelationClassifier(unittest.TestCase):
    """Direct tests of classify_relation_actors over the relation kinds."""

    def test_sys_only_event_rel(self):
        spec = textwrap.dedent("""
            def_start
                event A as system
                event B as system
                event Trig
            def_end
            rule_start
                R1 when Trig then A within 1 seconds
                R2 when Trig then B within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import (
            classify_events_with_annotations, classify_relation_actors,
            RelationActorKind,
        )
        model = _parse(spec)
        ec = classify_events_with_annotations(model)
        rel = model.relBlock.relations[0]
        self.assertEqual(classify_relation_actors(rel, ec),
                         RelationActorKind.SYS_ONLY_EVENTS)

    def test_env_only_event_rel(self):
        spec = textwrap.dedent("""
            def_start
                event A as environment
                event B as environment
                event R as system
                event Trig
            def_end
            rule_start
                R1 when Trig then R within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import (
            classify_events_with_annotations, classify_relation_actors,
            RelationActorKind,
        )
        model = _parse(spec)
        ec = classify_events_with_annotations(model)
        rel = model.relBlock.relations[0]
        self.assertEqual(classify_relation_actors(rel, ec),
                         RelationActorKind.ENV_ONLY_EVENTS)

    def test_mixed_env_sys_event_rel(self):
        spec = textwrap.dedent("""
            def_start
                event A as system
                event B as environment
                event Trig
            def_end
            rule_start
                R1 when Trig then A within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import (
            classify_events_with_annotations, classify_relation_actors,
            RelationActorKind,
        )
        model = _parse(spec)
        ec = classify_events_with_annotations(model)
        rel = model.relBlock.relations[0]
        self.assertEqual(classify_relation_actors(rel, ec),
                         RelationActorKind.MIXED_ENV_SYS_EVENTS)


class TestRealizabilityCheckerErrors(unittest.TestCase):
    """End-to-end: RealizabilityChecker raises on sys+measure relations."""

    def test_sys_event_with_measure_invariant_relation_errors(self):
        """A Causation relation `S {m}` where S is a system event:
        currently unsupported, must raise RelationClassificationError."""
        spec = textwrap.dedent("""
            def_start
                event Trig
                event S as system
                measure m: boolean
            def_end
            rule_start
                R1 when Trig then S within 5 seconds
            rule_end
            relation_start
                causation S {m}
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        from sleec_event_classification import RelationClassificationError
        model = _parse(spec)
        trace = _make_trace(3, [
            {"t": 1, "events": {"Trig"}, "measures": {"m": False}},
            {"t": 2, "events": {"Trig"}, "measures": {"m": False}},
            {"t": 3, "events": {"Trig"}, "measures": {"m": False}},
        ])
        checker = srlc.RealizabilityChecker(model, N=3, model_str=spec)
        with self.assertRaises(RelationClassificationError):
            checker.check(trace)

    def test_sys_only_event_rel_does_not_error(self):
        """Relation between two sys events should encode cleanly."""
        spec = textwrap.dedent("""
            def_start
                event Trig
                event A as system
                event B as system
            def_end
            rule_start
                R1 when Trig then A within 5 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        model = _parse(spec)
        trace = _make_trace(3, [
            {"t": 1, "events": {"Trig"}, "measures": {}},
            {"t": 2, "events": {"Trig"}, "measures": {}},
            {"t": 3, "events": {"Trig"}, "measures": {}},
        ])
        checker = srlc.RealizabilityChecker(model, N=3, model_str=spec)
        verdict = checker.check(trace)
        self.assertEqual(verdict.status, "realizable")

    def test_sys_only_event_rel_is_actually_enforced(self):
        """Verify the sys-sys relation actually flips the verdict when added.
        Without the relation, two sys obligations at the same time are
        independently satisfiable. With mutualExclusive A B, they conflict."""
        spec_no_rel = textwrap.dedent("""
            def_start
                event Trig
                event A as system
                event B as system
            def_end
            rule_start
                R1 when Trig then A within 0 seconds
                R2 when Trig then B within 0 seconds
            rule_end
        """)
        spec_with_rel = textwrap.dedent("""
            def_start
                event Trig
                event A as system
                event B as system
            def_end
            rule_start
                R1 when Trig then A within 0 seconds
                R2 when Trig then B within 0 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        trace = _make_trace(3, [
            {"t": 1, "events": {"Trig"}, "measures": {}},
            {"t": 2, "events": {"Trig"}, "measures": {}},
            {"t": 3, "events": {"Trig"}, "measures": {}},
        ])
        # Without the relation: realizable.
        v_no = srlc.RealizabilityChecker(
            _parse(spec_no_rel), N=3, model_str=spec_no_rel
        ).check(trace)
        self.assertEqual(v_no.status, "realizable",
            "two sys obligations on disjoint heads should be jointly satisfiable")
        # With mutualExclusive A B: unrealizable.
        v_with = srlc.RealizabilityChecker(
            _parse(spec_with_rel), N=3, model_str=spec_with_rel
        ).check(trace)
        self.assertEqual(v_with.status, "unrealizable",
            "mutualExclusive A B must make A@t and B@t conflict; verdict should flip")

    def test_mixed_env_sys_event_rel_is_skipped(self):
        """Mixed env+sys EventRel without a measure: silently skipped, no error."""
        spec = textwrap.dedent("""
            def_start
                event Trig as environment
                event Sys as system
            def_end
            rule_start
                R1 when Trig then Sys within 5 seconds
            rule_end
            relation_start
                mutualExclusive Trig Sys
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        model = _parse(spec)
        trace = _make_trace(3, [
            {"t": 1, "events": {"Trig"}, "measures": {}},
            {"t": 2, "events": {"Trig"}, "measures": {}},
            {"t": 3, "events": {"Trig"}, "measures": {}},
        ])
        # Should not raise (relation is silently skipped).
        checker = srlc.RealizabilityChecker(model, N=3, model_str=spec)
        verdict = checker.check(trace)
        # Verdict can be either; just assert it ran.
        self.assertIn(verdict.status, ("realizable", "unrealizable"))


if __name__ == "__main__":
    unittest.main()
