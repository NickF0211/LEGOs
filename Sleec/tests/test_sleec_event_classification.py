"""Unit tests for sleec_event_classification.

Covers the four-step inference pipeline plus the three blocking
conflict kinds and the one warning kind. Test specs are inlined as
strings to keep the suite self-contained; we parse them via the same
`parse_sleec` entry point the rest of the toolchain uses.
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
    """Parse a SLEEC source string into a textX model."""
    # Reset shared global state in sleecParser between parses so that
    # registered scalar types from prior tests don't leak in (mirrors the
    # idiom used elsewhere in the test suite).
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from sleecParser import parse_sleec
    model, *_ = parse_sleec(spec_text, read_file=False)
    return model


class TestEventKindAnnotations(unittest.TestCase):
    """Step 1: annotations are honored verbatim."""

    def test_annotation_system(self):
        spec = "def_start\n event A as system\ndef_end\nrule_start\n R1 when A then A within 1 seconds\nrule_end\n"
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        self.assertEqual(ec.kind["A"], Kind.SYSTEM)

    def test_annotation_environment(self):
        spec = ("def_start\n event A as environment\n event B\ndef_end\n"
                "rule_start\n R1 when A then B within 1 seconds\nrule_end\n")
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        self.assertEqual(ec.kind["A"], Kind.ENVIRONMENT)


class TestRuleResponseInference(unittest.TestCase):
    """Step 2: events appearing in a rule response are inferred SYSTEM."""

    def test_response_inferred_system(self):
        spec = ("def_start\n event Trig\n event Resp\ndef_end\n"
                "rule_start\n R1 when Trig then Resp within 5 seconds\nrule_end\n")
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        self.assertEqual(ec.kind["Resp"], Kind.SYSTEM)
        self.assertEqual(ec.kind["Trig"], Kind.ENVIRONMENT)

    def test_unused_event_defaults_to_environment(self):
        spec = ("def_start\n event Trig\n event Resp\n event Loose\ndef_end\n"
                "rule_start\n R1 when Trig then Resp within 5 seconds\nrule_end\n")
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        self.assertEqual(ec.kind["Loose"], Kind.ENVIRONMENT)


class TestRelationPropagation(unittest.TestCase):
    """Step 3: SYSTEM kind propagates through any multi-event relation."""

    def test_propagation_via_event_rel(self):
        spec = textwrap.dedent("""
            def_start
                event A as system
                event B
            def_end
            rule_start
                R1 when A then A within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        self.assertEqual(ec.kind["B"], Kind.SYSTEM,
            "B should propagate to system via mutualExclusive A B")

    def test_no_propagation_when_no_sys_neighbor(self):
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then A within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import classify_events_with_annotations, Kind
        ec = classify_events_with_annotations(_parse(spec))
        # A is sys (rule response), so B propagates.
        self.assertEqual(ec.kind["A"], Kind.SYSTEM)
        self.assertEqual(ec.kind["B"], Kind.SYSTEM)


class TestConflicts(unittest.TestCase):
    """The three blocking conflict kinds and the one warning."""

    def test_annotated_env_but_response(self):
        spec = textwrap.dedent("""
            def_start
                event A as environment
            def_end
            rule_start
                R1 when A then A within 5 seconds
            rule_end
        """)
        from sleec_event_classification import (classify_events_with_annotations,
                                                ConflictCode)
        ec = classify_events_with_annotations(_parse(spec))
        self.assertTrue(ec.has_errors)
        self.assertTrue(any(c.code == ConflictCode.ANNOTATED_ENV_BUT_RESPONSE
                            for c in ec.errors),
            f"expected ANNOTATED_ENV_BUT_RESPONSE; got {[c.code for c in ec.errors]}")

    def test_annotated_env_but_sys_relation(self):
        spec = textwrap.dedent("""
            def_start
                event A as system
                event B as environment
            def_end
            rule_start
                R1 when A then A within 1 seconds
            rule_end
            relation_start
                mutualExclusive A B
            relation_end
        """)
        from sleec_event_classification import (classify_events_with_annotations,
                                                ConflictCode)
        ec = classify_events_with_annotations(_parse(spec))
        self.assertTrue(ec.has_errors)
        self.assertTrue(any(c.code == ConflictCode.ANNOTATED_ENV_BUT_SYS_RELATION
                            for c in ec.errors),
            f"expected ANNOTATED_ENV_BUT_SYS_RELATION; got {[c.code for c in ec.errors]}")

    def test_annotated_sys_but_never_response_is_warning(self):
        spec = textwrap.dedent("""
            def_start
                event A as system
                event Trig
            def_end
            rule_start
                R1 when Trig then Trig within 1 seconds
            rule_end
            relation_start
                mutualExclusive A Trig
            relation_end
        """)
        from sleec_event_classification import (classify_events_with_annotations,
                                                ConflictCode)
        ec = classify_events_with_annotations(_parse(spec))
        # Trig is in a response, so Trig is sys; no env/sys relation conflict.
        # A is annotated sys but never used as a response -> warning, not error.
        self.assertFalse(ec.has_errors,
            f"expected no errors; got {[c.code for c in ec.errors]}")
        self.assertTrue(any(c.code == ConflictCode.ANNOTATED_SYS_BUT_NEVER_RESPONSE
                            for c in ec.warnings),
            f"expected ANNOTATED_SYS_BUT_NEVER_RESPONSE warning; "
            f"got {[c.code for c in ec.warnings]}")

    def test_clean_spec_has_no_conflicts(self):
        spec = textwrap.dedent("""
            def_start
                event Trig
                event Resp as system
                measure m: boolean
            def_end
            rule_start
                R1 when Trig and {m} then Resp within 5 seconds
            rule_end
        """)
        from sleec_event_classification import classify_events_with_annotations
        ec = classify_events_with_annotations(_parse(spec))
        self.assertFalse(ec.has_errors,
            f"expected no errors; got {[c.code for c in ec.errors]}")


class TestSamplerIntegration(unittest.TestCase):
    """Integration: the AbstractTraceSampler must raise EventClassificationError
    on a spec with classification errors."""

    def test_sampler_raises_on_conflict(self):
        spec = textwrap.dedent("""
            def_start
                event A as environment
            def_end
            rule_start
                R1 when A then A within 5 seconds
            rule_end
        """)
        import sleecRealizibilityCheck as srlc
        from sleec_event_classification import EventClassificationError
        model = _parse(spec)
        with self.assertRaises(EventClassificationError):
            srlc.AbstractTraceSampler(model, N=3, verbose=False)

    def test_sampler_succeeds_on_clean_spec(self):
        spec = textwrap.dedent("""
            def_start
                event Trig
                event Resp as system
            def_end
            rule_start
                R1 when Trig then Resp within 5 seconds
            rule_end
        """)
        import sleecRealizibilityCheck as srlc
        model = _parse(spec)
        sampler = srlc.AbstractTraceSampler(model, N=3, verbose=False)
        # env_events should derive from the ENVIRONMENT-kind events.
        self.assertIn("Trig", sampler.env_events)
        self.assertNotIn("Resp", sampler.env_events)


if __name__ == "__main__":
    unittest.main()
