"""Tests for first-class relations in decomposition.

Verifies decompose_with_relations:
  - Two cascading rules (R1: A->B, R2: B->C) form one component (already
    true via clause b; this is the user's confidence test).
  - Two rules with NO direct rule-rule coupling but linked by a sys-only
    relation (mutualExclusive on their heads) end up in one component.
  - Realizability check on that 2nd case correctly returns UNREALIZABLE
    (relation IS encoded into the per-component query, AND the polarity
    short-circuit is disabled because the component carries a relation).
  - Measure-only relations land in global_relation_indices (asserted in
    every component's solve).
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


def _parse_norm(spec_text):
    """Parse via SleecNorm.parse_sleec_norm; matches what the realizability
    checker uses."""
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from SleecNorm import parse_sleec_norm
    return parse_sleec_norm(spec_text, read_file=False)


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


class TestDecomposeWithRelations(unittest.TestCase):

    def test_cascade_R1_R2_one_component(self):
        """User's question: R1: when A then B, R2: when B then C
        → one component (clause b cascade)."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B as system
                event C as system
            def_end
            rule_start
                R1 when A then B within 5 seconds
                R2 when B then C within 5 seconds
            rule_end
        """)
        from sleec_decompose import decompose_with_relations
        from sleec_event_classification import classify_events_with_annotations
        m, rules, _A, _Acts, og_rules, _c, relations = _parse_norm(spec)
        ec = classify_events_with_annotations(m)
        d = decompose_with_relations(rules, og_rules, relations, ec)
        self.assertEqual(len(d.components), 1,
            "R1 and R2 should be cascade-linked into one component")
        self.assertEqual(set(d.components[0].rule_indices), {0, 1})

    def test_relation_links_otherwise_independent_rules(self):
        """R1: A -> P, R2: A -> Q. No head-share, no cascade.
        With a sys-only mutualExclusive P Q relation, the relation node
        unions them into one component."""
        spec = textwrap.dedent("""
            def_start
                event A
                event P as system
                event Q as system
            def_end
            rule_start
                R1 when A then P within 5 seconds
                R2 when A then Q within 5 seconds
            rule_end
            relation_start
                mutualExclusive P Q
            relation_end
        """)
        from sleec_decompose import decompose_with_relations, decompose_rules
        from sleec_event_classification import classify_events_with_annotations
        m, rules, _A, _Acts, og_rules, _c, relations = _parse_norm(spec)

        # Without first-class relations (legacy decompose_rules with the
        # *old* clause-d still uses _relation_alphabet; let's verify both
        # routes produce one component).
        legacy = decompose_rules(rules, og_rules, relations)
        self.assertEqual(len(legacy), 1,
            "legacy clause-d should also union R1+R2 via the relation")

        # New first-class: relation node lives inside the component.
        ec = classify_events_with_annotations(m)
        d = decompose_with_relations(rules, og_rules, relations, ec)
        self.assertEqual(len(d.components), 1)
        self.assertEqual(set(d.components[0].rule_indices), {0, 1})
        self.assertEqual(d.components[0].relation_indices, [0],
            "the mutualExclusive relation should be assigned to the component")

    def test_realizability_with_short_circuit_disabled_when_relation_present(self):
        """R1: A -> P, R2: A -> Q with mutualExclusive P Q.
        Polarity-clash short-circuit would (incorrectly) declare this
        realizable since neither P nor Q has both polarities. The relation
        forces UNSAT. The check must disable short-circuit when a
        component carries any coupling relation, so we get UNREALIZABLE."""
        spec = textwrap.dedent("""
            def_start
                event A
                event P as system
                event Q as system
            def_end
            rule_start
                R1 when A then P within 0 seconds
                R2 when A then Q within 0 seconds
            rule_end
            relation_start
                mutualExclusive P Q
            relation_end
        """)
        import sleecRealizibilityCheck as srlc
        from sleecParser import parse_sleec
        srlc._reset_sleecnorm_state()
        model, *_ = parse_sleec(spec, read_file=False)
        trace = _make_trace(3, [
            {"t": 1, "events": {"A"}, "measures": {}},
            {"t": 2, "events": {"A"}, "measures": {}},
            {"t": 3, "events": {"A"}, "measures": {}},
        ])
        verdict = srlc.RealizabilityChecker(
            model, N=3, model_str=spec
        ).check(trace)
        self.assertEqual(verdict.status, "unrealizable",
            "the mutualExclusive relation must be encoded in the per-component "
            "FOL* query, AND the short-circuit must be disabled because the "
            "component has a coupling relation")

    def test_measure_only_relation_is_global(self):
        """A measure invariant has empty event alphabet → global_relation_indices."""
        spec = textwrap.dedent("""
            def_start
                event A
                event R as system
                measure m: boolean
            def_end
            rule_start
                R1 when A then R within 5 seconds
            rule_end
            relation_start
                measure invariant {m}
            relation_end
        """)
        from sleec_decompose import decompose_with_relations
        from sleec_event_classification import classify_events_with_annotations
        m, rules, _A, _Acts, og_rules, _c, relations = _parse_norm(spec)
        ec = classify_events_with_annotations(m)
        d = decompose_with_relations(rules, og_rules, relations, ec)
        self.assertEqual(len(d.components), 1)
        self.assertEqual(d.components[0].relation_indices, [],
            "measure-only relations must NOT appear in the component's "
            "relation_indices (they are global)")
        self.assertEqual(d.global_relation_indices, [0],
            "the MeasureInv relation should be in global_relation_indices")


if __name__ == "__main__":
    unittest.main()
