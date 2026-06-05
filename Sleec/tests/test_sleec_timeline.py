"""Unit tests for sleec_timeline.build_timeline.

These tests exercise the timeline builder end-to-end on synthetic specs,
asserting that the generated grid text and tagged spans reflect the
expected obligations and conflicts.
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
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()
    from SleecNorm import parse_sleec_norm
    return parse_sleec_norm(spec_text, read_file=False)


def _make_trace(rules_fired, env_events, bool_measures=(), per_step=None, N=3):
    """Build the minimum trace-dict shape that build_timeline reads."""
    if per_step is None:
        per_step = [
            {"t": t, "events": set(env_events), "measures": {}}
            for t in range(1, N + 1)
        ]
    return {
        "N": N,
        "per_step": per_step,
        "rules_fired": list(rules_fired),
        "environment_events": list(env_events),
        "bool_measures": list(bool_measures),
        "num_measures": [],
        "scalar_measures": [],
    }


class TestBuildTimeline(unittest.TestCase):

    def test_empty_rules_fired_gives_no_sys_rows(self):
        """No firings -> no SYS rows, no conflicts."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 5 seconds
            rule_end
        """)
        _m, rules, _Am, _Acts, _og, _c, _rel = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace([], env_events=["A"], N=3)
        grid, spans = build_timeline(rules, trace, culprit_names=set())

        self.assertIn("-- Obligation timeline --", grid)
        self.assertNotIn("SYS  ", grid)       # no SYS lane
        self.assertNotIn("⚠", grid)           # no conflicts
        # No culprit or conflict tags (trigger_event tags on the env
        # lane label are always present and harmless).
        self.assertFalse(any(t == "culprit_rule" for _, _, t in spans))
        self.assertFalse(any(t == "conflict" for _, _, t in spans))

    def test_single_positive_obligation_no_conflict(self):
        """One rule fires; positive head shown; no conflict."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 3 seconds
            rule_end
        """)
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace([("R1", 1)], env_events=["A"], N=3)
        grid, spans = build_timeline(rules, trace, culprit_names=set())

        self.assertIn("SYS  B", grid)
        self.assertIn("[R1]", grid)
        self.assertNotIn("⚠", grid)
        # No culprits -> no culprit_rule tags.
        self.assertFalse(any(tag == "culprit_rule" for _, _, tag in spans))

    def test_negative_obligation_renders_with_prefix(self):
        """A rule with 'then not X' should render as '¬X' in the SYS lane."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then not B within 3 seconds
            rule_end
        """)
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace([("R1", 1)], env_events=["A"], N=3)
        grid, _spans = build_timeline(rules, trace, culprit_names=set())

        self.assertIn("¬B", grid)
        self.assertNotIn("⚠", grid)

    def test_head_conflict_produces_warn_cells(self):
        """Two rules on the same head with opposite polarity trigger ⚠ cells."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 3 seconds
                R2 when A then not B within 3 seconds
            rule_end
        """)
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace([("R1", 1), ("R2", 1)], env_events=["A"], N=3)
        grid, spans = build_timeline(
            rules, trace, culprit_names={"R1", "R2"}
        )

        self.assertIn("⚠", grid)
        # Conflict tag spans present.
        self.assertTrue(any(t == "conflict" for _, _, t in spans))
        # Culprit rule names tagged in cells.
        self.assertTrue(any(t == "culprit_rule" for _, _, t in spans))

    def test_cascade_closure_expands_to_downstream_rule(self):
        """If R1's head is R2's trigger, firing R1 should bring R2 into the SYS view."""
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
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        # Only R1 fires from the seed (A is env).  Cascade should add R2.
        trace = _make_trace([("R1", 1)], env_events=["A"], N=3)
        grid, _spans = build_timeline(rules, trace, culprit_names=set())

        self.assertIn("SYS  B", grid)
        self.assertIn("SYS  C", grid)
        self.assertIn("[R1]", grid)
        self.assertIn("[R2]", grid)

    def test_culprit_tag_only_on_failing_rule(self):
        """Culprit highlighting is applied only to rules in culprit_names."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
                event C
                event D
            def_end
            rule_start
                R1 when A then B within 3 seconds
                R2 when C then D within 3 seconds
            rule_end
        """)
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace(
            [("R1", 1), ("R2", 1)],
            env_events=["A", "C"],
            N=3,
        )
        # Mark only R1 culprit.
        _grid, spans = build_timeline(
            rules, trace, culprit_names={"R1"}
        )

        rule_spans = [s for s in spans if s[2] == "culprit_rule"]
        # Every culprit_rule span text should be "R1" (index via the grid
        # text).
        grid_text, _ = build_timeline(rules, trace, culprit_names={"R1"})
        for start, end, tag in rule_spans:
            self.assertEqual(grid_text[start:end], "R1",
                f"expected 'R1' but got {grid_text[start:end]!r}")

    def test_big_window_extends_past_horizon(self):
        """Obligations with deadlines past N should render overshoot columns."""
        spec = textwrap.dedent("""
            def_start
                event A
                event B
            def_end
            rule_start
                R1 when A then B within 10 seconds
            rule_end
        """)
        _m, rules, *_ = _parse_norm(spec)

        from sleec_timeline import build_timeline
        trace = _make_trace([("R1", 1)], env_events=["A"], N=3)
        grid, _ = build_timeline(rules, trace, culprit_names=set())

        # Overshoot markers '·' should appear in the header.
        self.assertIn("·", grid)
        # The obligation should appear past t=3.
        self.assertIn("t=4·", grid)


if __name__ == "__main__":
    unittest.main()
