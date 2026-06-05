"""UI smoke-test for friendly error rendering and relation-spec
parsing.

Verifies that the Tk frontend (sleecFrontEnd.check_realizability) :
  - parses specs with `event NAME as system|environment` annotations,
  - parses specs with relation blocks (witness, mutualExclusive, etc.),
  - on RelationClassificationError (sys+measure relation): renders a
    friendly headline plus the diagnostic, with NO Python traceback.
  - on EventClassificationError (annotated env event used as response):
    same friendly handling.

Uses the headless harness from ui_headless_smoke that monkey-patches
Tk's mainloop and substitutes fake widgets capturing every insert().
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


def _write_spec(text):
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".sleec")
    os.write(fd, text.encode("utf-8"))
    os.close(fd)
    return path


def _run(spec_text, N):
    """Write spec to disk, run UI on it, return captured output text."""
    from ui_headless_smoke import run
    p = _write_spec(spec_text)
    try:
        return run(p, N).text
    finally:
        os.unlink(p)


class TestFriendlyErrorRendering(unittest.TestCase):

    def test_event_classification_error_no_traceback(self):
        spec = textwrap.dedent("""
            def_start
                event A as environment
            def_end
            rule_start
                R1 when A then A within 5 seconds
            rule_end
        """)
        out = _run(spec, 3)
        self.assertIn("Event-classification conflict", out)
        self.assertIn("annotated_env_but_response", out)
        # The fix: NO traceback string should leak into the user-visible output.
        self.assertNotIn("Traceback", out)

    def test_relation_classification_error_no_traceback(self):
        spec = textwrap.dedent("""
            def_start
                event Trig
                event ClosingDoor as system
                measure doorClosed: boolean
            def_end
            rule_start
                R1 when Trig then ClosingDoor within 1 seconds
            rule_end
            relation_start
                causation ClosingDoor {doorClosed}
            relation_end
        """)
        out = _run(spec, 3)
        self.assertIn("Unsupported relation kind", out)
        self.assertIn("system events with measures", out)
        self.assertNotIn("Traceback", out)


class TestRelationSpecsRender(unittest.TestCase):
    """Verify the UI renders cleanly on each relation kind."""

    def _check(self, spec, N, expect_verdict=None):
        out = _run(spec, N)
        # No traceback anywhere.
        self.assertNotIn("Traceback", out, f"unexpected traceback in:\n{out[:800]}")
        # Standard sections present.
        self.assertTrue("Partial trace" in out or "trace" in out.lower())
        self.assertTrue("Rule decomposition" in out or "component" in out.lower())
        self.assertTrue("Obligation timeline" in out)
        if expect_verdict == "REAL":
            self.assertIn("REALIZABLE", out)
        elif expect_verdict == "UNREAL":
            self.assertIn("UNREALIZABLE", out)

    def test_witness_relation_renders(self):
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
        self._check(spec, N=4, expect_verdict="REAL")

    def test_mutex_relation_renders(self):
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
        self._check(spec, N=4, expect_verdict="REAL")

    def test_until_em_relation_renders(self):
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
        self._check(spec, N=4, expect_verdict="REAL")


if __name__ == "__main__":
    unittest.main()
