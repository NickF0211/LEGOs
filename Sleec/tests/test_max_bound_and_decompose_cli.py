"""Unit tests for tools/compute_max_bound.py and tools/decompose_to_sleec.py."""

import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, os.path.join(SLEEC, "tools")):
    if p not in sys.path:
        sys.path.insert(0, p)

import sleecRealizibilityCheck as _rlz  # noqa
_rlz._reset_sleecnorm_state()

from SleecNorm import parse_sleec_norm  # noqa
import compute_max_bound  # noqa


# -----------------------------------------------------------------------------
# Bound detector
# -----------------------------------------------------------------------------

class TestComputeBmax(unittest.TestCase):

    def _b_max_for(self, spec_text):
        _rlz._reset_sleecnorm_state()
        _m, nr, _AM, _A, _og, _c, rels = parse_sleec_norm(spec_text,
                                                          read_file=False)
        return compute_max_bound.compute_b_max(nr, rels)

    def test_minimal_spec_one_rule_zero_deadline(self):
        spec = """
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B
rule_end
"""
        r = self._b_max_for(spec)
        self.assertFalse(r["has_eventually"])
        self.assertEqual(r["T_max"], 0)
        self.assertEqual(r["rule_count"], 1)
        self.assertEqual(r["h_size"], 1)
        # (0 + 2)^1 * 1 = 2
        self.assertEqual(r["b_max"], 2)

    def test_finite_deadline_lifts_T_max(self):
        spec = """
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B within 5 seconds
rule_end
"""
        r = self._b_max_for(spec)
        self.assertEqual(r["T_max"], 5)
        # (5 + 2)^1 * 1 = 7
        self.assertEqual(r["b_max"], 7)

    def test_eventually_returns_infinity(self):
        spec = """
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B eventually
rule_end
"""
        r = self._b_max_for(spec)
        self.assertTrue(r["has_eventually"])
        self.assertEqual(r["b_max"], float("inf"))

    def test_multiple_rules_exponent_in_R(self):
        spec = """
def_start
  event A
  event B
  event C
def_end
rule_start
  R1 when A then B within 3 seconds
  R2 when B then C within 3 seconds
rule_end
"""
        r = self._b_max_for(spec)
        self.assertEqual(r["T_max"], 3)
        self.assertEqual(r["rule_count"], 2)
        self.assertEqual(r["h_size"], 1)
        # (3 + 2)^2 * 1 = 25
        self.assertEqual(r["b_max"], 25)

    def test_minutes_normalized_to_seconds(self):
        spec = """
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B within 2 minutes
rule_end
"""
        r = self._b_max_for(spec)
        # 2 minutes = 120 seconds
        self.assertEqual(r["T_max"], 120)
        # (120 + 2)^1 * 1 = 122
        self.assertEqual(r["b_max"], 122)

    def test_happenBefore_doubles_H(self):
        spec = """
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B within 0 seconds
rule_end
relation_start
  happenBefore A B
relation_end
"""
        r = self._b_max_for(spec)
        self.assertEqual(r["c_hb"], 1)
        self.assertEqual(r["h_size"], 2)
        # (0 + 2)^1 * 2 = 4
        self.assertEqual(r["b_max"], 4)

    def test_multiple_happenBefore_compose_multiplicatively(self):
        spec = """
def_start
  event A
  event B
  event C
def_end
rule_start
  R1 when A then B within 0 seconds
  R2 when B then C within 0 seconds
rule_end
relation_start
  happenBefore A B
  happenBefore B C
relation_end
"""
        r = self._b_max_for(spec)
        self.assertEqual(r["c_hb"], 2)
        # 2 hb + 0 un -> |H| = 2^2 = 4
        self.assertEqual(r["h_size"], 4)
        self.assertEqual(r["b_max"], 16)  # (0+2)^2 * 4


# -----------------------------------------------------------------------------
# CLI integration tests
# -----------------------------------------------------------------------------

_CHECKER = os.path.join(SLEEC, "sleecRealizibilityCheck.py")
_BOUND_TOOL = os.path.join(SLEEC, "tools", "compute_max_bound.py")
_DECOMP_TOOL = os.path.join(SLEEC, "tools", "decompose_to_sleec.py")


class TestCliIntegration(unittest.TestCase):

    def test_realizability_cli_max_bound_flag(self):
        """--max-bound on the main CLI prints B_max and exits 0."""
        demo = os.path.join(SLEEC, "demo.sleec")
        r = subprocess.run(
            [sys.executable, _CHECKER, demo, "--max-bound", "--quiet"],
            capture_output=True, text=True, timeout=30)
        self.assertEqual(r.returncode, 0)
        self.assertIn("B_max", r.stdout)
        # demo.sleec: 3 rules, T_max=5 -> (5+2)^3 = 343
        self.assertIn("343", r.stdout)
        self.assertNotIn("Traceback", r.stderr)

    def test_bound_tool_eventually_exits_one(self):
        """The standalone bound tool exits 1 when the bound is infinite."""
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".sleec", delete=False) as f:
            f.write("""
def_start
  event A
  event B
def_end
rule_start
  R1 when A then B eventually
rule_end
""")
            path = f.name
        try:
            r = subprocess.run(
                [sys.executable, _BOUND_TOOL, path],
                capture_output=True, text=True, timeout=10)
            self.assertEqual(r.returncode, 1)
            self.assertIn("infinity", r.stdout)
        finally:
            os.unlink(path)

    def test_decompose_tool_writes_files(self):
        """The decompose tool writes one .sleec file per component."""
        demo = os.path.join(SLEEC, "demo.sleec")
        with tempfile.TemporaryDirectory() as tmpdir:
            r = subprocess.run(
                [sys.executable, _DECOMP_TOOL, demo, "-o", tmpdir, "-q"],
                capture_output=True, text=True, timeout=10)
            self.assertEqual(r.returncode, 0, msg=r.stderr)
            files = sorted(os.listdir(tmpdir))
            self.assertEqual(len(files), 1)  # demo is one component
            self.assertTrue(files[0].startswith("demo_component_"))
            self.assertTrue(files[0].endswith(".sleec"))

            # File must contain a valid SLEEC structure.
            with open(os.path.join(tmpdir, files[0])) as f:
                content = f.read()
            self.assertIn("def_start", content)
            self.assertIn("def_end", content)
            self.assertIn("rule_start", content)
            self.assertIn("rule_end", content)
            self.assertIn("callEmergencyServices", content)

    def test_decompose_tool_stdout_when_no_output_dir(self):
        """Without -o, decompose tool prints to stdout with component header."""
        demo = os.path.join(SLEEC, "demo.sleec")
        r = subprocess.run(
            [sys.executable, _DECOMP_TOOL, demo, "-q"],
            capture_output=True, text=True, timeout=10)
        self.assertEqual(r.returncode, 0, msg=r.stderr)
        self.assertIn("Component 1", r.stdout)
        self.assertIn("def_start", r.stdout)
        self.assertIn("rule_start", r.stdout)

    def test_decompose_handles_relation_wrappers(self):
        """A spec with relations must produce a parseable per-component file.

        Regression test: parse_sleec_norm returns relations as wrapper
        objects (EventRelation, UntilEMRelation, Causation, ...) that
        do NOT carry textX positions directly — they expose the
        underlying textX node via ``.reference``. The decompose tool
        must unwrap via ``.reference`` for both source extraction and
        AST walking; otherwise the generated ``relation_start`` block
        ends up empty and fails to parse (the grammar requires
        relations+=Relation+).
        """
        # Use a relation_specs file that exercises every wrapper kind
        # we care about (EventRelation with witness/happenBefore,
        # UntilEMRelation, Causation, Effect/Forbid).
        for rel_spec in [
            "experiments/relation_specs/witness_env.sleec",
            "experiments/relation_specs/happenBefore_env.sleec",
            "experiments/relation_specs/causation_env.sleec",
            "experiments/relation_specs/forbid_env.sleec",
            "experiments/relation_specs/until_em.sleec",
        ]:
            spec_path = os.path.join(SLEEC, rel_spec)
            if not os.path.isfile(spec_path):
                continue
            with self.subTest(spec=rel_spec):
                with tempfile.TemporaryDirectory() as tmpdir:
                    r = subprocess.run(
                        [sys.executable, _DECOMP_TOOL, spec_path,
                         "-o", tmpdir, "-q"],
                        capture_output=True, text=True, timeout=10)
                    self.assertEqual(r.returncode, 0, msg=r.stderr)
                    files = sorted(os.listdir(tmpdir))
                    self.assertGreaterEqual(len(files), 1)
                    for fname in files:
                        with open(os.path.join(tmpdir, fname)) as f:
                            content = f.read()
                        # Sanity: file should not have an empty
                        # relation_start/end block (would fail parse).
                        if "relation_start" in content:
                            block = content.split("relation_start", 1)[1]
                            block = block.split("relation_end", 1)[0]
                            # Block should have non-whitespace content.
                            stripped = block.strip()
                            self.assertTrue(
                                stripped,
                                f"{fname}: empty relation_start/end block "
                                f"would fail to parse",
                            )
                        # End-to-end: the realizability CLI must parse it.
                        sleec_path = os.path.join(tmpdir, fname)
                        parse = subprocess.run(
                            [sys.executable, _CHECKER, sleec_path,
                             "--quiet", "--no-rules", "--no-roles"],
                            capture_output=True, text=True, timeout=30)
                        self.assertEqual(
                            parse.returncode, 0,
                            f"{fname}: realizability CLI failed to parse "
                            f"the generated component "
                            f"(rc={parse.returncode}; "
                            f"stderr={parse.stderr[-300:]})",
                        )


class TestLoudFailureSemantics(unittest.TestCase):
    """The tools must FAIL LOUDLY on malformed inputs rather than silently
    producing degraded output. This catches the entire class of "silent
    fall-through" bugs that would otherwise produce unsound bounds or
    unparseable per-component specs."""

    def test_compute_b_max_raises_on_normalized_rule_without_oc(self):
        """A NormalizedRule lacking .oc breaks the contract; raise instead
        of silently treating its deadlines as 0."""
        class _FakeNR:
            oc = None  # Missing obligation chain.

        with self.assertRaises(RuntimeError) as ctx:
            compute_max_bound.compute_b_max([_FakeNR()], [])
        self.assertIn("obligation chain", str(ctx.exception))

    def test_compute_b_max_raises_on_unparseable_deadline(self):
        """A deadline that does not stringify to an integer is a
        normalization bug; surface it loudly."""
        class _FakeDeadline:
            def is_inf(self): return False
            def is_inst(self): return False
            class _End:
                def __str__(self): return "not-an-int"
            end = _End()
        class _FakeObg:
            deadline = _FakeDeadline()
            head = None
        class _FakeCobg:
            obligation = _FakeObg()
        class _FakeOC:
            obligations = [_FakeCobg()]
        class _FakeNR:
            oc = _FakeOC()

        with self.assertRaises(RuntimeError) as ctx:
            compute_max_bound.compute_b_max([_FakeNR()], [])
        self.assertIn("could not parse deadline", str(ctx.exception))

    def test_compute_b_max_raises_on_timedEM_missing_duration(self):
        """TimedEM relations missing a duration would silently drop a
        contribution to |H|; raise loudly so callers know."""
        class _FakeTimedEM:
            pass
        _FakeTimedEM.__name__ = "TimedEMRelation"

        with self.assertRaises(RuntimeError) as ctx:
            compute_max_bound.compute_b_max([], [_FakeTimedEM()])
        self.assertIn("duration", str(ctx.exception))


if __name__ == "__main__":
    unittest.main()