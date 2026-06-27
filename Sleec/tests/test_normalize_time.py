"""Tests for tools/normalize_time.py.

Test-driven: written BEFORE the implementation. The tests encode the
contract:

  normalize_time(spec) -> (normalized_spec, gcd)

  1. The normalized spec parses through the SLEEC analyzer.
  2. All deadlines in the normalized spec are integers in seconds.
  3. The GCD returned divides every non-zero deadline + TimedEM
     duration in the input.
  4. Every non-zero deadline in the output equals
     (corresponding input deadline) / gcd.
  5. Idempotence: normalize_time(normalize_time(s)[0])[1] == 1.
  6. The realizability verdict is preserved (this is the load-bearing
     correctness property, tested empirically on a set of specs).
"""

import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
TOOLS = os.path.join(SLEEC, "tools")
for p in (SLEEC, ANALYZER, TOOLS):
    if p not in sys.path:
        sys.path.insert(0, p)

_CHECKER = os.path.join(SLEEC, "sleecRealizibilityCheck.py")


# =============================================================================
# Whitebox tests on normalize_time_str()
# =============================================================================

class TestNormalizeTimeBasics(unittest.TestCase):
    """Whitebox tests on the in-process normalize_time_str API."""

    def setUp(self):
        import normalize_time
        self.normalize = normalize_time.normalize_time_str

    def test_no_deadlines_at_all_returns_gcd_1(self):
        """A spec with only instantaneous (within 0 / no within) deadlines
        has no non-zero values to scale by; GCD defaults to 1."""
        spec = (
            "def_start\n"
            "  event A\n"
            "  event B\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B\n"
            "rule_end\n"
        )
        _, g = self.normalize(spec)
        self.assertEqual(g, 1)

    def test_single_deadline_in_minutes_gcd_is_that_deadline(self):
        """One rule with `within 5 minutes` (= 300 seconds): GCD=300."""
        spec = (
            "def_start\n"
            "  event A\n"
            "  event B\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 5 minutes\n"
            "rule_end\n"
        )
        new, g = self.normalize(spec)
        self.assertEqual(g, 300)
        # 300 / 300 = 1, output should have `within 1 seconds`
        self.assertIn("within 1 seconds", new)

    def test_all_minute_deadlines_gcd_is_60(self):
        """Multiple minute deadlines: GCD = 60 * gcd(integer parts)."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 5 minutes\n"
            "  R2 when A then C within 10 minutes\n"
            "rule_end\n"
        )
        # Deadlines in seconds: 300, 600 -> GCD = 300.
        new, g = self.normalize(spec)
        self.assertEqual(g, 300)
        self.assertIn("within 1 seconds", new)  # 300/300
        self.assertIn("within 2 seconds", new)  # 600/300

    def test_mixed_seconds_and_minutes(self):
        """Mixing seconds + minutes: GCD over actual seconds."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 5 seconds\n"
            "  R2 when A then C within 1 minutes\n"
            "rule_end\n"
        )
        # Deadlines: 5, 60. GCD = 5.
        new, g = self.normalize(spec)
        self.assertEqual(g, 5)
        self.assertIn("within 1 seconds", new)   # 5/5
        self.assertIn("within 12 seconds", new)  # 60/5

    def test_eventually_does_not_participate_in_gcd(self):
        """An `eventually` deadline is infinite; it does NOT lower GCD."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 10 minutes\n"
            "  R2 when A then C eventually\n"
            "rule_end\n"
        )
        # Only deadline contributing to GCD: 600. GCD = 600.
        _, g = self.normalize(spec)
        self.assertEqual(g, 600)

    def test_gcd_one_when_coprime_seconds(self):
        """When deadlines are coprime (no common factor), GCD = 1 -> no scaling."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 7 seconds\n"
            "  R2 when A then C within 11 seconds\n"
            "rule_end\n"
        )
        new, g = self.normalize(spec)
        self.assertEqual(g, 1)
        # Output should still contain both deadlines as-is.
        self.assertIn("within 7 seconds", new)
        self.assertIn("within 11 seconds", new)

    def test_hours_scale_correctly(self):
        """Hour deadlines convert to 3600 seconds each."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 1 hours\n"
            "  R2 when A then C within 2 hours\n"
            "rule_end\n"
        )
        # 3600 and 7200, GCD = 3600.
        new, g = self.normalize(spec)
        self.assertEqual(g, 3600)
        self.assertIn("within 1 seconds", new)  # 3600/3600
        self.assertIn("within 2 seconds", new)  # 7200/3600

    def test_timed_em_duration_also_scales(self):
        """`when E then phi for N seconds` durations participate in GCD too.

        SKIPPED: the current SLEEC grammar's TimedEM clause is
        syntactically ambiguous with UntilEM and does not parse in
        practice; the parser commits to UntilEM and fails before
        reaching `for`. The normalize_time tool's implementation
        walks every TimeValue regardless of context, so this test
        would pass automatically once TimedEM parsing is fixed
        upstream.
        """
        self.skipTest("TimedEM doesn't parse in current grammar (UntilEM "
                      "alternative shadows it)")

    def test_idempotence(self):
        """Normalizing twice gives the same result as normalizing once,
        i.e., a second normalize-pass has GCD = 1."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 1 minutes\n"
            "rule_end\n"
        )
        once, g1 = self.normalize(spec)
        twice, g2 = self.normalize(once)
        self.assertEqual(g1, 60)
        self.assertEqual(g2, 1)
        self.assertEqual(twice, once)


# =============================================================================
# Output validity tests
# =============================================================================

class TestNormalizedOutputParses(unittest.TestCase):
    """The normalized spec must remain a valid SLEEC spec the analyzer
    accepts. We test this both directly (parse_sleec) and end-to-end
    (the realizability CLI exits without parse errors)."""

    def setUp(self):
        import normalize_time
        self.normalize = normalize_time.normalize_time_str

    def _parse(self, spec_text):
        import sleecRealizibilityCheck as _rlz
        _rlz._reset_sleecnorm_state()
        from sleecParser import parse_sleec
        return parse_sleec(spec_text, read_file=False)

    def test_normalized_spec_parses_for_each_repo_spec(self):
        """Every .sleec spec in the repo: normalize and re-parse."""
        for spec_path in (
            os.path.join(SLEEC, "demo.sleec"),
            os.path.join(SLEEC, "experiments", "specs", "three_disjoint.sleec"),
            os.path.join(SLEEC, "experiments", "specs", "five_disjoint.sleec"),
            os.path.join(SLEEC, "experiments", "specs", "bridge_measure.sleec"),
            os.path.join(SLEEC, "experiments", "relation_specs", "happenBefore_env.sleec"),
            os.path.join(SLEEC, "experiments", "relation_specs", "until_em.sleec"),
        ):
            if not os.path.isfile(spec_path):
                continue
            with self.subTest(spec=os.path.basename(spec_path)):
                with open(spec_path) as f:
                    orig = f.read()
                new, g = self.normalize(orig)
                # Must round-trip through parse_sleec without error.
                try:
                    self._parse(new)
                except Exception as exc:
                    self.fail(
                        f"normalized spec ({spec_path}, g={g}) failed "
                        f"to parse:\n{exc}\n---\n{new[:500]}"
                    )


# =============================================================================
# Verdict equivalence (the load-bearing correctness test)
# =============================================================================

class TestVerdictPreservation(unittest.TestCase):
    """The verdict from --auto-bound on the original spec MUST equal the
    verdict on the normalized spec. This is the entire reason the
    transformation must be sound."""

    def setUp(self):
        import normalize_time
        self.normalize = normalize_time.normalize_time_str

    def _verdict(self, spec_text: str) -> str:
        """Run --auto-bound on the given spec text and return the verdict
        string (one of UNREALIZABLE / REALIZABLE / INCONCLUSIVE)."""
        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".sleec", delete=False) as f:
            f.write(spec_text)
            path = f.name
        try:
            r = subprocess.run(
                [sys.executable, _CHECKER, path,
                 "--auto-bound", "--quiet"],
                capture_output=True, text=True, timeout=120)
            self.assertNotIn("Traceback", r.stderr,
                f"unexpected error:\n{r.stderr[-500:]}")
            if "UNREALIZABLE" in r.stdout:
                return "UNREALIZABLE"
            if "REALIZABLE" in r.stdout:
                return "REALIZABLE"
            if "INCONCLUSIVE" in r.stdout:
                return "INCONCLUSIVE"
            self.fail(f"unexpected verdict output:\n{r.stdout[-500:]}")
        finally:
            os.unlink(path)

    def test_demo_realizable_or_unrealizable_preserved(self):
        """demo.sleec: same verdict before and after normalization."""
        with open(os.path.join(SLEEC, "demo.sleec")) as f:
            orig = f.read()
        new, _ = self.normalize(orig)
        v_orig = self._verdict(orig)
        v_new = self._verdict(new)
        self.assertEqual(v_orig, v_new,
            f"verdict mismatch on demo.sleec: orig={v_orig}, normalized={v_new}")

    def test_witness_env_realizable_preserved(self):
        """witness_env.sleec (REALIZABLE): preserved after normalization."""
        path = os.path.join(SLEEC, "experiments", "relation_specs",
                            "witness_env.sleec")
        if not os.path.isfile(path):
            self.skipTest("witness_env.sleec not in repo")
        with open(path) as f:
            orig = f.read()
        new, _ = self.normalize(orig)
        v_orig = self._verdict(orig)
        v_new = self._verdict(new)
        self.assertEqual(v_orig, v_new,
            f"verdict mismatch: orig={v_orig}, normalized={v_new}")

    def test_three_disjoint_realizable_preserved(self):
        """three_disjoint.sleec (REALIZABLE multi-component)."""
        path = os.path.join(SLEEC, "experiments", "specs",
                            "three_disjoint.sleec")
        if not os.path.isfile(path):
            self.skipTest("three_disjoint.sleec not in repo")
        with open(path) as f:
            orig = f.read()
        new, _ = self.normalize(orig)
        v_orig = self._verdict(orig)
        v_new = self._verdict(new)
        self.assertEqual(v_orig, v_new)

    def test_aspen_scaled_60x_preserves_verdict(self):
        """A minute-deadline spec: GCD=60 scales it 60x; verdict preserved."""
        spec = (
            "def_start\n"
            "  event A\n  event B\n  event C\n"
            "def_end\n"
            "rule_start\n"
            "  R1 when A then B within 4 minutes\n"
            "  R2 when A then not B within 2 minutes\n"
            "  R3 when B then C within 5 minutes\n"
            "  R4 when A then not C within 10 minutes\n"
            "rule_end\n"
        )
        new, g = self.normalize(spec)
        self.assertEqual(g, 60)  # All minute multiples; GCD = 60
        v_orig = self._verdict(spec)
        v_new = self._verdict(new)
        self.assertEqual(v_orig, v_new,
            f"verdict mismatch: orig={v_orig}, normalized={v_new}")


# =============================================================================
# CLI tests
# =============================================================================

class TestNormalizeTimeCli(unittest.TestCase):
    """The standalone tools/normalize_time.py CLI."""

    def test_cli_emits_normalized_spec_to_stdout(self):
        tool = os.path.join(SLEEC, "tools", "normalize_time.py")
        path = os.path.join(SLEEC, "demo.sleec")
        r = subprocess.run(
            [sys.executable, tool, path, "--quiet"],
            capture_output=True, text=True, timeout=30)
        self.assertEqual(r.returncode, 0, msg=r.stderr)
        self.assertIn("def_start", r.stdout)
        self.assertIn("rule_start", r.stdout)

    def test_cli_writes_to_output_path(self):
        tool = os.path.join(SLEEC, "tools", "normalize_time.py")
        path = os.path.join(SLEEC, "demo.sleec")
        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".sleec", delete=False) as f:
            out_path = f.name
        try:
            r = subprocess.run(
                [sys.executable, tool, path, "-o", out_path, "--quiet"],
                capture_output=True, text=True, timeout=30)
            self.assertEqual(r.returncode, 0, msg=r.stderr)
            with open(out_path) as f:
                content = f.read()
            self.assertIn("def_start", content)
        finally:
            os.unlink(out_path)


if __name__ == "__main__":
    unittest.main()
