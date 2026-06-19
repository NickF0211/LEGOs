"""Unit tests for tools/relation_json_to_sleec.py.

Covers:
 1. The mapping table — every JSON flag emits the documented SLEEC keyword.
 2. Edge cases — false outcomes, unknown outcomes, self-pairs,
    commutative de-duplication, missing operands, missing flag.
 3. The end-to-end round-trip — a generated .sleec file actually parses
    via the SLEEC analyzer and runs through --check-conflict cleanly
    (the converter's quality guarantee).
"""
import json
import os
import subprocess
import sys
import tempfile
import unittest

_THIS = os.path.dirname(os.path.abspath(__file__))
_SLEEC = os.path.dirname(_THIS)
_TOOL = os.path.join(_SLEEC, "tools", "relation_json_to_sleec.py")
_CHECKER = os.path.join(_SLEEC, "sleecRealizibilityCheck.py")

# Make the tool importable as a module for white-box tests.
sys.path.insert(0, os.path.join(_SLEEC, "tools"))
import relation_json_to_sleec as r2s  # noqa: E402


def _doc(*relationships, name="test_spec"):
    """Build a minimal relation.json document."""
    return {"name": name, "relations": [{"Relationship": r} for r in relationships]}


class TestFlagDispatch(unittest.TestCase):
    def test_event_witness_to_sleec_witness(self):
        out = r2s.render_relation("witness", "A", "B")
        self.assertEqual(out, "witness A B")

    def test_event_conflicts_to_sleec_mutualExclusive(self):
        out = r2s.render_relation("conflicts", "A", "B")
        self.assertEqual(out, "mutualExclusive A B")

    def test_event_HB_to_sleec_happenBefore(self):
        out = r2s.render_relation("HB", "A", "B")
        self.assertEqual(out, "happenBefore A B")

    def test_measure_implies_to_sleec_imply(self):
        out = r2s.render_relation("implies", "m1", "m2")
        self.assertEqual(out, "measure imply {m1} {m2}")

    def test_measure_equals_to_sleec_iff(self):
        out = r2s.render_relation("equals", "m1", "m2")
        self.assertEqual(out, "measure iff {m1} {m2}")

    def test_measure_ME_to_sleec_mutualExclusive(self):
        out = r2s.render_relation("ME", "m1", "m2")
        self.assertEqual(out, "measure mutualExclusive {m1} {m2}")


class TestConvertEmissions(unittest.TestCase):
    def test_true_outcome_is_emitted(self):
        doc = _doc({"event1": "A", "event2": "B", "witness": True,
                    "justification": "trivial"})
        text, warnings = r2s.convert(doc)
        self.assertIn("witness A B", text)
        self.assertEqual(warnings, [])

    def test_false_outcome_is_commented(self):
        doc = _doc({"event1": "A", "event2": "B", "witness": False,
                    "justification": "trivial"})
        text, _ = r2s.convert(doc)
        # A bare "witness A B" with no leading slash must NOT appear; only
        # commented forms.
        emitted = [ln.strip() for ln in text.splitlines()
                   if ln.strip() == "witness A B"]
        self.assertEqual(emitted, [], "false outcome must not emit live relation")
        self.assertIn("// witness A B", text)

    def test_unknown_outcome_is_commented_with_warning(self):
        doc = _doc({"event1": "A", "event2": "B", "witness": "{fill in}",
                    "justification": "trivial"})
        text, warnings = r2s.convert(doc)
        self.assertIn("// witness A B", text)
        self.assertEqual(len(warnings), 1)
        self.assertIn("UNKNOWN", text.upper())

    def test_self_pair_witness_emits_as_comment_trivially_true(self):
        doc = _doc({"event1": "A", "event2": "A", "witness": True,
                    "justification": "trivial"})
        text, _ = r2s.convert(doc)
        # The live "witness A A" line must not appear (self-pair is vacuous).
        self.assertNotIn("    witness A A\n", text)
        self.assertIn("trivially TRUE", text)

    def test_self_pair_conflicts_emits_as_comment_trivially_false_with_warning(self):
        doc = _doc({"event1": "A", "event2": "A", "conflicts": True,
                    "justification": "trivial"})
        text, warnings = r2s.convert(doc)
        self.assertNotIn("    mutualExclusive A A\n", text)
        self.assertIn("trivially FALSE", text)
        self.assertEqual(len(warnings), 1)

    def test_commutative_pair_dedupe(self):
        # ME is commutative — (m, n) and (n, m) should collapse to one line.
        doc = _doc(
            {"measure1": "m1", "measure2": "m2", "ME": True,
             "justification": "1"},
            {"measure1": "m2", "measure2": "m1", "ME": True,
             "justification": "2"},
        )
        text, _ = r2s.convert(doc)
        live = [ln for ln in text.splitlines()
                if ln.strip().startswith("measure mutualExclusive")]
        self.assertEqual(len(live), 1, f"expected 1 live ME line; got {live!r}")

    def test_non_commutative_pair_keeps_both_orders(self):
        # HB is NOT commutative — (a, b) and (b, a) must both appear.
        doc = _doc(
            {"event1": "A", "event2": "B", "HB": True, "justification": "1"},
            {"event1": "B", "event2": "A", "HB": True, "justification": "2"},
        )
        text, _ = r2s.convert(doc)
        live = [ln for ln in text.splitlines()
                if ln.strip().startswith("happenBefore")]
        self.assertEqual(len(live), 2,
                         f"expected 2 happenBefore lines for distinct directions; got {live!r}")
        self.assertIn("happenBefore A B", text)
        self.assertIn("happenBefore B A", text)

    def test_missing_operand_skipped_with_warning(self):
        doc = _doc({"event1": "A", "witness": True, "justification": "missing event2"})
        text, warnings = r2s.convert(doc)
        self.assertEqual(len(warnings), 1)
        self.assertNotIn("witness A", text.replace("//", ""))

    def test_missing_flag_skipped_with_warning(self):
        doc = _doc({"event1": "A", "event2": "B", "justification": "no flag"})
        _, warnings = r2s.convert(doc)
        self.assertEqual(len(warnings), 1)
        self.assertIn("no recognised", warnings[0])

    def test_event_and_measure_declarations_collected(self):
        doc = _doc(
            {"event1": "Hello", "event2": "World", "witness": True,
             "justification": ""},
            {"measure1": "a", "measure2": "b", "implies": True,
             "justification": ""},
        )
        text, _ = r2s.convert(doc)
        self.assertIn("event Hello", text)
        self.assertIn("event World", text)
        self.assertIn("measure a: boolean", text)
        self.assertIn("measure b: boolean", text)


class TestRoundTripThroughAnalyzer(unittest.TestCase):
    """The converter's quality bar: output must parse via the real analyzer
    and pass --check-conflict without exiting nonzero or printing a
    Python traceback."""

    @classmethod
    def setUpClass(cls):
        cls.tmpdir = tempfile.mkdtemp(prefix="rj2sleec_")

    def _convert_and_run_checker(self, doc, checker_args):
        json_path = os.path.join(self.tmpdir, "in.json")
        sleec_path = os.path.join(self.tmpdir, "out.sleec")
        with open(json_path, "w") as f:
            json.dump(doc, f)
        # Convert via subprocess so we exercise main() too.
        rc = subprocess.run(
            [sys.executable, _TOOL, json_path, "-o", sleec_path, "--quiet"],
            capture_output=True, text=True, timeout=10).returncode
        self.assertEqual(rc, 0, "converter exit 0 expected on clean input")
        # Now run the SLEEC checker over the generated spec.
        run = subprocess.run(
            [sys.executable, _CHECKER, sleec_path, *checker_args, "--quiet"],
            capture_output=True, text=True, timeout=60)
        self.assertNotIn("Traceback", run.stderr,
                         f"checker traceback on generated spec:\n{run.stderr[-600:]}")
        return run

    def test_parse_roundtrip_simple(self):
        doc = _doc(
            {"event1": "A", "event2": "B", "witness": True,
             "justification": ""},
            {"event1": "C", "event2": "B", "HB": True,
             "justification": ""},
        )
        run = self._convert_and_run_checker(doc, [])
        self.assertEqual(run.returncode, 0,
                         f"expected exit 0 from analyzer parse; got {run.returncode}")

    def test_check_conflict_runs_clean(self):
        doc = _doc(
            {"event1": "A", "event2": "B", "witness": True,
             "justification": ""},
            {"measure1": "m1", "measure2": "m2", "ME": True,
             "justification": ""},
        )
        run = self._convert_and_run_checker(doc, ["--check-conflict"])
        self.assertEqual(run.returncode, 0)
        self.assertIn("CONSISTENCY CONFLICT CHECK", run.stdout)

    def test_realistic_payload_almi_style(self):
        """A small ALMI-shaped payload that mixes all three event flags
        and two measure flags. Mirrors the actual upstream JSON shape."""
        doc = {"name": "almi_like", "relations": [
            {"Relationship": {"event1": "AllowUserToCook",
                              "event2": "MonitorMealTime",
                              "witness": True,
                              "justification": "user cooking implies meal monitoring"}},
            {"Relationship": {"event1": "UserHasLimitation",
                              "event2": "AllowUserToCook",
                              "conflicts": True,
                              "justification": "limitation conflicts with cooking"}},
            {"Relationship": {"event1": "PreparingDeployment",
                              "event2": "AgentDeployed",
                              "HB": True,
                              "justification": "preparation precedes deployment"}},
            {"Relationship": {"measure1": "alarmRestarts",
                              "measure2": "alarmOn",
                              "implies": True,
                              "justification": "restart implies on"}},
            {"Relationship": {"measure1": "userDisablesAlarm",
                              "measure2": "alarmOn",
                              "ME": True,
                              "justification": "disable means not on"}},
        ]}
        run = self._convert_and_run_checker(doc, ["--check-conflict"])
        self.assertEqual(run.returncode, 0)
        # And the static check should report "Not Conflicting" since
        # the relations don't actually contradict each other.
        self.assertIn("Not Conflicting", run.stdout)


if __name__ == "__main__":
    unittest.main()
