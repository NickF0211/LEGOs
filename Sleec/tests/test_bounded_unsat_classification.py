"""
Regression tests for the realizability result classification:

  check_property_refining returns
    * tuple -> SAT            -> verdict "realizable"
    * 0     -> genuine UNSAT  -> verdict "unrealizable"
    * 2     -> "bounded UNSAT" (volume bound exceeded) -> "inconclusive"
    * -1    -> iteration budget exhausted               -> "inconclusive"

Bounded/exhausted results must NOT be reported as unrealizable — they are
UNKNOWN. This was a real soundness bug: a large monolithic query tripped
the volume bound and was mis-reported as UNREALIZABLE while the same spec
was REALIZABLE under --decompose.

We test the classification deterministically by monkeypatching
analyzer.check_property_refining to return each sentinel, rather than
relying on a spec that happens to trip the volume bound.
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER):
    if p not in sys.path:
        sys.path.insert(0, p)

# A spec with a polarity clash (R1: A->B, R2: A->not B) so the component is
# actually SOLVED via check_property_refining (not short-circuited as
# "realizable by inspection"). That lets the monkeypatched return value drive
# the classification under test.
SPEC = (
    "def_start\n"
    "    event A as environment\n"
    "    event B as system\n"
    "def_end\n"
    "rule_start\n"
    "    R1 when A then B\n"
    "    R2 when A then not B\n"
    "rule_end\n"
)


class TestResultClassification(unittest.TestCase):
    def _verdict_with_solver_returning(self, sentinel):
        """Run the checker with analyzer.check_property_refining patched to
        return ``sentinel`` for the (single) component solve."""
        import sleecRealizibilityCheck as srlc
        srlc._reset_sleecnorm_state()
        from sleecParser import parse_sleec
        import analyzer
        import tempfile

        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".sleec", delete=False) as f:
            f.write(SPEC)
            path = f.name
        orig = analyzer.check_property_refining
        try:
            model, *_ = parse_sleec(path, read_file=True)
            trace = srlc.AbstractTraceSampler(
                model, N=2, verbose=False).next_trace()
            # Force a polarity-clash-free spec to actually be SOLVED (not
            # short-circuited "realizable by inspection") by disabling
            # decomposition: the monolithic component is always solved.
            analyzer.check_property_refining = lambda *a, **k: sentinel
            checker = srlc.RealizabilityChecker(
                model, N=2, model_str=SPEC, mode="strong",
                decompose=False, record_proof=False,
            )
            return checker.check(trace, verbose=False)
        finally:
            analyzer.check_property_refining = orig
            os.unlink(path)

    def test_genuine_unsat_zero_is_unrealizable(self):
        v = self._verdict_with_solver_returning(0)
        self.assertEqual(v.status, "unrealizable")

    def test_bounded_unsat_two_is_inconclusive(self):
        v = self._verdict_with_solver_returning(2)
        self.assertEqual(v.status, "inconclusive")

    def test_iteration_exhausted_minus_one_is_inconclusive(self):
        v = self._verdict_with_solver_returning(-1)
        self.assertEqual(v.status, "inconclusive")

    def test_sat_tuple_is_realizable(self):
        # A 2-tuple stands in for the solver's (model, ...) SAT return.
        v = self._verdict_with_solver_returning(({}, {}))
        self.assertEqual(v.status, "realizable")

    def test_inconclusive_has_no_culprit_or_witness(self):
        v = self._verdict_with_solver_returning(2)
        self.assertEqual(v.culprit_rules, [])
        self.assertIsNone(v.witness)


if __name__ == "__main__":
    unittest.main()
