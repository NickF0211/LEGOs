"""Tests for the ALO blocker.

Two sampler implementations exist:
  - AbstractTraceSampler (default; --abstract): block() already operated
    at the (rule, step) level via per-rule assumption variables. This
    file verifies that behavior.
  - TraceSampler (legacy, --no-abstract): block() previously operated at
    the env-event level only, missing measure-driven adversarial traces.
    Today's change brings it in line with AbstractTraceSampler by
    blocking on satisfied soft clauses (env_var AND condition).

Coverage:
  1. AbstractTraceSampler enumerates measure-driven distinct traces.
  2. AbstractTraceSampler's block() returns False on saturation.
  3. TraceSampler also enumerates measure-driven distinct traces under
     the new soft-clause blocking (regression test for the fix).
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


# Spec: two rules whose conditions partition the measure space. Same env
# event Trig at every step. Without rule-firing-level blocking, only one
# of the two rules would ever be sampled.
SPEC_MEASURE_PARTITION = textwrap.dedent("""
    def_start
        event Trig
        event A as system
        measure m: boolean
    def_end
    rule_start
        R1 when Trig and {m} then A within 0 seconds
        R2 when Trig and (not {m}) then A within 0 seconds
    rule_end
""")


class TestAbstractTraceSamplerBlocker(unittest.TestCase):
    """AbstractTraceSampler: block() uses self.assumption_vars (per-rule,
    per-step Boolean). It always blocked at the (rule, step) level."""

    def test_enumerates_measure_driven_distinct_traces(self):
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(SPEC_MEASURE_PARTITION),
                                            N=2, verbose=False)
        seen = set()
        for _ in range(5):
            trace = sampler.next_trace()
            if trace is None:
                break
            seen.add(frozenset(trace["rules_fired"]))
            if not sampler.block(trace):
                break
        self.assertGreaterEqual(
            len(seen), 2,
            f"expected at least 2 distinct rule-firing patterns; saw "
            f"{len(seen)}: {seen}",
        )

    def test_block_returns_false_when_saturated(self):
        spec = textwrap.dedent("""
            def_start
                event Trig
                event A as system
            def_end
            rule_start
                R1 when Trig then A within 0 seconds
            rule_end
        """)
        import sleecRealizibilityCheck as srlc
        sampler = srlc.AbstractTraceSampler(_parse(spec), N=2, verbose=False)
        trace = sampler.next_trace()
        self.assertIsNotNone(trace)
        # The trivial rule R1 has no condition; assumption is True at every
        # step; trace must fire it at every step. block() therefore exhausts.
        self.assertFalse(sampler.block(trace),
            "block() should return False once every assumption is satisfied")


class TestTraceSamplerBlocker(unittest.TestCase):
    """TraceSampler: block() now uses self.rule_soft (per-(rule, step)
    soft clause = env_var AND condition). Verifies the fix from this
    session: previously it blocked env-event presence only and missed
    measure-driven adversarial traces."""

    def test_enumerates_measure_driven_distinct_traces(self):
        import sleecRealizibilityCheck as srlc
        sampler = srlc.TraceSampler(_parse(SPEC_MEASURE_PARTITION),
                                    N=2, verbose=False)
        seen = set()
        for _ in range(5):
            trace = sampler.next_trace()
            if trace is None:
                break
            seen.add(frozenset(trace["rules_fired"]))
            if not sampler.block(trace):
                break
        self.assertGreaterEqual(
            len(seen), 2,
            f"TraceSampler with the new ALO must enumerate at least 2 "
            f"distinct rule-firing patterns; saw {len(seen)}: {seen}",
        )


if __name__ == "__main__":
    unittest.main()
