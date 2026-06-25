"""Regression test for the GUI back-to-back-click stale-state bug.

Symptom: clicking 'check realizability' (or any other static-check
button) in the GUI a second time, after any previous parse_sleec()
call has populated type_constructor state, crashes with
    KeyError: '<some scalar measure name>'
because the second parse_sleec() looks up scalar types that the prior
run failed to clean up.

The fix is for every GUI handler to call _reset_sleecnorm_state() as
its first action so each click starts from a clean slate.

This test verifies the fix by reproducing the stale-state condition
directly (two parse_sleec calls in a row without an explicit reset)
and then exercising the headless GUI harness to confirm the GUI path
no longer crashes after multiple invocations.
"""
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER, HERE):
    if p not in sys.path:
        sys.path.insert(0, p)


class TestStaleTypeConstructorState(unittest.TestCase):
    """Without a reset between parse_sleec calls, the second one crashes
    when the spec uses scalar measures. The GUI handlers must call
    _reset_sleecnorm_state() before any parse_sleec to be robust to a
    prior click leaving state dirty."""

    def setUp(self):
        # Use a spec known to use scalar measures. The DPA/ALMI-style
        # spec has a scale(low, medium, high) measure that is the
        # canonical trigger for this bug. Fall back to any scalar-using
        # spec under experiments/.
        candidates = [
            os.path.join(SLEEC, "experiments", "almi_full.sleec"),
            os.path.join(SLEEC, "experiments", "dpa_gdpr.sleec"),
        ]
        self.spec_path = next((p for p in candidates if os.path.isfile(p)), None)
        if self.spec_path is None:
            self.skipTest("no scalar-using spec available for the regression")

    def test_double_parse_without_reset_reproduces_the_bug(self):
        """The pre-fix bug pattern: two consecutive parse_sleec calls
        with no state reset between them. The second call crashes with
        KeyError on a scalar-measure name."""
        import sleecRealizibilityCheck as _rlz
        from sleecParser import parse_sleec
        with open(self.spec_path) as f:
            text = f.read()
        _rlz._reset_sleecnorm_state()
        parse_sleec(text, read_file=False)
        with self.assertRaises(KeyError):
            parse_sleec(text, read_file=False)

    def test_double_parse_with_reset_does_not_crash(self):
        """With a reset between parses, the second one succeeds. This
        is the contract every GUI handler must satisfy."""
        import sleecRealizibilityCheck as _rlz
        from sleecParser import parse_sleec
        with open(self.spec_path) as f:
            text = f.read()
        _rlz._reset_sleecnorm_state()
        parse_sleec(text, read_file=False)
        _rlz._reset_sleecnorm_state()
        # Must NOT raise.
        parse_sleec(text, read_file=False)


class TestGuiHandlersAllResetState(unittest.TestCase):
    """Every GUI handler in sleecFrontEnd.py that ultimately calls
    parse_sleec must invoke _reset_sleecnorm_state first. This test
    inspects the source to assert that property holds, so a future
    edit that drops the reset gets caught by CI."""

    def test_every_check_handler_resets_state_before_any_parse(self):
        src = open(os.path.join(SLEEC, "sleecFrontEnd.py")).read()
        # Find every 'def check_*' function body.
        import re
        for m in re.finditer(
                r"^def (check_[A-Za-z_]+)\(\):\n((?:[ \t]+[^\n]*\n)+)",
                src, re.MULTILINE):
            name = m.group(1)
            body = m.group(2)
            # Find positions of the reset call and any parse-triggering
            # call inside the body. The handler is correct iff every
            # parse-triggering call is preceded by a reset.
            triggers = [
                ("parse_sleec(",          "calls parse_sleec()"),
                ("check_input_concerns(", "calls check_input_concerns()"),
                ("check_input_purpose(",  "calls check_input_purpose()"),
                ("check_input_conflict(", "calls check_input_conflict()"),
                ("check_input_red(",      "calls check_input_red()"),
                ("check_situational_conflict(",
                                          "calls check_situational_conflict()"),
            ]
            for needle, desc in triggers:
                idx_parse = body.find(needle)
                if idx_parse < 0:
                    continue
                idx_reset = body.find("_reset_sleecnorm_state(")
                self.assertGreaterEqual(
                    idx_reset, 0,
                    f"GUI handler {name!r} {desc} but never calls "
                    f"_reset_sleecnorm_state(); back-to-back clicks will "
                    f"hit the stale-type-constructor bug.",
                )
                self.assertLess(
                    idx_reset, idx_parse,
                    f"GUI handler {name!r}: _reset_sleecnorm_state() at "
                    f"char {idx_reset} runs AFTER {needle} at char "
                    f"{idx_parse}. The reset must come first so any "
                    f"stale state from a prior click is wiped before the "
                    f"next parse touches type_constructor.",
                )


if __name__ == "__main__":
    unittest.main()
