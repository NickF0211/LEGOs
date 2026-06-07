"""CLI integration smoke tests.

Invokes `sleecRealizibilityCheck.py` as a subprocess (the way a user
runs it from the terminal) and asserts on exit code + key output
strings. Catches bugs that unit-test-level calls miss, including:

  - verbose-mode code paths (unit tests run with verbose=False),
  - argparse + main() wiring,
  - exit code semantics documented in the README,
  - stderr error reporting,
  - --help output completeness vs README claims.

These are slower (~1s per test, subprocess overhead) but they exercise
exactly what a user types at the terminal. The README's CLI examples
should all pass these tests.

History: the line-1519 NameError that crashed every realizability
check in verbose mode was caught only by manual user testing (and a
fresh-user-walkthrough subagent). A CLI smoke suite would have caught
it before any user saw it. This file fills that gap.
"""

import os
import subprocess
import sys
import tempfile
import textwrap
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC_DIR = os.path.dirname(HERE)
ANALYZER_DIR = os.path.join(os.path.dirname(SLEEC_DIR), "Analyzer")
CLI_PATH = os.path.join(SLEEC_DIR, "sleecRealizibilityCheck.py")


def _run(*args, timeout: int = 60) -> subprocess.CompletedProcess:
    """Invoke the CLI with the given args. Returns the completed process
    with `stdout` and `stderr` captured as strings.

    `cwd` is set to the Sleec/ directory so relative spec paths in the
    args resolve the same way they would for a user.
    """
    env = os.environ.copy()
    # Ensure both Sleec/ and Analyzer/ are on PYTHONPATH so the CLI's
    # `from sleecParser import ...` lines resolve regardless of where
    # the test runner was invoked from.
    py = env.get("PYTHONPATH", "")
    extra = f"{SLEEC_DIR}{os.pathsep}{ANALYZER_DIR}"
    env["PYTHONPATH"] = f"{extra}{os.pathsep}{py}" if py else extra
    return subprocess.run(
        [sys.executable, CLI_PATH, *args],
        cwd=SLEEC_DIR,
        capture_output=True,
        text=True,
        timeout=timeout,
        env=env,
    )


class TestRealizabilityCLI(unittest.TestCase):
    """Tests for the README's CLI examples and exit-code claims."""

    def test_demo_unrealizable_verbose(self):
        """Run the README's first example command exactly as written
        (no --quiet). The line-1519 NameError bug crashed this case.
        Must exit 1 with UNREALIZABLE banner and no Python traceback."""
        r = _run("demo.sleec", "--sample", "5", "--realizability-check")
        self.assertEqual(r.returncode, 1,
            f"expected exit 1 (UNREAL); got {r.returncode}\n"
            f"stdout tail: {r.stdout[-400:]}\n"
            f"stderr tail: {r.stderr[-400:]}")
        self.assertIn("UNREALIZABLE", r.stdout,
            "expected UNREALIZABLE banner in stdout")
        # Most important regression check: no Python traceback in stderr.
        self.assertNotIn("Traceback", r.stderr,
            f"unexpected traceback in stderr:\n{r.stderr[-800:]}")
        self.assertNotIn("NameError", r.stderr + r.stdout,
            "NameError leaked")

    def test_demo_unrealizable_quiet(self):
        """Same as above but with --quiet. Same verdict, less output.
        --quiet was the only configuration that worked before the fix."""
        r = _run("demo.sleec", "--sample", "5", "--realizability-check",
                 "--quiet")
        self.assertEqual(r.returncode, 1)
        self.assertIn("UNREALIZABLE", r.stdout)
        self.assertNotIn("Traceback", r.stderr)

    def test_realizable_spec_exits_zero(self):
        """A spec where every sampled trace is realizable must exit 0.
        witness_env.sleec is a small env-only relation spec."""
        r = _run("experiments/relation_specs/witness_env.sleec",
                 "--sample", "4", "--realizability-check")
        self.assertEqual(r.returncode, 0,
            f"expected exit 0 (REAL); got {r.returncode}\n"
            f"stdout tail: {r.stdout[-400:]}")
        self.assertIn("REALIZABLE", r.stdout)
        self.assertNotIn("Traceback", r.stderr)

    def test_unsupported_relation_exits_two(self):
        """A spec coupling a system event to a measure (Causation S {m})
        is not yet supported by the realizability check. Must abort with
        exit 2 and a friendly diagnostic, no traceback."""
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
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".sleec", delete=False
        ) as fh:
            fh.write(spec)
            spec_path = fh.name
        try:
            r = _run(spec_path, "--sample", "3", "--realizability-check",
                     "--quiet")
        finally:
            os.unlink(spec_path)
        self.assertEqual(r.returncode, 2,
            f"expected exit 2 (ABORT); got {r.returncode}")
        self.assertIn("system events with measures", r.stderr,
            "expected diagnostic about sys+measure relation")
        self.assertNotIn("Traceback", r.stderr)

    def test_event_classification_conflict_exits_two(self):
        """An event annotated as environment but used in a rule's response
        is an ANNOTATED_ENV_BUT_RESPONSE conflict. Must abort with exit
        2 and a friendly diagnostic, no traceback."""
        spec = textwrap.dedent("""
            def_start
                event A as environment
            def_end
            rule_start
                R1 when A then A within 5 seconds
            rule_end
        """)
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".sleec", delete=False
        ) as fh:
            fh.write(spec)
            spec_path = fh.name
        try:
            r = _run(spec_path, "--sample", "3", "--realizability-check",
                     "--quiet")
        finally:
            os.unlink(spec_path)
        self.assertEqual(r.returncode, 2)
        self.assertIn("annotated_env_but_response", r.stderr.lower())
        self.assertNotIn("Traceback", r.stderr)

    def test_help_lists_documented_flags(self):
        """Every flag the README documents must appear in --help output.
        Catches drift between README and actual CLI."""
        r = _run("--help")
        self.assertEqual(r.returncode, 0)
        readme_flags = [
            "--sample",
            "--realizability-check",
            "--decompose",
            "--weak",
            "--legacy-sampler",
            "--quiet",
            "--check-conflict",
            "--check-redundancy",
            "--check-situational",
            "--check-concern",
            "--check-purpose",
        ]
        for flag in readme_flags:
            self.assertIn(flag, r.stdout,
                f"--help output is missing the {flag!r} flag documented "
                f"in the README")

    def test_sample_without_realizability_check(self):
        """`--sample N` without `--realizability-check` should sample a
        partial trace and print it, then exit 0. Not a verdict, just
        a trace."""
        r = _run("demo.sleec", "--sample", "3", "--quiet")
        self.assertEqual(r.returncode, 0,
            f"expected exit 0; got {r.returncode}\n"
            f"stderr: {r.stderr[-400:]}")
        # Partial trace should appear in stdout.
        self.assertIn("partial trace", r.stdout.lower(),
            "expected a partial-trace section in stdout")
        self.assertIn("t=1", r.stdout,
            "expected per-step lines starting at t=1")
        self.assertNotIn("Traceback", r.stderr)

    def test_static_checks_demo_combined(self):
        """All five static-check flags should run without crash on
        demo.sleec, even when combined in a single invocation. Each
        underlying check_input_* function internally re-parses the
        spec; the dispatch must reset module-level state between calls
        so the second/third/etc. parse doesn't hit stale type-constructor
        state."""
        r = _run("demo.sleec",
                 "--check-conflict", "--check-redundancy",
                 "--check-concern", "--check-purpose",
                 "--check-situational", "--quiet")
        self.assertEqual(r.returncode, 0,
            f"expected exit 0; got {r.returncode}\n"
            f"stderr: {r.stderr[-600:]}")
        self.assertNotIn("Traceback", r.stderr)
        for banner in ("CONSISTENCY CONFLICT CHECK", "REDUNDANCY CHECK",
                       "CONCERN CHECK", "PURPOSE CHECK",
                       "SITUATIONAL CONFLICT CHECK"):
            self.assertIn(banner, r.stdout,
                f"expected banner {banner!r} in stdout when all five "
                f"static checks are requested")


if __name__ == "__main__":
    unittest.main()
