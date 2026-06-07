# SLEEC-D — SLEEC normative requirements analyzer

A graphical and command-line tool for analyzing SLEEC normative
specifications. Built on top of the LEGOS FOL\* satisfiability checker.

## Install

### 1. Python dependencies

From the repository root (the directory containing `requirements.txt`,
NOT the `Sleec/` subdirectory):

```bash
cd /path/to/LEGOs        # the repo root
pip3 install -r requirements.txt
```

This installs `pysmt`, `z3-solver`, `textx`, `termcolor`, `ordered-set`,
and the supporting libraries.

### 2. Tk (for the GUI)

`tkinter` is a standard-library module but on some platforms requires a
separate OS package. **`pip install python-tk` does NOT work** — there
is no PyPI package by that name.

| OS | Install | Verify |
|---|---|---|
| macOS (Homebrew Python) | `brew install python-tk@3.12` (or your minor version) | `python3 -m tkinter` opens a small test window |
| Ubuntu / Debian | `sudo apt install python3-tk` | same |
| Fedora | `sudo dnf install python3-tkinter` | same |
| Windows (python.org installer) | already bundled | same |

If `python3 -m tkinter` opens the demo window, you have everything
needed.

## Launch the GUI

```bash
cd Sleec
python3 sleecFrontEnd.py
```

A window opens, preloaded with `test.sleec`. Edit the text in the top
pane to use a different spec.

### Buttons (top to bottom in the window)

| Button | What it does |
|---|---|
| `check redundancy` | Detects rules subsumed by others. |
| `check conflicts` | Detects pairs of rules that cannot be jointly satisfied. |
| `check concern` | Verifies declared concerns against the rules. |
| `check purpose` | Verifies declared purposes. |
| `check situational conflict` | Finds situations where rules conflict only under specific environment states. |
| `check realizability (bounded strong)` | Bounded realizability check. Prompts for horizon `N`. Returns REALIZABLE or UNREALIZABLE with the failing component, partial trace, and an obligation timeline. |

### What you should see when clicking a button

The bottom pane fills with output (rule citations, partial traces,
verdict banner). For situational-conflict and realizability checks,
relevant rule fragments are highlighted (yellow for triggers, red for
clashing heads).

## Example specs in this folder

- `test.sleec` — preloaded; the patient-care example used in the
  walkthroughs.
- `demo.sleec` — the paper's motivating example (emergency response).
- `experiments/annotated/*.sleec` — the same examples with explicit
  `event NAME as system|environment` annotations.
- `experiments/relation_specs/*.sleec` — small focused specs
  exercising every supported relation kind.

## CLI usage

For automation / CI gating:

```bash
cd Sleec
python3 sleecRealizibilityCheck.py demo.sleec --sample 5 --realizability-check
```

| Flag | Effect |
|---|---|
| `--sample N` | Sample at horizon N (required for realizability check). |
| `--realizability-check` | Run the bounded realizability check on the sampled trace. |
| `--decompose` | Partition rules into dependency components and check each independently. |
| `--weak` | Use bounded-weak semantics (strong is the default). |
| `--legacy-sampler` | Use the legacy `TraceSampler` instead of the default `AbstractTraceSampler`. |
| `--check-conflict` | Run the static **consistency-conflict** check (rule pairs with unsatisfiable conjunction). No `--sample` needed. |
| `--check-redundancy` | Run the static **redundancy** check (rules whose removal does not change the spec semantics). No `--sample` needed. |
| `--check-situational` | Run the static **situational-conflict** check (measure valuations under which two or more rules require contradictory responses). No `--sample` needed. |
| `--check-concern` | Run the static **concern** check against `concern_start ... concern_end`. Reports concerns the rules fail to address. No `--sample` needed. |
| `--check-purpose` | Run the static **purpose** check against `purpose_start ... purpose_end`. Reports purposes the rules fail to satisfy (i.e. rules that block intended behavior). No `--sample` needed. |
| `--quiet` | Suppress solver chatter. |

The five "static check" flags above replace the corresponding GUI
buttons (check redundancy / check conflicts / check concern / check
purpose / check situational conflict) and are the CLI alternative when
the GUI is unavailable. They can be combined freely — e.g.:

```bash
python3 sleecRealizibilityCheck.py demo.sleec \
    --check-conflict --check-redundancy --check-situational \
    --check-concern --check-purpose
```

| GUI button | CLI flag | Underlying check |
|---|---|---|
| check conflicts | `--check-conflict` | Two rules can never be jointly satisfied |
| check redundancy | `--check-redundancy` | A rule is implied by the others (could be removed) |
| check concern | `--check-concern` | Spec violates a declared `concern_start` clause |
| check purpose | `--check-purpose` | Spec blocks a declared `purpose_start` behavior |
| check situational conflict | `--check-situational` | Some measure valuation forces contradictory responses |
| check realizability (bounded strong) | `--realizability-check --sample N` | Adversarial environment can force a violation within horizon N |

Each emits a banner followed by the underlying analyzer's diagnostic
output. Exit code is `0` even when conflicts/redundancies/concerns are
found (the diagnostic is informational); `2` only on parse / file
errors.

Exit codes: `0` = REALIZABLE, `1` = UNREALIZABLE on at least one trace,
`2` = aborted (event-classification or relation-classification error).

For full flag help: `python3 sleecRealizibilityCheck.py --help`. The
table above lists the most-used flags; a few additional flags
(`--check`, `--skip`, `--no-rules`, `--no-roles`, `--normalize`,
`--k K`, `--abstract` (deprecated)) are documented in `--help`.

## Event annotations

Events can be explicitly tagged as system or environment in the
`def_start` block:

```
def_start
    event closingDoor as system
    event emergencyArrived as environment
def_end
```

Without annotations the classifier infers kinds:

1. **Annotation** — honored verbatim if present.
2. **Rule response** — any event appearing in any rule's response is
   `system`.
3. **Relation propagation** — events co-mentioned with a `system` event
   in a relation become `system` too.
4. **Default** — anything still unclassified becomes `environment`.

If an annotation contradicts (1)-(3) or a relation mixes system and
environment events in a way the analyzer can't handle, the run aborts
with a diagnostic.

## Running the test suite

After installing dependencies, you can verify the install by running
the unit and CLI integration tests:

```bash
cd Sleec

# Top-level unit tests (analyzer + checker logic):
python3 -m unittest test_sleecRealizibilityCheck.py

# Subdirectory tests (decomposition, sampler, classification, CLI smoke):
python3 -m unittest discover -s tests -p "test_*.py"
```

Both should report `OK`. The CLI smoke tests in particular invoke the
`sleecRealizibilityCheck.py` binary as a subprocess and assert the
exit codes and output strings match this README's claims, so a passing
suite means the documented CLI behavior is intact.

## Troubleshooting

### macOS: window opens but buttons don't respond

The Tk event loop on macOS is sensitive to two things:

1. **Long-running synchronous handlers.** Realizability checks invoke a
   SAT solver that can take seconds (or tens of seconds on large specs).
   During that time macOS may mark the window as unresponsive. **Wait
   30–60 seconds** before assuming it's hung. Watch the terminal for
   solver progress messages.

2. **`idlelib.percolator` ↔ Tk version mismatch.** On some Python builds
   the syntax-highlighter from `idlelib` interferes with mouse-click
   dispatch on the Text widget. If buttons fail to respond even with the
   terminal showing no activity, check your Python install:

   ```bash
   python3 --version
   python3 -c "import tkinter; print(tkinter.TkVersion, tkinter.TclVersion)"
   ```

   The recommended combination on macOS is Python from
   `brew install python@3.12` plus `brew install python-tk@3.12`. If you
   have a different combination and clicks still don't dispatch, run the
   CLI tool instead — it has identical analysis capabilities.

### `pip3 install python-tk` fails

This is expected. There is no `python-tk` package on PyPI. Use your OS
package manager (table above) to install Tk.

### "ImportError: No module named pysmt"

Run `pip3 install -r requirements.txt` from the repo root. If you have
multiple Python versions, make sure you're using the same one for both
install and run (`pip3` and `python3` should point to the same
interpreter; verify with `which pip3` and `which python3`).
