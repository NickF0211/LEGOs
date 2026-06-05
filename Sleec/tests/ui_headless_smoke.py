"""Headless harness for sleecFrontEnd.check_realizability.

Simulates the minimum Tk surface the function touches so we can verify
the rendering logic without popping a window or prompting for N. The
function reads the editor text via `aText.get(...)`, asks a user for the
horizon via `simpledialog.askinteger(...)`, and writes output to
`new_text.insert(...)` + `new_text.pack(...)` + `new_text.delete(...)`.

We replace each of those with a lightweight fake that records every
written fragment. The result is a single string per run.

Usage:
    python3 tests/ui_headless_smoke.py
"""

import os
import sys


# Ensure imports resolve.
HERE = os.path.dirname(os.path.abspath(__file__))
SLEEC = os.path.dirname(HERE)
ANALYZER = os.path.join(os.path.dirname(SLEEC), "Analyzer")
for p in (SLEEC, ANALYZER):
    if p not in sys.path:
        sys.path.insert(0, p)


# ------------------------------- Fakes --------------------------------------

class _Captured:
    def __init__(self):
        self.chunks = []  # list of (text, tag_or_None)
    def insert(self, _idx, text, *tags):
        tag = tags[0] if tags else None
        self.chunks.append((text, tag))
    def delete(self, *_a, **_k):
        self.chunks.clear()
    def pack(self, *_a, **_k):
        pass
    def tag_config(self, *_a, **_k):
        pass
    @property
    def text(self):
        return "".join(c for c, _ in self.chunks)
    def tag_summary(self):
        """Return dict tag -> list of distinct spans written with that tag."""
        summary = {}
        for text, tag in self.chunks:
            if tag is None:
                continue
            summary.setdefault(tag, []).append(text)
        return summary


class _FakeEditor:
    def __init__(self, src):
        self.src = src
    def get(self, *_a):
        return self.src


def _install_fakes(spec_text, horizon):
    """Monkeypatch sleecFrontEnd's globals so check_realizability runs headlessly."""
    # Patch tkinter.Tk.mainloop BEFORE importing sleecFrontEnd so
    # `lord.mainloop()` at module load doesn't block.
    import tkinter
    tkinter.Tk.mainloop = lambda self: None

    import sleecFrontEnd as fe
    captured = _Captured()
    fe.aText = _FakeEditor(spec_text)
    fe.new_text = captured

    # Patch dialogs: askinteger returns the horizon, showerror writes to stderr.
    import tkinter.simpledialog as sd
    import tkinter.messagebox as mb
    sd.askinteger = lambda *a, **k: horizon

    def _err(title, msg, **_):
        print(f"[error dialog] {title}: {msg}", file=sys.stderr)
    mb.showerror = _err

    return captured, fe


# ------------------------------- Runner -------------------------------------

def run(spec_path, horizon):
    with open(spec_path) as fh:
        src = fh.read()
    captured, fe = _install_fakes(src, horizon)
    fe.check_realizability()
    return captured


def main():
    specs = [
        ("demo.sleec",                        5),
        ("test.sleec",                        5),
        ("/tmp/twogroup.sleec",               3),
        ("experiments/specs/five_disjoint.sleec", 3),
        ("experiments/specs/bridge_cascade.sleec", 3),
    ]
    for rel, N in specs:
        path = rel if os.path.isabs(rel) else os.path.join(SLEEC, rel)
        if not os.path.isfile(path):
            print(f"SKIP {path!r}: not found")
            continue
        print("=" * 72)
        print(f"SPEC {rel}   N={N}")
        print("=" * 72)
        try:
            captured = run(path, N)
            output = captured.text
            tag_sum = captured.tag_summary()
        except Exception as e:
            print(f"ERROR: {type(e).__name__}: {e}")
            import traceback; traceback.print_exc()
            continue
        # Keep output concise for screenshotting — trim the body of the
        # partial trace and preserve the important banners.
        lines = output.splitlines()
        keep = []
        in_trace = False
        for ln in lines:
            if "Sampled partial trace" in ln:
                in_trace = True
                keep.append(ln)
                continue
            if in_trace:
                if ln.startswith("  at time") or ln.strip() == "":
                    if len(keep) < 200:
                        keep.append(ln)
                if "Verdict" in ln:
                    in_trace = False
            if not in_trace:
                keep.append(ln)
        # Dedupe consecutive blank lines.
        out = []
        for ln in keep:
            if ln == "" and out and out[-1] == "":
                continue
            out.append(ln)
        print("\n".join(out))
        print()
        # Show what tags were written for this spec.
        if tag_sum:
            print("-- Tag spans written --")
            for tag, spans in tag_sum.items():
                distinct = sorted(set(spans))
                print(f"  {tag}: {distinct}")
        print()


if __name__ == "__main__":
    main()
