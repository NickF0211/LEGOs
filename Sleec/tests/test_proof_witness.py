"""
Tests for sleec_proof_witness — the FOL*-unsat-proof minimum-witness
extractor used by the bounded realizability diagnosis.

The witness extractor mirrors check_situational_conflict's structured
UNSAT-core attribution:

  * culprit RULES come from mapping the proof's UNSAT-core input ids
    back to source rules (NO regex on proof text);
  * essential ENV EVENTS / MEASURES are derived structurally by walking
    the culprit rules' trigger + condition textX ASTs and projecting the
    sampled trace onto the referenced symbols;
  * the CLASHING HEAD event(s) are the heads appearing with both
    polarities across the culprit rules.

Two layers of tests:

  1. Whitebox unit tests on the pure functions (symbol tables, id
     mapping, AST walks, trace projection) using small parsed specs and
     synthetic UNSAT cores — fast, no solver.
  2. Integration tests driving the full RealizabilityChecker on crafted
     specs with a KNOWN minimal conflict, asserting the witness narrows
     to exactly the culpable rules + symbols and EXCLUDES rules that fire
     but are not part of the conflict.
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


def _reset():
    import sleecRealizibilityCheck as srlc
    srlc._reset_sleecnorm_state()


def _parse(spec_text):
    """Parse spec text into a textX model (with clean global state)."""
    _reset()
    from sleecParser import parse_sleec
    import tempfile
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".sleec", delete=False) as f:
        f.write(spec_text)
        path = f.name
    try:
        model, *_ = parse_sleec(path, read_file=True)
        return model
    finally:
        os.unlink(path)


class _FakeInput:
    """Stand-in for a proof_reader.InputRule (carries only ``.id``)."""
    def __init__(self, id):
        self.id = id


# Small two-rule direct-conflict spec used across several tests.
DIRECT_CONFLICT = (
    "def_start\n"
    "    event A as environment\n"
    "    event B as system\n"
    "    measure m: boolean\n"
    "def_end\n"
    "rule_start\n"
    "    R1 when A then B\n"
    "    R2 when A and {m} then not B\n"
    "rule_end\n"
)


# =============================================================================
# 1. Symbol tables
# =============================================================================

class TestSymbolTables(unittest.TestCase):
    def test_event_kinds_classifies_declared_events(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        kinds = spw.event_kinds(model)
        self.assertEqual(kinds.get("A"), "environment")
        self.assertEqual(kinds.get("B"), "system")

    def test_measure_names_collects_all_measures(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        self.assertIn("m", spw.measure_names(model))

    def test_unannotated_event_kind_is_empty_string(self):
        import sleec_proof_witness as spw
        spec = (
            "def_start\n"
            "    event A\n"           # no kind annotation
            "    event B as system\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "rule_end\n"
        )
        model = _parse(spec)
        self.assertEqual(spw.event_kinds(model).get("A"), "")


class TestEnvironmentEventResolution(unittest.TestCase):
    """Environment events must be resolved even when UNANNOTATED — the
    common SLEEC case. An event is environment iff it is never a rule
    response head (only the env can produce it)."""

    UNANNOTATED = (
        "def_start\n"
        "    event Trigger\n"          # never a head -> environment
        "    event Resp\n"             # head of R1/R2 -> system
        "    measure g: boolean\n"
        "def_end\n"
        "rule_start\n"
        "    R1 when Trigger then Resp\n"
        "    R2 when Trigger and {g} then not Resp\n"
        "rule_end\n"
    )

    def test_structural_fallback_classifies_never_head_as_env(self):
        import sleec_proof_witness as spw
        model = _parse(self.UNANNOTATED)
        # No trace -> structural fallback (all events minus response heads).
        env = spw.environment_event_names(model, trace=None)
        self.assertIn("Trigger", env)
        self.assertNotIn("Resp", env)

    def test_trace_environment_events_is_authoritative(self):
        import sleec_proof_witness as spw
        model = _parse(self.UNANNOTATED)
        # The sampler's classification wins when present.
        trace = {"environment_events": ["Trigger"]}
        env = spw.environment_event_names(model, trace=trace)
        self.assertIn("Trigger", env)
        self.assertNotIn("Resp", env)

    def test_annotated_env_is_always_unioned(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)  # A is 'as environment'
        env = spw.environment_event_names(model, trace=None)
        self.assertIn("A", env)


# =============================================================================
# 2. Structured UNSAT-core -> culprit names
# =============================================================================

class TestMapUnsatCore(unittest.TestCase):
    def test_maps_ids_to_rule_and_relation_names(self):
        import sleec_proof_witness as spw
        id_to_source = {
            0: ("rule", "R_unused_property"),   # id 0 typically the property
            1: ("rule", "R1"),
            2: ("rule", "R2"),
            5: ("relation", "rel0"),
        }
        core = [_FakeInput(1), _FakeInput(2), _FakeInput(5)]
        rules, relations = spw.map_unsat_core(core, id_to_source)
        self.assertEqual(set(rules), {"R1", "R2"})
        self.assertEqual(relations, ["rel0"])

    def test_ids_absent_from_table_are_ignored(self):
        import sleec_proof_witness as spw
        # id 0 (property/trace) and id 99 (unknown) are not in the table.
        id_to_source = {1: ("rule", "R1")}
        core = [_FakeInput(0), _FakeInput(1), _FakeInput(99)]
        rules, relations = spw.map_unsat_core(core, id_to_source)
        self.assertEqual(rules, ["R1"])
        self.assertEqual(relations, [])

    def test_duplicates_are_removed(self):
        import sleec_proof_witness as spw
        id_to_source = {1: ("rule", "R1"), 2: ("rule", "R1")}
        core = [_FakeInput(1), _FakeInput(2)]
        rules, _ = spw.map_unsat_core(core, id_to_source)
        self.assertEqual(rules, ["R1"])

    def test_sort_rule_names_uses_spec_order(self):
        import sleec_proof_witness as spw
        order = ["R1", "R2", "R10", "R3"]
        out = spw.sort_rule_names(["R3", "R1", "R10"], order)
        self.assertEqual(out, ["R1", "R10", "R3"])

    def test_sort_rule_names_appends_unknowns_alphabetically(self):
        import sleec_proof_witness as spw
        out = spw.sort_rule_names(["Z", "R1", "A"], ["R1"])
        self.assertEqual(out, ["R1", "A", "Z"])


# =============================================================================
# 3. AST walks over culprit rules
# =============================================================================

class TestAstWalks(unittest.TestCase):
    def test_refs_in_trigger_condition_collects_env_event_and_measure(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        env_names = {n for n, k in spw.event_kinds(model).items()
                     if k == "environment"}
        m_names = spw.measure_names(model)
        # R2: when A and {m} then not B  -> env event A, measure m.
        r2 = {r.name: r for r in model.ruleBlock.rules}["R2"]
        events, measures = spw.refs_in_trigger_condition(r2, env_names, m_names)
        self.assertEqual(events, {"A"})
        self.assertEqual(measures, {"m"})

    def test_refs_ignores_system_event_trigger(self):
        import sleec_proof_witness as spw
        # R1's head B is a system event; trigger A is env. Walking R1's
        # trigger+condition must yield env event A only (B is in the
        # response, not the trigger/condition).
        model = _parse(DIRECT_CONFLICT)
        env_names = {n for n, k in spw.event_kinds(model).items()
                     if k == "environment"}
        m_names = spw.measure_names(model)
        r1 = {r.name: r for r in model.ruleBlock.rules}["R1"]
        events, measures = spw.refs_in_trigger_condition(r1, env_names, m_names)
        self.assertEqual(events, {"A"})
        self.assertEqual(measures, set())

    def test_refs_only_matches_declared_symbols(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        # Pass empty symbol tables: nothing should be collected even
        # though the AST has names — matching is table-driven, not
        # regex/heuristic.
        r2 = {r.name: r for r in model.ruleBlock.rules}["R2"]
        events, measures = spw.refs_in_trigger_condition(r2, set(), set())
        self.assertEqual(events, set())
        self.assertEqual(measures, set())

    def test_refs_collects_defeater_unless_guard_measure(self):
        import sleec_proof_witness as spw
        # 'unless {g}' puts measure g in the defeater guard, NOT in the
        # trigger/condition. It is essential to the conflict (the conflict
        # needs the defeater to NOT fire), so it must be collected.
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event B as system\n"
            "    measure g: boolean\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A then not B unless {g}\n"
            "rule_end\n"
        )
        model = _parse(spec)
        env_names = {n for n, k in spw.event_kinds(model).items()
                     if k == "environment"}
        m_names = spw.measure_names(model)
        r2 = {r.name: r for r in model.ruleBlock.rules}["R2"]
        events, measures = spw.refs_in_trigger_condition(r2, env_names, m_names)
        self.assertEqual(events, {"A"})
        self.assertIn("g", measures)

    def test_conflict_heads_detects_both_polarity_head(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        by = {r.name: r for r in model.ruleBlock.rules}
        # R1 -> B (positive), R2 -> not B (negative).  Clash on B.
        heads = spw.conflict_heads([by["R1"], by["R2"]])
        self.assertEqual(heads, ["B"])

    def test_conflict_heads_empty_when_no_clash(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        by = {r.name: r for r in model.ruleBlock.rules}
        # R1 alone has only a positive head -> no clash.
        self.assertEqual(spw.conflict_heads([by["R1"]]), [])


# =============================================================================
# 4. Trace projection (build_env_witness)
# =============================================================================

class TestBuildEnvWitness(unittest.TestCase):
    def _trace(self):
        return {
            "rules_fired": [("R1", 1), ("R2", 1), ("R3", 2)],
            "per_step": [
                {"t": 1, "events": {"A"},
                 "measures": {"m": True, "irrelevant": False}},
                {"t": 2, "events": {"C"},
                 "measures": {"m": False}},
            ],
        }

    def test_projects_only_essential_symbols_at_culprit_steps(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        by = {r.name: r for r in model.ruleBlock.rules}
        env_names = {n for n, k in spw.event_kinds(model).items()
                     if k == "environment"}
        m_names = spw.measure_names(model)
        env, measures = spw.build_env_witness(
            [by["R1"], by["R2"]], self._trace(),
            env_names, m_names, ["R1", "R2"],
        )
        # Culprit rules fire at t=1; essential env event A, measure m.
        self.assertEqual(env, {1: ["A"]})
        self.assertEqual(measures, {1: {"m": True}})
        # t=2 (where only R3 fires) is excluded.
        self.assertNotIn(2, env)
        self.assertNotIn(2, measures)

    def test_irrelevant_measure_is_dropped(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        by = {r.name: r for r in model.ruleBlock.rules}
        env_names = {n for n, k in spw.event_kinds(model).items()
                     if k == "environment"}
        m_names = spw.measure_names(model)
        _, measures = spw.build_env_witness(
            [by["R1"], by["R2"]], self._trace(),
            env_names, m_names, ["R1", "R2"],
        )
        self.assertNotIn("irrelevant", measures.get(1, {}))


# =============================================================================
# 5. build_witness integration (parsed model + synthetic core)
# =============================================================================

class TestBuildWitness(unittest.TestCase):
    def test_assembles_full_witness_from_core(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        # property=id0; complete_rules: R1->id1, R2->id2.
        id_to_source = {1: ("rule", "R1"), 2: ("rule", "R2")}
        core = [_FakeInput(0), _FakeInput(1), _FakeInput(2)]
        trace = {
            "rules_fired": [("R1", 1), ("R2", 1)],
            "per_step": [
                {"t": 1, "events": {"A"}, "measures": {"m": True}},
            ],
        }
        w = spw.build_witness(model, core, id_to_source, trace)
        self.assertEqual(w.rules, ["R1", "R2"])
        self.assertEqual(w.conflict_events, ["B"])
        self.assertEqual(w.env_events, {1: ["A"]})
        self.assertEqual(w.measures, {1: {"m": True}})
        self.assertFalse(w.is_empty())

    def test_highlights_are_stored_and_deduped(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        id_to_source = {1: ("rule", "R1"), 2: ("rule", "R2")}
        core = [_FakeInput(1), _FakeInput(2)]
        trace = {"rules_fired": [("R1", 1)], "per_step": [
            {"t": 1, "events": {"A"}, "measures": {}}]}
        # Pass duplicate/unsorted spans; expect sorted-unique on the witness.
        w = spw.build_witness(model, core, id_to_source, trace,
                              highlights=[(10, 20), (5, 8), (10, 20)])
        self.assertEqual(w.highlights, [(5, 8), (10, 20)])

    def test_highlights_default_empty(self):
        import sleec_proof_witness as spw
        model = _parse(DIRECT_CONFLICT)
        w = spw.build_witness(model, [_FakeInput(1)],
                              {1: ("rule", "R1")},
                              {"rules_fired": [], "per_step": []})
        self.assertEqual(w.highlights, [])


# =============================================================================
# 6. End-to-end via RealizabilityChecker
# =============================================================================

class TestEndToEndWitness(unittest.TestCase):
    """Drive the full checker on crafted specs with a KNOWN minimal
    conflict and assert the witness narrows correctly."""

    def _check(self, spec_text, N=2, decompose=True):
        import sleecRealizibilityCheck as srlc
        _reset()
        from sleecParser import parse_sleec
        import tempfile
        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".sleec", delete=False) as f:
            f.write(spec_text)
            path = f.name
        try:
            model, *_ = parse_sleec(path, read_file=True)
            sampler = srlc.AbstractTraceSampler(model, N=N, verbose=False)
            trace = sampler.next_trace()
            checker = srlc.RealizabilityChecker(
                model, N=N, model_str=spec_text,
                mode="strong", decompose=decompose,
                record_proof=True,  # these tests exercise the proof witness
            )
            return checker.check(trace, verbose=False)
        finally:
            os.unlink(path)

    def test_direct_conflict_narrows_to_two_rules(self):
        v = self._check(DIRECT_CONFLICT)
        self.assertEqual(v.status, "unrealizable")
        self.assertIsNotNone(v.witness)
        self.assertEqual(set(v.witness.rules), {"R1", "R2"})
        self.assertEqual(v.witness.conflict_events, ["B"])

    def test_witness_excludes_firing_but_irrelevant_rule(self):
        # R3 fires (C is env) but is NOT part of the B-conflict; it must
        # be excluded from the minimal witness.
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event C as environment\n"
            "    event B as system\n"
            "    event D as system\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A then not B\n"
            "    R3 when C then D\n"
            "rule_end\n"
        )
        v = self._check(spec)
        self.assertEqual(v.status, "unrealizable")
        self.assertIsNotNone(v.witness)
        self.assertEqual(set(v.witness.rules), {"R1", "R2"})
        self.assertNotIn("R3", v.witness.rules)
        # D (R3's head) must not be flagged as a conflict event.
        self.assertEqual(v.witness.conflict_events, ["B"])

    def test_witness_env_events_only_essential(self):
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event C as environment\n"
            "    event B as system\n"
            "    event D as system\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A then not B\n"
            "    R3 when C then D\n"
            "rule_end\n"
        )
        v = self._check(spec)
        # The essential env event is A (drives the B clash); C is not.
        all_env = set()
        for evs in v.witness.env_events.values():
            all_env |= set(evs)
        self.assertIn("A", all_env)
        self.assertNotIn("C", all_env)

    def test_measure_gated_conflict_reports_measure(self):
        # The clash only arises when {m} holds (R2 is conditioned on m).
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event B as system\n"
            "    measure m: boolean\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A and {m} then not B\n"
            "rule_end\n"
        )
        v = self._check(spec)
        self.assertEqual(v.status, "unrealizable")
        all_measures = set()
        for d in v.witness.measures.values():
            all_measures |= set(d.keys())
        self.assertIn("m", all_measures)

    def test_unless_defeater_conflict_reports_guard_measure(self):
        # End-to-end: 'unless {g}' gates the clash. The witness must
        # narrow to {R1,R2}, flag head B, and report g (the defeater
        # guard) as an essential measure.
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event B as system\n"
            "    measure g: boolean\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A then not B unless {g}\n"
            "rule_end\n"
        )
        v = self._check(spec)
        self.assertEqual(v.status, "unrealizable")
        self.assertEqual(set(v.witness.rules), {"R1", "R2"})
        self.assertEqual(v.witness.conflict_events, ["B"])
        all_measures = set()
        for d in v.witness.measures.values():
            all_measures |= set(d.keys())
        self.assertIn("g", all_measures)

    def test_unannotated_env_event_appears_in_witness(self):
        # Regression: UNANNOTATED trigger events (no 'as environment')
        # must still surface in the witness. Mirrors the cascade
        #   r2: PatientFallen -> CallSupport
        #   r3: PatientFallen -> ProvideCompanionship unless {patientNotDeaf}
        #   r4: CallSupport   -> not ProvideCompanionship
        # The essential env event PatientFallen has no annotation.
        spec = (
            "def_start\n"
            "    event PatientFallen\n"
            "    event CallSupport\n"
            "    event ProvideCompanionship\n"
            "    measure patientNotDeaf: boolean\n"
            "def_end\n"
            "rule_start\n"
            "    r2 when PatientFallen then CallSupport\n"
            "    r3 when PatientFallen then ProvideCompanionship "
            "unless {patientNotDeaf}\n"
            "    r4 when CallSupport then not ProvideCompanionship\n"
            "rule_end\n"
        )
        v = self._check(spec, N=1)
        self.assertEqual(v.status, "unrealizable")
        self.assertEqual(set(v.witness.rules), {"r2", "r3", "r4"})
        self.assertEqual(v.witness.conflict_events, ["ProvideCompanionship"])
        all_env = set()
        for evs in v.witness.env_events.values():
            all_env |= set(evs)
        self.assertIn("PatientFallen", all_env)

    def test_proof_highlights_populated_and_within_culprit_rules(self):
        # The witness must carry proof-driven source-highlight spans
        # (get_high_light over the minimized derivation), and each span
        # must fall inside one of the culprit rules' source ranges.
        spec = (
            "def_start\n"
            "    event A as environment\n"
            "    event B as system\n"
            "def_end\n"
            "rule_start\n"
            "    R1 when A then B\n"
            "    R2 when A then not B\n"
            "rule_end\n"
        )
        import sleecRealizibilityCheck as srlc
        v = self._check(spec, N=2)
        self.assertEqual(v.status, "unrealizable")
        self.assertTrue(v.witness.highlights,
                        "expected non-empty proof-driven highlights")
        # Build culprit rule source ranges from the model.
        srlc._reset_sleecnorm_state()
        from sleecParser import parse_sleec
        import tempfile, os
        with tempfile.NamedTemporaryFile(
                mode="w", suffix=".sleec", delete=False) as f:
            f.write(spec); path = f.name
        try:
            model, *_ = parse_sleec(path, read_file=True)
        finally:
            os.unlink(path)
        ranges = [(r._tx_position, r._tx_position_end)
                  for r in model.ruleBlock.rules
                  if r.name in set(v.witness.rules)]
        for (s, e) in v.witness.highlights:
            self.assertTrue(
                any(rs <= s and e <= re for (rs, re) in ranges),
                f"highlight span ({s},{e}) not within any culprit rule")
        # The clashing event B must be among the highlighted texts.
        spec_text = spec
        hl_texts = {spec_text[s:e].strip().strip("{}")
                    for (s, e) in v.witness.highlights}
        self.assertIn("B", hl_texts)


if __name__ == "__main__":
    unittest.main()
