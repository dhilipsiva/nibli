//! Integration tests for the nibli-engine: full pipeline (parse → compile → reason).
//!
//! Each test creates a fresh NibliEngine, asserts Lojban text, and queries with proof.
//! No WASM, no HTTP — exercises nibli-kr+nibli-semantics+nibli-reason directly via Rust crate calls.

use nibli_engine::{
    EngineAggregateOp, EngineComputeRequest, EngineError, EngineLogicBuffer, EngineLogicNode,
    EngineLogicalTerm, EngineQueryResult, NibliEngine,
};
use nibli_render::{
    DRUG_INTERACTIONS_OVERLAY, GDPR_OVERLAY, Register, render_collapsed_text_with,
    summarize_proof_with,
};
use nibli_store::NibliStore;
use std::fs;
use std::path::{Path, PathBuf};

/// A fresh KR-mode engine (the suite was machine-ported from Lojban at THE
/// DROP — per-literal Lojban→`nibli_kr::render` conversion, the corpora-twins
/// equality guarantee held at the port).
fn fresh_engine() -> NibliEngine {
    NibliEngine::new()
}

/// `NibliEngine::open` (see `fresh_engine`).
fn fresh_open(path: &Path, expect_msg: &str) -> NibliEngine {
    NibliEngine::open(path).expect(expect_msg)
}

/// Helper: create a fresh engine, assert multiple lines, return the engine.
fn engine_with_facts(lines: &[&str]) -> NibliEngine {
    let engine = fresh_engine();
    for line in lines {
        engine
            .assert_text(line)
            .unwrap_or_else(|e| panic!("Failed to assert '{}': {}", line, e));
    }
    engine
}

fn assert_true(result: &EngineQueryResult, msg: &str) {
    assert!(result.is_true(), "{msg}: got {result:?}");
}

fn assert_false(result: &EngineQueryResult, msg: &str) {
    assert!(result.is_false(), "{msg}: got {result:?}");
}

fn temp_db_path(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join("nibli_engine_integration_tests");
    fs::create_dir_all(&dir).unwrap();
    dir.join(format!("{name}.redb"))
}

/// Find the named Neo-Davidsonian role predicate (e.g. `klama_x4`) in the typed
/// `LogicBuffer` and return its argument list. `compile_debug` returns the typed
/// IR, so we walk nodes instead of substring-matching an S-expr string.
fn find_role<'a>(buf: &'a EngineLogicBuffer, role: &str) -> Option<&'a [EngineLogicalTerm]> {
    buf.nodes.iter().find_map(|n| match n {
        EngineLogicNode::Predicate((rel, args)) if rel == role => Some(args.as_slice()),
        _ => None,
    })
}

/// True if the named role predicate exists and one of its argument places is the
/// constant `value`. Used to assert which place a term landed in.
fn role_has_const(buf: &EngineLogicBuffer, role: &str, value: &str) -> bool {
    find_role(buf, role).is_some_and(|args| {
        args.iter()
            .any(|t| matches!(t, EngineLogicalTerm::Constant(c) if c == value))
    })
}

fn cleanup(path: &Path) {
    let _ = fs::remove_file(path);
}

// ─── Basic assertion and query ──────────────────────────────────────

#[test]
fn simple_assertion_and_query() {
    let engine = engine_with_facts(&["big(some dog)."]);
    let (holds, trace, json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_true(&holds, "Query for asserted fact should hold");
    assert!(!trace.is_empty(), "Proof trace should be non-empty");
    assert!(!json.is_empty(), "Proof JSON should be non-empty");
}

#[test]
fn simple_negation_query_false() {
    let engine = engine_with_facts(&["big(some dog)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("big(some cat).").unwrap();
    assert_false(&holds, "Query for unasserted fact should not hold");
}

// ─── du (identity) equivalence through the surface pipeline (G-M1) ───

#[test]
fn equals_surface_equivalence_transfers_fact() {
    // la .coumadin. cu du la .varfarin.  (brand name == generic name)
    // la .coumadin. cu xukmi             (Coumadin is a drug)
    // ? la .varfarin. cu xukmi           → TRUE via du-equivalence transfer.
    let engine = engine_with_facts(&["Coumadin = Varfarin.", "chemical(Coumadin)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("chemical(Varfarin).").unwrap();
    assert_true(
        &holds,
        "chemical should transfer from Coumadin to Varfarin via surface du",
    );
}

#[test]
fn equals_surface_equivalence_is_symmetric() {
    // Assert the fact about the SECOND name, query the FIRST.
    let engine = engine_with_facts(&["Coumadin = Varfarin.", "chemical(Varfarin)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("chemical(Coumadin).").unwrap();
    assert_true(&holds, "du equivalence is symmetric");
}

#[test]
fn equals_surface_negative_control() {
    // No du link → no transfer.
    let engine = engine_with_facts(&["chemical(Coumadin)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("chemical(Varfarin).").unwrap();
    assert_false(&holds, "without du, the fact must not transfer");
}

#[test]
fn equals_over_numeric_literals() {
    // `du` (identity) over `li` number literals resolves by reflexivity with nothing
    // asserted: identical literals are TRUE, distinct literals FALSE. Pins the resolved
    // sub-part (c) of the former "numeric-group only covers ∃-query" item — the
    // surface-du fix made `du` reachable and the du-query arm's `args[0] == args[1]`
    // short-circuit handles identical `GroundTerm::Number` operands. Constant
    // reflexivity is the sanity peer.
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("1 = 1.").unwrap(),
        "1 du 1 must be TRUE by reflexivity",
    );
    assert_false(
        &engine.query_holds("1 = 2.").unwrap(),
        "1 du 2 must be FALSE (distinct literals, nothing asserted)",
    );
    assert_true(
        &engine.query_holds("Djan = Djan.").unwrap(),
        "constant reflexivity sanity: djan du djan must be TRUE",
    );
}

#[test]
fn not_equals_surface_contradiction() {
    // Asserting both an identity and an inequality for the same pair is flagged.
    let engine = engine_with_facts(&["Djan = Jan.", "~Djan = Jan."]);
    let violations = engine.check_contradictions();
    assert!(
        violations
            .iter()
            .any(|v| v.contains("Inequality contradiction")),
        "du + na du for the same pair must be flagged: {violations:?}"
    );
}

// ─── Cooperative cancellation ───────────────────────────────────────

#[test]
fn engine_cancel_flag_aborts_query() {
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    // With the cancel flag pre-set, every query path returns Err instead of
    // running to completion. This is the hook the native server's watchdog
    // uses to free a blocking thread when the request timeout elapses.
    let engine = engine_with_facts(&["dog(Adam).", "animal(every dog)."]);
    let flag = Arc::new(AtomicBool::new(true));
    engine.set_cancel_flag(flag.clone());

    let proof = engine.query_text_with_proof("animal(Adam).");
    assert!(
        proof.is_err(),
        "cancelled proof query must Err, got {proof:?}"
    );
    assert!(
        proof
            .unwrap_err()
            .to_string()
            .to_lowercase()
            .contains("cancel")
    );

    let holds = engine.query_holds("animal(Adam).");
    assert!(
        holds.is_err(),
        "cancelled holds query must Err, got {holds:?}"
    );

    // Clearing the flag restores normal evaluation.
    engine.clear_cancel_flag();
    let (result, _, _) = engine
        .query_text_with_proof("animal(Adam).")
        .expect("query should succeed after clearing cancel flag");
    assert_true(
        &result,
        "syllogism should hold once cancellation is cleared",
    );
}

// ─── Universal rule chain (syllogism) ───────────────────────────────

#[test]
fn universal_rule_chain_syllogism() {
    let engine = engine_with_facts(&["animal(every dog).", "eats(every animal).", "dog(Adam)."]);

    // Direct fact
    let (holds, _trace, _json) = engine.query_text_with_proof("dog(Adam).").unwrap();
    assert_true(&holds, "Direct fact should hold");

    // One-hop derivation: gerku → danlu
    let (holds, trace, _json) = engine.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(&holds, "One-hop derived fact should hold");
    assert!(trace.contains("Rule"), "Proof trace should show derivation");

    // Two-hop derivation: gerku → danlu → citka
    let (holds, trace, _json) = engine.query_text_with_proof("eats(Adam).").unwrap();
    assert_true(&holds, "Two-hop derived fact should hold");
    assert!(
        trace.contains("Rule"),
        "Proof trace should show derivation chain"
    );

    // Real FALSE: a bird is not in the KB (the preset's negative control —
    // Ch 19's "is Adam a bird?" query). Exact playground bytes for the verdict,
    // back-translation, "why", and collapsed proof are pinned in nibli-wasm's
    // `syllogism_playground_bytes_are_verbatim`.
    let (holds, _trace, _json) = engine.query_text_with_proof("bird(Adam).").unwrap();
    assert_false(&holds, "cipni (bird) is a real FALSE — not derivable");
}

// ─── Binary-condition universal rules (poi se R) ────────────────────
//
// A universal rule whose restrictor contains a CONVERTED two-place relation
// (`poi se prami la .alis.`) must fire. Pre-fix it returned FALSE: in a relative
// clause the implicit `ke'a` subject was injected post-hoc into the first
// unspecified `_x1` role, but `se` conversion had already vacated that slot and
// moved the explicit sumti — so the clause compiled `prami(dog, alis)` ("dog
// loves alis") instead of `prami(alis, dog)` ("loved by alis"), mismatching the
// asserted fact. Fixed in nibli-semantics by placing `ke'a` as the clause's x1 argument
// BEFORE conversion (semantic/compile.rs), mirroring the explicit-subject path.

#[test]
fn tensed_restrictor_rule_fires() {
    // "every dog that ATE (past) is hungry"; rex is a dog AND ate in the past.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past eats(it)).",
        "dog(Rex).",
        "past eats(Rex).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_true(
        &holds,
        "tensed-antecedent rule should fire when the matching Past premise holds",
    );
}

#[test]
fn tensed_restrictor_negative_control() {
    // rex is a dog but never ate → the tensed condition is unsatisfied.
    let engine = engine_with_facts(&["be_hungry(every dog where past eats(it)).", "dog(Rex)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_false(
        &holds,
        "tensed-antecedent rule must not fire without the past premise",
    );
}

#[test]
fn tensed_restrictor_wrong_tense_control() {
    // rex WILL eat (future) — must not satisfy a PAST antecedent (strict tense).
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past eats(it)).",
        "dog(Rex).",
        "future eats(Rex).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_false(
        &holds,
        "a Future premise must not satisfy a Past antecedent",
    );
}

#[test]
fn tensed_restrictor_bare_premise_control() {
    // rex eats (bare/timeless) — must not satisfy a PAST antecedent.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past eats(it)).",
        "dog(Rex).",
        "eats(Rex).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_false(&holds, "a bare premise must not satisfy a Past antecedent");
}

// ── Disjunctive rule antecedents (DNF rule-splitting) ──
// `ro lo X poi P ja Q cu R` is `∀x.(P(x)∨Q(x))→R(x)`, compiled as one
// backward-chaining rule per disjunct. Previously fail-closed-rejected.

#[test]
fn disjunctive_restrictor_fires_via_left_branch() {
    // "every dog that loves or befriends [something] is an animal." The poi clause
    // leaves x2 unspecified (zo'e), so the premise is the objectless `la .rex. cu
    // prami` (matching how the existing tensed-restrictor test uses objectless citka).
    let engine = engine_with_facts(&[
        "animal(every dog where loves(it) | friend(it)).",
        "dog(Rex).",
        "loves(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_true(
        &holds,
        "disjunctive antecedent fires via the left disjunct (prami)",
    );
}

#[test]
fn disjunctive_restrictor_fires_via_right_branch() {
    let engine = engine_with_facts(&[
        "animal(every dog where loves(it) | friend(it)).",
        "dog(Rex).",
        "friend(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_true(
        &holds,
        "disjunctive antecedent fires via the right disjunct (pendo)",
    );
}

#[test]
fn disjunctive_restrictor_negative_control() {
    // rex is a dog but neither loves nor befriends → neither disjunct holds.
    let engine = engine_with_facts(&[
        "animal(every dog where loves(it) | friend(it)).",
        "dog(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_false(
        &holds,
        "neither disjunct satisfied → disjunctive rule does not fire",
    );
}

#[test]
fn conjunctive_where_clauses_require_both() {
    // Control: `poi prami je pendo` (AND) still requires both — one is not enough.
    let engine = engine_with_facts(&[
        "animal(every dog where loves(it) & friend(it)).",
        "dog(Rex).",
        "loves(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_false(
        &holds,
        "conjunctive `je` restrictor requires both conjuncts — one is not enough",
    );
}

#[test]
fn disjunctive_forethought_implication_fires() {
    // `ganai ga P gi Q gi R` — (P ∨ Q) → R, a ground conditional with a disjunctive
    // antecedent. Fires when either disjunct holds.
    let engine = engine_with_facts(&[
        "loves(Rex, Alis).",
        "loves(Rex, Alis) | friend(Rex, Alis) -> animal(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_true(
        &holds,
        "forethought disjunctive antecedent (ganai ga…gi…gi) fires via a held disjunct",
    );
}

// ── Tensed rule conclusions ──
// `ganai A gi pu B` → `Or(Not(A), Past(B))` — a ground conditional with a tensed
// CONSEQUENT operand. Derives the Past fact only (the simple `ro lo X cu pu Q` is
// whole-rule `Past(ForAll(...))` and stays correctly rejected).

#[test]
fn tensed_conclusion_implication_fires() {
    let engine = engine_with_facts(&["dog(Rex) -> past animal(Rex).", "dog(Rex)."]);
    let (past_holds, _t, _j) = engine.query_text_with_proof("past animal(Rex).").unwrap();
    assert_true(
        &past_holds,
        "tensed conclusion derives the Past fact when the antecedent holds",
    );
    let (bare_holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_false(
        &bare_holds,
        "tensed conclusion must NOT derive a bare fact (tense-exact)",
    );
}

#[test]
fn tensed_conclusion_prenex_fires() {
    // `ro da zo'u ganai da gerku gi pu da danlu` → ∀da. gerku(da) → Past(danlu(da)).
    let engine = engine_with_facts(&["all $da: dog($da) -> past animal($da).", "dog(Rex)."]);
    let (past_holds, _t, _j) = engine.query_text_with_proof("past animal(Rex).").unwrap();
    assert_true(
        &past_holds,
        "prenex tensed conclusion derives the Past fact",
    );
    let (bare_holds, _t, _j) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_false(
        &bare_holds,
        "prenex tensed conclusion must NOT derive a bare fact",
    );
}

// ── Disjunctive rule conclusions as integrity constraints ──
// `ro lo X cu Q ja R` (a disjunctive HEAD) is registered as ¬(P ∧ ¬Q ∧ ¬R), not a
// Horn rule (deriving a disjunct is unsound). check_contradictions flags it when P
// holds and BOTH disjuncts are explicitly denied (`na`). The positive use is a query.

#[test]
fn disjunctive_conclusion_contradiction_flagged() {
    let engine = engine_with_facts(&[
        "every dog $d: animal($d) | fish($d).",
        "dog(Rex).",
        "~animal(Rex).",
        "~fish(Rex).",
    ]);
    let v = engine.check_contradictions();
    assert!(
        v.iter()
            .any(|m| m.contains("Disjunctive constraint violated")),
        "gerku(rex) holds and both disjuncts explicitly denied → contradiction: {v:?}"
    );
}

#[test]
fn disjunctive_conclusion_one_denied_no_contradiction() {
    let engine = engine_with_facts(&[
        "every dog $d: animal($d) | fish($d).",
        "dog(Rex).",
        "~animal(Rex).",
    ]);
    assert!(
        engine.check_contradictions().is_empty(),
        "only one disjunct denied → the other could hold → no contradiction"
    );
}

#[test]
fn disjunctive_query_still_works() {
    // The positive use of a disjunction is a QUERY, not a rule: `is rex Q or R?`.
    let engine = engine_with_facts(&["animal(Rex)."]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("animal(Rex) | fish(Rex).")
        .unwrap();
    assert_true(
        &holds,
        "a disjunctive query is TRUE when one disjunct holds (handled by the query evaluator)",
    );
}

#[test]
fn disjunctive_conclusion_jo_ju_stay_fail_closed() {
    // `jo` (biconditional) and `ju` (xor) are the only surface predicate connectives that
    // produce a MIXED conclusion head, but their expansions carry Not(..) / Not(And(..)),
    // which are not Horn-able — so they correctly stay fail-closed. (The clean mixed head
    // `And(P, Or)` is still reachable only via raw FOL; its positive case lives in the
    // nibli-reason `test_mixed_conclusion_*` unit tests. `gi'e` does NOT produce it: the GIhA
    // desugar repeats the head at the SENTENCE level, so `ro lo … gi'e …` compiles to a
    // conjunction of two universals, not one rule with a compound conclusion.)
    let engine = fresh_engine();
    assert!(
        engine
            .assert_text("every dog $d: animal($d) <-> fish($d).")
            .is_err(),
        "a `jo` (biconditional) conclusion head must fail closed (Not-bearing, not Horn)"
    );
    let engine2 = fresh_engine();
    assert!(
        engine2
            .assert_text("every dog $d: animal($d) ^ fish($d).")
            .is_err(),
        "a `ju` (xor) conclusion head must fail closed (Not(And(..)), not Horn)"
    );
    assert!(
        engine2.check_contradictions().is_empty(),
        "a failed `ju` assertion leaves no constraint (rollback)"
    );
}

// ── GIhA proposition-tail connectives (gi'e/gi'a/gi'o/gi'u) ──
// `mi klama gi'e citka`: each tail is a full predication sharing the head
// terms. the front-end desugars the chain to the `.i je` Connected shape with the head
// repeated (ONE sentence → one logic root), and nibli-reason's ground-path
// conjunction flattening stores a `gi'e`'s conjuncts as independently
// queryable facts. Surfaced by int19h's nibli-formalize feedback (2026-07-10):
// idiomatic reference translations use `gi'e` in nearly every sentence.

#[test]
fn conjoined_tails_assert_both_conjuncts() {
    let engine = engine_with_facts(&["goes(me) & eats(me)."]);
    let (klama, _, _) = engine.query_text_with_proof("goes(me).").unwrap();
    assert_true(&klama, "first gi'e tail is independently queryable");
    let (citka, _, _) = engine.query_text_with_proof("eats(me).").unwrap();
    assert_true(&citka, "second gi'e tail is independently queryable");
    let (sipna, _, _) = engine.query_text_with_proof("sleep(me).").unwrap();
    assert_false(&sipna, "unasserted predication stays FALSE (CWA control)");
}

#[test]
fn conjoined_tails_per_tail_trailing_argument() {
    // Each tail keeps its own trailing argument; the head is shared.
    let engine = engine_with_facts(&["goes(me, the market) & eats(me, some apple)."]);
    let (klama, _, _) = engine
        .query_text_with_proof("goes(me, the market).")
        .unwrap();
    assert_true(&klama, "first tail with its own x2");
    let (citka, _, _) = engine
        .query_text_with_proof("eats(me, some apple).")
        .unwrap();
    assert_true(&citka, "second tail with its own x2");
    let (cross, _, _) = engine
        .query_text_with_proof("eats(me, the market).")
        .unwrap();
    assert_false(&cross, "tail sumti must not leak across tails");
}

#[test]
fn conjoined_tails_genesis_negated_tail_verse() {
    // int19h's Genesis 1:2 shape, with a NAME head: `la .terdi. cu na se tarmi
    // gi'e kunti` ("the earth was without form AND void") — the `na` binds its
    // tail only. A description head would mint a fresh witness per tail,
    // silently splitting one surface referent into two (wrong TRUE on
    // disjoint witnesses) — the Name head avoids that trap.
    let engine = engine_with_facts(&["~shape(object: Terdi) & empty(Terdi)."]);
    let (kunti, _, _) = engine.query_text_with_proof("empty(Terdi).").unwrap();
    assert_true(&kunti, "positive tail asserted");
    let (tarmi, _, _) = engine
        .query_text_with_proof("shape(object: Terdi).")
        .unwrap();
    assert_false(&tarmi, "negated tail stores no positive fact");
}

#[test]
fn conjoined_tails_fused_negation_negates_right_tail() {
    // Solid `gi'enai` must behave exactly like `gi'e nai` (before the lexer
    // fix it parsed as a phantom lujvo pair that INVERTED the negation:
    // `mi citka` came back TRUE and `mi klama` FALSE).
    let engine = engine_with_facts(&["goes(me) & ~eats(me)."]);
    let (klama, _, _) = engine.query_text_with_proof("goes(me).").unwrap();
    assert_true(&klama, "positive tail asserted");
    let (citka, _, _) = engine.query_text_with_proof("eats(me).").unwrap();
    assert_false(&citka, "nai-negated tail stores no positive fact");
    engine.assert_text("eats(me).").unwrap();
    assert!(
        !engine.check_contradictions().is_empty(),
        "contrary positive after a gi'enai tail must flag a contradiction"
    );
}

#[test]
fn conjoined_tails_xor_negated_tail_fabricates_no_contradiction() {
    // `mi klama gi'u na citka` is Xor(K, ¬C): nibli-semantics lowers it to
    // And(Or(K,¬C), Not(And(K,¬C))). The Not(And(K,¬C)) conjunct's body is
    // NOT a pure positive conjunction — recording it would degrade ¬(K ∧ ¬C)
    // to ¬K (collect_ground_facts drops the inner Not) and fabricate a
    // contradiction on the consistent KB {K, C} (Xor satisfied: K true, ¬C
    // false). The purity guard must keep it out of the negative registry.
    let engine = engine_with_facts(&["goes(me) ^ ~eats(me).", "goes(me).", "eats(me)."]);
    assert!(
        engine.check_contradictions().is_empty(),
        "consistent KB must not report a fabricated contradiction: {:?}",
        engine.check_contradictions()
    );
}

#[test]
fn iju_negated_operand_fabricates_no_contradiction() {
    // Same purity-guard regression through the pre-existing `.i ju` surface.
    let engine = engine_with_facts(&["~goes(me) ^ eats(me).", "goes(me).", "eats(me)."]);
    assert!(
        engine.check_contradictions().is_empty(),
        "consistent KB must not report a fabricated contradiction: {:?}",
        engine.check_contradictions()
    );
}

#[test]
fn negation_inside_abstraction_fabricates_no_contradiction() {
    // A negation INSIDE an abstraction is quoted content, not an asserted
    // claim — the negative-conjunct walk must stop at the abstraction marker.
    let engine = engine_with_facts(&["knows(me, fact { ~goes(Rex) }).", "goes(Rex)."]);
    assert!(
        engine.check_contradictions().is_empty(),
        "a quoted negation must not feed contradiction detection: {:?}",
        engine.check_contradictions()
    );
}

#[test]
fn conjoined_tails_retraction_removes_both_conjuncts_and_negative_entry() {
    // A gi'e sentence is ONE fact-id; retracting it must remove both stored
    // conjuncts AND the na-tail's negative-registry entry (retract ≡
    // never-asserted).
    let engine = fresh_engine();
    let ids = engine.assert_text("dog(Rex) & ~animal(Rex).").unwrap();
    assert_eq!(ids.len(), 1, "a GIhA chain is one fact");
    let (gerku, _, _) = engine.query_text_with_proof("dog(Rex).").unwrap();
    assert_true(&gerku, "conjunct stored");
    engine.retract_fact(ids[0]).unwrap();
    let (gerku2, _, _) = engine.query_text_with_proof("dog(Rex).").unwrap();
    assert_false(&gerku2, "retracted conjunct gone");
    engine.assert_text("animal(Rex).").unwrap();
    assert!(
        engine.check_contradictions().is_empty(),
        "retracted na-tail must leave no negative-registry entry"
    );
}

#[test]
fn and_statement_negated_conjunct_preserves_tense_context() {
    // The negative template must carry the negated conjunct's tense — a
    // contrary positive with the SAME tense flags a contradiction.
    let engine = engine_with_facts(&["dog(Rex) & past ~goes(Rex).", "past goes(Rex)."]);
    assert!(
        !engine.check_contradictions().is_empty(),
        "tensed contrary positive must flag the tensed negative conjunct"
    );
}

#[test]
fn conjoined_tails_iff_and_whether_assert_behavior_pinned() {
    // `gi'o` (iff) asserts like its `.i jo` counterpart: the biconditional
    // registers two material-conditional rules (accepted; they form a cycle,
    // so a bare side queries Unknown(CycleCut), never TRUE — no ground fact
    // is stored). `gi'u` (xor) with positive tails stays fail-closed like
    // `.i ju`.
    let engine = fresh_engine();
    engine.assert_text("goes(me) <-> eats(me).").unwrap();
    let (klama, _, _) = engine.query_text_with_proof("goes(me).").unwrap();
    assert!(
        !klama.is_true(),
        "a bare biconditional must not derive either side TRUE: got {klama:?}"
    );
    let engine2 = fresh_engine();
    assert!(
        engine2.assert_text("goes(me) ^ eats(me).").is_err(),
        "a positive-tails xor assertion must fail closed like `.i ju`"
    );
}

#[test]
fn conjoined_tails_negated_tail_records_negative_fact_for_contradiction() {
    // The `na`-negated tail must land in the negative-fact registry exactly
    // like a standalone `na` assertion, so a later contrary positive is
    // flagged. Before the fix, a negated conjunct inside a compound assertion
    // was silently dropped (`collect_ground_facts` skips NotNode leaves).
    let engine = engine_with_facts(&["dog(Rex) & ~animal(Rex).", "animal(Rex)."]);
    assert!(
        !engine.check_contradictions().is_empty(),
        "contrary positive after a na-tail must flag a contradiction"
    );
}

#[test]
fn and_statement_negated_conjunct_records_negative_fact() {
    // Same registry fix through the pre-existing `.i je` surface: the `na`
    // half of `P .i je na Q` was silently dropped before.
    let engine = engine_with_facts(&["dog(Rex) & ~animal(Rex).", "animal(Rex)."]);
    assert!(
        !engine.check_contradictions().is_empty(),
        "contrary positive after a negated .i je conjunct must flag a contradiction"
    );
}

#[test]
fn conjoined_tails_all_negative_conjunction_accepted() {
    // `mi na klama gi'e na citka` — EVERY conjunct negated. Previously the
    // zero-ingest guard rejected this shape outright ("no representable
    // content"); now it is accepted like two standalone `na` assertions, each
    // recorded in the negative-fact registry.
    let engine = engine_with_facts(&["~goes(me) & ~eats(me)."]);
    let (klama, _, _) = engine.query_text_with_proof("goes(me).").unwrap();
    assert_false(&klama, "negated conjuncts store no positive facts");
    engine.assert_text("goes(me).").unwrap();
    assert!(
        !engine.check_contradictions().is_empty(),
        "contrary positive after an all-negative conjunction must flag a contradiction"
    );
}

#[test]
fn conjoined_tails_or_assert_stays_fail_closed_like_or_statement() {
    // A bare disjunction ingests no facts — `gi'a` at assert time fails closed
    // exactly like its `.i ja` spelled-out form (parity), while remaining fine
    // as a QUERY.
    let engine = fresh_engine();
    assert!(
        engine.assert_text("goes(me) | eats(me).").is_err(),
        "asserting a bare gi'a disjunction must fail closed"
    );
    let q = engine_with_facts(&["goes(me)."]);
    let (holds, _, _) = q.query_text_with_proof("goes(me) | eats(me).").unwrap();
    assert_true(&holds, "gi'a as a query is TRUE when one disjunct holds");
}

// ── Position-aware da/de/di quantifier scope ──
// A bare logic variable scopes by Lojban surface order. `da citka ro lo gerku`
// ("something eats every dog") is ∃da.∀x — a single witness eats ALL dogs —
// whereas `ro lo gerku cu se citka da` ("every dog is eaten by something") is
// ∀x.∃da (a possibly-different eater per dog). Before the fix both collapsed to
// ∀x.∃da regardless of word order.

#[test]
fn query_leading_existential_over_universal() {
    // ∃da.∀x is TRUE only when ONE entity eats every dog. Pre-fix the query
    // compiled to ∀x.∃da, wrongly returning TRUE for the split-eater KB.
    let one_eater = engine_with_facts(&[
        "eats(Adam, Rex).",
        "eats(Adam, Spot).",
        "dog(Rex).",
        "dog(Spot).",
    ]);
    let (holds, _t, _j) = one_eater
        .query_text_with_proof("eats($da, every dog).")
        .unwrap();
    assert_true(&holds, "adam eats every dog → ∃ one eater of all dogs");

    let split_eaters = engine_with_facts(&[
        "eats(Adam, Rex).",
        "eats(Ben, Spot).",
        "dog(Rex).",
        "dog(Spot).",
    ]);
    let (holds, _t, _j) = split_eaters
        .query_text_with_proof("eats($da, every dog).")
        .unwrap();
    assert_false(
        &holds,
        "different eaters per dog → NO single eater of all (∃∀, not ∀∃)",
    );
}

#[test]
fn assert_leading_existential_over_universal_compiles_and_round_trips() {
    // Asserting `da citka ro lo gerku` (∃da.∀x) must SUCCEED — nibli-reason skolemizes
    // the leading ∃ to a fresh constant and compiles the inner ∀ as a rule (sk₀
    // eats every dog). Before the dispatch change this errored as a "bare
    // disjunction". The asserted single witness then satisfies the ∃∀ query.
    let engine = fresh_engine();
    engine
        .assert_text("eats($da, every dog).")
        .expect("∃∀ assertion must compile via the leading-∃ skolemization path");
    engine.assert_text("dog(Rex).").unwrap();
    engine.assert_text("dog(Spot).").unwrap();
    let (holds, _t, _j) = engine
        .query_text_with_proof("eats($da, every dog).")
        .unwrap();
    assert_true(
        &holds,
        "the asserted single witness eats every dog (∃∀ round-trips)",
    );
}

#[test]
fn tensed_leading_existential_over_universal_rejected() {
    // `pu da citka ro lo gerku` → Past(Exists(ForAll)): a tense wrapping a whole
    // ∃∀ rule is rejected with the clear whole-rule message, not the ground
    // path's misleading "bare disjunction" error.
    let engine = fresh_engine();
    let err = engine
        .assert_text("past eats($da, every dog).")
        .expect_err("a tense wrapping a whole ∃∀ rule must be rejected");
    assert!(
        err.to_string().contains("whole universal/conditional"),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn trailing_existential_after_universal_is_per_witness() {
    // CONTROL: `ro lo gerku cu se citka da` (every dog is eaten by something) is
    // ∀x.∃da — a possibly-different eater per dog — so the ∃∀ query "is there one
    // eater of all dogs?" is FALSE. Confirms the after-case stays ∀∃ (unchanged).
    let engine = engine_with_facts(&[
        "eats(food: every dog, eater: $da).",
        "dog(Rex).",
        "dog(Spot).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("eats($da, every dog).")
        .unwrap();
    assert_false(
        &holds,
        "∀∃ gives per-dog eaters → NO single eater of all dogs",
    );
}

#[test]
fn implication_tensed_antecedent_fires_with_premise() {
    // Positive companion to the `ganai_tensed_antecedent_must_not_fire_unconditionally`
    // known-failure guard: a ground conditional with a tensed antecedent fires when
    // (and only when) the matching Past premise is present.
    let engine = engine_with_facts(&["past runs(Adam) -> animal(Adam).", "past runs(Adam)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(
        &holds,
        "tensed-antecedent ground conditional should fire on its Past premise",
    );
}

// A tense (pu/ca/ba) or deontic (ei/e'e) scoping a WHOLE universal rule cannot
// be soundly compiled to a timeless backward-chaining rule, so it is rejected.

#[test]
fn whole_rule_tense_universal_rejected() {
    // `pu ro lo gerku cu danlu` → Past(ForAll(...)) is rejected with the clear
    // whole-rule message (not the misleading "bare disjunction" zero-ingest one).
    let engine = fresh_engine();
    let err = engine
        .assert_text("past animal(every dog).")
        .expect_err("a tense wrapping a whole universal must be rejected");
    assert!(
        err.to_string().contains("whole universal/conditional"),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn whole_rule_deontic_universal_rejected() {
    // `ei ro lo prenu cu xamgu` → Obligatory(ForAll(...)): deriving an actuality
    // from an obligation is the same class of over-claim — rejected.
    let engine = fresh_engine();
    let err = engine
        .assert_text("must good(every person).")
        .expect_err("a deontic wrapping a whole universal must be rejected");
    assert!(
        err.to_string().contains("whole universal/conditional"),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn ground_obligation_does_not_imply_actuality() {
    // `ei la .adam. cu vimcu` ("Adam OUGHT to be removed") must NOT make the bare
    // actuality `la .adam. cu vimcu` ("Adam IS removed") hold — deriving "is" from
    // "ought" is an over-claim. The obligation itself stays queryable with its wrapper.
    // (A GROUND deontic fact is allowed; only a deontic over a WHOLE rule is rejected.)
    let engine = fresh_engine();
    engine
        .assert_text("must removes(Adam).")
        .expect("a ground deontic fact should assert");

    assert_false(
        &engine.query_holds("removes(Adam).").unwrap(),
        "ought must not imply is (ground obligation is not actuality)",
    );
    assert_true(
        &engine.query_holds("must removes(Adam).").unwrap(),
        "the obligation itself is preserved and queryable",
    );
}

#[test]
fn prenex_tensed_body_universal_rejected() {
    // `ro da zo'u pu da prami` → ForAll(Past(...)): a tense on the rule spine,
    // INSIDE the universal. Pre-fix it was silently stripped to a timeless rule.
    let engine = fresh_engine();
    let err = engine
        .assert_text("all $da: past loves($da).")
        .expect_err("a prenex with a tensed body must be rejected");
    assert!(
        err.to_string().contains("whole universal/conditional"),
        "expected the whole-rule rejection, got: {err}"
    );
}

#[test]
fn via_modal_arity_one_rejected() {
    // `mi barda fi'o prenu fe'u do` — `prenu` (person) is a 1-place predicate, so the
    // fi'o modal has no x2 slot to carry the main proposition's x1 (`mi`). The engine
    // fails closed rather than silently dropping that link. (Latent end-to-end:
    // The `via` grammar accepts any predicate, and every curated modal is arity >= 2,
    // so only fi'o over an arity-1 predicate reaches this.)
    let engine = fresh_engine();
    let err = engine
        .assert_text("big(me) via person(you).")
        .expect_err("a 1-place fi'o modal must be rejected");
    assert!(
        err.to_string().contains("modal tag predicate"),
        "expected the modal-arity rejection, got: {err}"
    );
}

#[test]
fn untensed_universal_still_compiles_and_fires() {
    // CONTROL: the untensed universal is unaffected — it compiles and fires.
    let engine = engine_with_facts(&["animal(every dog).", "dog(Rex)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_true(
        &holds,
        "an untensed universal must still compile and fire (only whole-rule tense is rejected)",
    );
}

#[test]
fn binary_restrictor_rule_fires() {
    // "every dog that is loved by alis is an animal"; rex is a dog AND loved by alis.
    let engine = engine_with_facts(&[
        "animal(every dog where loves(Alis, it)).",
        "dog(Rex).",
        "loves(loved: Rex, lover: Alis).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_true(
        &holds,
        "binary-restrictor rule should fire when both the gadri and the 2-place relation hold",
    );
}

#[test]
fn binary_restrictor_negative_control() {
    // rex is loved by alis but is NOT asserted to be a dog → rule must NOT fire.
    let engine = engine_with_facts(&[
        "animal(every dog where loves(Alis, it)).",
        "loves(loved: Rex, lover: Alis).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("animal(Rex).").unwrap();
    assert_false(
        &holds,
        "rule must not fire when the gadri predicate is unsatisfied",
    );
}

// ─── noi (non-restrictive) vs poi (restrictive) relative clauses ─────

#[test]
fn incidental_clause_predicate_is_asserted() {
    // "every dog, which is big, goes" — noi is NON-restrictive: it asserts the
    // dogs ARE big (a side-fact about every domain member) rather than
    // restricting the rule's domain to big dogs. So from gerku(rex) alone the
    // engine derives BOTH klama(rex) and barda(rex).
    let engine = engine_with_facts(&["dog(Rex).", "goes(every dog also big)."]);
    let (big, _trace, _json) = engine.query_text_with_proof("big(Rex).").unwrap();
    assert_true(
        &big,
        "noi asserts the incidental predicate about every dog (derived from gerku alone)",
    );
    let (goes, _trace, _json) = engine.query_text_with_proof("goes(Rex).").unwrap();
    assert_true(
        &goes,
        "noi rule fires on the unrestricted domain regardless of the incidental property",
    );
}

#[test]
fn restrictive_where_does_not_assert_incidental() {
    // Same shape with poi: the clause RESTRICTS the domain, so `barda` is a
    // premise (must be independently known), never a conclusion. Guards that
    // the noi fix does not leak into poi.
    let engine = engine_with_facts(&["dog(Rex).", "goes(every dog where big)."]);
    let (big, _trace, _json) = engine.query_text_with_proof("big(Rex).").unwrap();
    assert_false(
        &big,
        "poi keeps the restrictor as a premise, not a derived conclusion",
    );
}

#[test]
fn binary_restrictor_constant_second_place_fires() {
    // DDI-shape: "every drug metabolised-by CYP2C9 triggers an alert".
    let engine = engine_with_facts(&[
        "warns(every chemical where metabolized_by(it, Siptucin)).",
        "chemical(Uarfarin).",
        "metabolized_by(Uarfarin, Siptucin).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("warns(Uarfarin).").unwrap();
    assert_true(
        &holds,
        "2-place restrictor with a constant second place should fire",
    );
}

// ─── Object-position multi-universal rules (ro lo X cu R ro lo Y) ────
// `ro lo gerku cu pendo ro lo mlatu` ("every dog befriends every cat") compiles
// to a nested universal `∀x.(gerku(x) → ∀y.(mlatu(y) → pendo(x,y)))`; the rule
// compiler prenex-flattens it into the SAME rule the prenex form below produces
// (and fires via the same multi-variable join).

#[test]
fn object_position_universal_fires() {
    // every dog befriends every cat; rex is a dog, tom is a cat → rex pendo tom.
    // RED before prenex-flattening (the nested ∀ was rejected at compilation).
    let engine = engine_with_facts(&["friend(every dog, every cat).", "dog(Rex).", "cat(Tom)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("friend(Rex, Tom).").unwrap();
    assert_true(
        &holds,
        "object-position universal: every dog befriends every cat",
    );
}

#[test]
fn object_position_universal_negative_control() {
    // tom is NOT asserted to be a cat → the (rex, tom) pair must NOT fire.
    let engine = engine_with_facts(&["friend(every dog, every cat).", "dog(Rex)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("friend(Rex, Tom).").unwrap();
    assert_false(&holds, "tom is not a cat → no friendship derived");
}

#[test]
fn object_position_existential_import_no_phantom_entity() {
    // The existential-import existential-import presupposition for `ro lo gerku cu pendo ro lo
    // mlatu` must assert a dog witness and a cat witness as DISTINCT entities — NOT
    // one phantom entity that is both. So "is some dog a cat?" is FALSE. RED before
    // the per-universal-witness fix (a single shared witness satisfied both).
    let engine = engine_with_facts(&["friend(every dog, every cat)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("cat(some dog).").unwrap();
    assert_false(&holds, "no single xorlo witness is both a dog and a cat");
}

#[test]
fn object_position_count_object_fails_closed() {
    // An exact-count object (`ci lo mlatu` = "exactly three cats") is NOT a
    // universal, so it is not prenex-peeled; the Count consequent fails closed.
    let engine = fresh_engine();
    let err = engine
        .assert_text("friend(every dog, exactly 3 cat).")
        .expect_err("an exact-count object position must be rejected");
    assert!(
        err.to_string().contains("not a flat predicate") || err.to_string().contains("Rejecting"),
        "expected a fail-closed rejection, got: {err}"
    );
}

// ─── Prenex multi-variable rules (ro da ro de zo'u) ─────────────────

#[test]
fn prenex_symmetric_rule_fires() {
    // ro da ro de zo'u ganai da pendo de gi de pendo da
    // "for all da, de: if da befriends de, then de befriends da." Both vars are
    // bound by the conclusion (de pendo da), so this exercises prenex parse +
    // lowering + leading-ForAll compilation without the unbound-var firing gap.
    let engine = engine_with_facts(&[
        "all $da, $de: friend($da, $de) -> friend($de, $da).",
        "friend(Rex, Felix).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("friend(Felix, Rex).").unwrap();
    assert_true(
        &holds,
        "prenex symmetric rule should derive the reverse friendship",
    );
}

#[test]
fn prenex_cross_entity_join_fires() {
    // ro da ro de ro di zo'u ganai ge da fanta di gi de se katna di gi de zenba
    // "for all inhibitor da, substrate de, enzyme di: if da inhibits di AND de is
    // metabolized-by di, then de's concentration rises." The CYP cross-entity
    // join: querying `de zenba` binds only de; the inhibitor (da) and enzyme (di)
    // appear ONLY in conditions, so this is the unbound-individual-var firing case.
    let engine = engine_with_facts(&[
        "all $da, $de, $di: prevents($da, $di) & metabolized_by($de, $di) -> increases($de).",
        "prevents(Flukonazol, Siptucin).",
        "metabolized_by(Uarfarin, Siptucin).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("increases(Uarfarin).")
        .unwrap();
    assert_true(
        &holds,
        "prenex CYP cross-entity join should raise warfarin concentration",
    );
}

#[test]
fn prenex_cross_entity_join_negative_control() {
    // Same rule, but apixaban is metabolized by a DIFFERENT enzyme that no drug
    // inhibits → the join must NOT fire (guards against an under-conditioned rule).
    let engine = engine_with_facts(&[
        "all $da, $de, $di: prevents($da, $di) & metabolized_by($de, $di) -> increases($de).",
        "prevents(Flukonazol, Siptucin).",
        "metabolized_by(Apiksaban, Sipibeman).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("increases(Apiksaban).")
        .unwrap();
    assert_false(
        &holds,
        "no drug inhibits apixaban's enzyme → no concentration rise",
    );
}

#[test]
fn prenex_join_terminates_without_blowup() {
    // A 3-variable prenex join over a modest fact base must resolve quickly —
    // no candidates^k / members^dep_count blowup. Watchdog thread; the query is
    // TRUE (warfarin's enzyme is inhibited) and must return well within budget.
    use std::sync::mpsc;
    use std::time::Duration;
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let mut lines = vec![
            "all $da, $de, $di: prevents($da, $di) & metabolized_by($de, $di) -> increases($de)."
                .to_string(),
            "prevents(Flukonazol, Siptucin).".to_string(),
        ];
        // Distinct noise drugs/enzymes (letter-only cmevla — no digits).
        for v in [
            "a", "e", "i", "o", "u", "ai", "au", "ei", "oi", "ia", "ie", "io",
        ] {
            lines.push(format!("metabolized_by(Druk{v}n, Enk{v}n)."));
        }
        lines.push("metabolized_by(Uarfarin, Siptucin).".to_string());
        let refs: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
        let engine = engine_with_facts(&refs);
        let r = engine.query_text_with_proof("increases(Uarfarin).");
        let _ = tx.send(r.map(|(h, _, _)| h.is_true()));
    });
    match rx.recv_timeout(Duration::from_secs(15)) {
        Ok(Ok(true)) => {}
        Ok(other) => panic!("prenex join gave unexpected result: {other:?}"),
        Err(_) => panic!("prenex join did not terminate within 15s (candidates^k blowup?)"),
    }
}

// ─── Temporal reasoning ─────────────────────────────────────────────

#[test]
fn temporal_past_assertion_and_query() {
    let engine = engine_with_facts(&["past big(some dog)."]);

    // Tensed query should hold
    let (holds, _trace, _json) = engine.query_text_with_proof("past big(some dog).").unwrap();
    assert_true(&holds, "Past-tensed query should hold");

    // Bare (untensed) query should NOT hold
    let (holds, _trace, _json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_false(&holds, "Bare query should not match past-tensed fact");
}

#[test]
fn temporal_tense_discrimination() {
    let engine = engine_with_facts(&["past big(some dog)."]);

    // Future tense should NOT match past tense
    let (holds, _trace, _json) = engine
        .query_text_with_proof("future big(some dog).")
        .unwrap();
    assert_false(&holds, "Future query should not match past-tensed fact");
}

// ─── Tense/deontic flavor matrix (mutation-baseline kills) ──────────
// The Past (`pu`) paths are pinned above; the 2026-07 mutation sweep showed the
// Future/Present/Permitted arms (kb.rs `with_tense`/`unify_facts`/
// `tense_to_static`/`extract_from_index`, rules.rs `build_stored_fact_from_node`,
// reasoning.rs `find_witnesses`) were exercised only by the nibli-verify oracle
// gates, which don't run per-mutant. These pin them in the per-mutant suite.

#[test]
fn temporal_future_and_present_matrix() {
    let engine = engine_with_facts(&["future eats(Rex).", "now eats(Bel)."]);

    assert_true(
        &engine.query_holds("future eats(Rex).").unwrap(),
        "Future fact matches a Future query",
    );
    assert_false(
        &engine.query_holds("past eats(Rex).").unwrap(),
        "Future fact must not match a Past query",
    );
    assert_false(
        &engine.query_holds("eats(Rex).").unwrap(),
        "Future fact must not leak into a bare query",
    );
    assert_true(
        &engine.query_holds("now eats(Bel).").unwrap(),
        "Present fact matches a Present query",
    );
    assert_false(
        &engine.query_holds("future eats(Bel).").unwrap(),
        "Present fact must not match a Future query",
    );
}

#[test]
fn future_rule_consequent_derives_future_fact() {
    // Mirrors tensed_conclusion_implication_fires for `ba`: derives Future(B) only.
    let engine = engine_with_facts(&["dog(Rex) -> future dead(Rex).", "dog(Rex)."]);
    assert_true(
        &engine.query_holds("future dead(Rex).").unwrap(),
        "Future conclusion derives the Future fact",
    );
    assert_false(
        &engine.query_holds("dead(Rex).").unwrap(),
        "Future conclusion must not derive a bare fact",
    );
    assert_false(
        &engine.query_holds("past dead(Rex).").unwrap(),
        "Future conclusion must not derive a Past fact",
    );
}

#[test]
fn deontic_permitted_and_obligatory_matrix() {
    // e'e = Permitted, ei = Obligatory — flavor-exact, no bare leak either way.
    let engine = engine_with_facts(&["may eats(Rex).", "must goes(Bel)."]);

    assert_true(
        &engine.query_holds("may eats(Rex).").unwrap(),
        "Permitted fact matches a Permitted query",
    );
    assert_false(
        &engine.query_holds("eats(Rex).").unwrap(),
        "Permitted fact must not leak into a bare query",
    );
    assert_false(
        &engine.query_holds("must eats(Rex).").unwrap(),
        "Permitted fact must not match an Obligatory query",
    );
    assert_true(
        &engine.query_holds("must goes(Bel).").unwrap(),
        "Obligatory fact matches an Obligatory query",
    );
    assert_false(
        &engine.query_holds("may goes(Bel).").unwrap(),
        "Obligatory fact must not match a Permitted query",
    );
}

#[test]
fn deontic_rule_consequent_derives_flavored_fact() {
    // `ganai A gi e'e B` derives Permitted(B) — flavor-exact, mirroring the
    // tensed-conclusion behavior above. This pins the 2026-07 fix: the deontic
    // consequent wrapper used to be stripped WITHOUT setting the flavor, so this
    // rule derived a BARE citka fact — permission leaked into unqualified truth
    // (found by the mutation-baseline triage).
    let engine = engine_with_facts(&["dog(Rex) -> may eats(Rex).", "dog(Rex)."]);
    assert_true(
        &engine.query_holds("may eats(Rex).").unwrap(),
        "a Permitted conclusion derives the Permitted fact",
    );
    assert_false(
        &engine.query_holds("eats(Rex).").unwrap(),
        "a Permitted conclusion must NOT derive a bare fact",
    );
    assert_false(
        &engine.query_holds("must eats(Rex).").unwrap(),
        "a Permitted conclusion must NOT derive an Obligatory fact",
    );
}

#[test]
fn deontic_rule_condition_is_flavor_exact() {
    // `ganai e'e A gi B`: the condition matches only a stored Permitted(A) —
    // a bare A must not fire it (same 2026-07 fix, condition side).
    let engine = engine_with_facts(&["may dog(Rex) -> eats(Rex).", "dog(Rex)."]);
    assert_false(
        &engine.query_holds("eats(Rex).").unwrap(),
        "a bare fact must not fire a Permitted-flavored condition",
    );

    let engine2 = engine_with_facts(&["may dog(Rex) -> eats(Rex).", "may dog(Rex)."]);
    assert_true(
        &engine2.query_holds("eats(Rex).").unwrap(),
        "a Permitted fact fires the Permitted-flavored condition",
    );
}

#[test]
fn future_existential_witness_query() {
    // `da` under `ba`: the existential witness search must look through the
    // FutureNode wrapper (reasoning.rs find_witnesses) — flavor-exact.
    let engine = engine_with_facts(&["future eats(Rex)."]);
    assert_true(
        &engine.query_holds("future eats($da).").unwrap(),
        "existential finds the Future fact under a Future query",
    );
    assert_false(
        &engine.query_holds("past eats($da).").unwrap(),
        "existential must not find the Future fact under a Past query",
    );
}

// ─── Exact-count queries as propositions (mutation-baseline kills) ──
// The CountNode fallback loop in check_formula_holds_core (member enumeration +
// satisfying tally) was unexercised by the per-mutant suites — the curated count
// coverage lives in nibli-verify's ASP oracle. Pin the tally arithmetic here.

#[test]
fn exact_count_query_over_ground_facts() {
    let engine = engine_with_facts(&["dog(Adam).", "dog(Bel).", "animal(Adam).", "animal(Bel)."]);
    assert_true(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "exactly-2 holds when exactly two members satisfy the body",
    );
    assert_false(
        &engine.query_holds("animal(exactly 3 dog).").unwrap(),
        "exactly-3 fails when only two members satisfy the body",
    );
    assert_false(
        &engine.query_holds("animal(exactly 1 dog).").unwrap(),
        "exactly-1 fails when two members satisfy the body",
    );
}

// ─── Mutation-triage kills, round 2 (2026-07: category-E survivors) ──

#[test]
fn present_rule_consequent_derives_present_fact() {
    // `ca` analog of the Future/Past tensed-conclusion tests — pins the
    // (Present, Present) unify_facts arm on the rule-conclusion path.
    let engine = engine_with_facts(&["dog(Rex) -> now dead(Rex).", "dog(Rex)."]);
    assert_true(
        &engine.query_holds("now dead(Rex).").unwrap(),
        "Present conclusion derives the Present fact",
    );
    assert_false(
        &engine.query_holds("dead(Rex).").unwrap(),
        "Present conclusion must not derive a bare fact",
    );
}

#[test]
fn obligatory_rule_consequent_derives_obligatory_fact() {
    // `ei` analog of the Permitted-consequent test — pins the
    // (Obligatory, Obligatory) unify_facts arm on the rule-conclusion path.
    let engine = engine_with_facts(&["dog(Rex) -> must eats(Rex).", "dog(Rex)."]);
    assert_true(
        &engine.query_holds("must eats(Rex).").unwrap(),
        "Obligatory conclusion derives the Obligatory fact",
    );
    assert_false(
        &engine.query_holds("eats(Rex).").unwrap(),
        "Obligatory conclusion must not derive a bare fact",
    );
    assert_false(
        &engine.query_holds("may eats(Rex).").unwrap(),
        "Obligatory conclusion must not derive a Permitted fact",
    );
}

#[test]
fn flavor_polymorphic_rule_firing_is_flavor_exact() {
    // An UNMARKED rule fires flavor-polymorphically: a `ba` goal pins the rule's
    // conditions to `ba` (apply_tense_to_fact). Both directions matter:
    // a ba fact supports the ba goal; a BARE fact must NOT.
    let engine = engine_with_facts(&["animal(every dog).", "future dog(Rex)."]);
    assert_true(
        &engine.query_holds("future animal(Rex).").unwrap(),
        "unmarked rule fires for a Future goal from a Future condition fact",
    );

    let engine2 = engine_with_facts(&["animal(every dog).", "dog(Rex)."]);
    assert_false(
        &engine2.query_holds("future animal(Rex).").unwrap(),
        "a Future goal must NOT fire the rule from a bare condition fact",
    );
}

#[test]
fn disjunctive_existential_witness() {
    // `da gerku ja mlatu` — the existential witness search must descend BOTH
    // disjuncts (find_witnesses OrNode arm): a cat alone satisfies it.
    let engine = engine_with_facts(&["cat(Adam)."]);
    assert_true(
        &engine.query_holds("dog($da) | cat($da).").unwrap(),
        "a witness satisfying the right disjunct suffices",
    );
    assert_false(
        &engine.query_holds("dog($da) & cat($da).").unwrap(),
        "the conjunctive form still needs both",
    );
}

#[test]
fn tensed_negation_is_flavor_exact() {
    // `na` under each tense flavor: the negation must be recorded at ITS flavor
    // (find_negation_body threads tense) — the positive same-flavor query stays
    // FALSE and the contradiction is detected on the flavored re-assert.
    for tense in ["past", "now", "future"] {
        let engine = engine_with_facts(&[&format!("{tense} ~eats(Adam).")]);
        assert_false(
            &engine.query_holds(&format!("{tense} eats(Adam).")).unwrap(),
            "the flavored positive must be FALSE after the flavored denial",
        );
    }
}

#[test]
fn count_block_lowering_matches_term_position_behavior() {
    // The BLOCK spelling `exactly 2 dog $d: big($d).` lowers to the same
    // Count shape as `big(exactly 2 dog).` (seam-pinned), so it inherits the
    // 2026-07-02 count-assertion semantics: two fresh witnesses materialize,
    // each satisfying restrictor and body.
    let engine = engine_with_facts(&["exactly 2 dog $d: big($d)."]);
    for q in ["big(some dog).", "dog($da).", "big(exactly 2 dog)."] {
        assert_true(
            &engine.query_holds(q).unwrap(),
            "count-block assertion must materialize satisfying witnesses",
        );
    }
    assert_false(
        &engine.query_holds("big(exactly 3 dog).").unwrap(),
        "exactly 3 must be FALSE after a 2-witness count block",
    );
}

#[test]
fn count_assertion_materializes_witnesses() {
    // DECIDED 2026-07-02 (GUARANTEES §Aggregation): an exact-count ASSERTION
    // materializes PA distinct fresh witnesses satisfying the restrictor and
    // body — so the assertion is SELF-DERIVABLE and composes with CWA. (This
    // pin previously asserted the opposite: count assertions were accepted
    // but verdict-inert, deriving nothing at all.)
    let engine = engine_with_facts(&["big(exactly 1 dog)."]);
    for q in [
        "big(exactly 1 dog).",
        "dog($da).",
        "big($da).",
        "big(some dog).",
    ] {
        assert_true(
            &engine.query_holds(q).unwrap(),
            "a count assertion materializes its witness",
        );
    }
    assert_false(
        &engine.query_holds("big(exactly 2 dog).").unwrap(),
        "exactly-one stays exactly one",
    );

    // count > 1: DISTINCT witnesses with DISTINCT events.
    let engine2 = engine_with_facts(&["small(exactly 2 cat)."]);
    assert_true(
        &engine2.query_holds("small(exactly 2 cat).").unwrap(),
        "exactly-two materializes two distinct witnesses",
    );
    assert_false(
        &engine2.query_holds("small(exactly 1 cat).").unwrap(),
        "two witnesses are not one",
    );
    assert_true(
        &engine2.query_holds("cat($da).").unwrap(),
        "the witnesses satisfy the restrictor",
    );
}

#[test]
fn exact_count_excludes_existential_import_witness() {
    // DECIDED 2026-07-02 (GUARANTEES §Aggregation): the existential-import presupposition
    // witness a description universal asserts satisfies ∃/∀ but is EXCLUDED
    // from counting — a phantom entity a rule presupposed must not change
    // "how many". (Engine-probed pre-change: 2 dogs + the taxonomy rule made
    // `re lo gerku cu danlu` count 3 and fail.)
    let engine = engine_with_facts(&["dog(Adam).", "dog(Karl).", "animal(every dog)."]);
    assert_true(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "two real dogs count as two — the presupposition phantom is not counted",
    );
    assert_false(
        &engine.query_holds("animal(exactly 3 dog).").unwrap(),
        "the phantom must not push the count to three",
    );
}

#[test]
fn find_witnesses_collapse_equals_and_events() {
    // The audit scenario: broda(adam), broda(karl), adam du karl used to
    // return FOUR ?? tuples (2 derivation events × 2 du-merged names) for ONE
    // entity. Entity-level enumeration returns exactly one.
    let engine = engine_with_facts(&["dog(Adam).", "dog(Karl).", "Adam = Karl."]);
    let tuples = engine.query_find_text("dog($da).").unwrap();
    assert_eq!(
        tuples.len(),
        1,
        "one entity, one witness tuple (was 4 pre-decision): {tuples:?}"
    );
    assert_eq!(
        engine.count_witnesses_text("dog($da).").unwrap(),
        1,
        "count_witnesses agrees with the entity-level enumeration",
    );
}

#[test]
fn zero_count_assertion_mints_no_witness() {
    // `no lo gerku cu barda` (exactly zero): no witness may be minted — a
    // phantom member would corrupt the domain and the closed-world verdicts.
    let engine = engine_with_facts(&["big(no dog)."]);
    assert_false(
        &engine.query_holds("dog($da).").unwrap(),
        "a zero-count assertion must not mint a witness",
    );
}

#[test]
fn over_arity_untagged_argument_is_rejected() {
    // gerku has 2 places; three untagged argument overflow — the compile must
    // REJECT (fail-closed), never silently drop the extra argument.
    let engine = fresh_engine();
    assert!(
        engine.assert_text("dog(Adam, Bob, Kim).").is_err(),
        "untagged over-arity sumti must fail closed, not drop silently"
    );
}

#[test]
fn builtin_arithmetic_verdicts() {
    // sumji(x1, x2, x3): x1 = x2 + x3 via the built-in evaluator — pins the
    // GroundTerm::as_f64 numeric extraction the compute dispatch relies on.
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("sum(5, 2, 3).").unwrap(),
        "5 = 2 + 3 is TRUE by built-in arithmetic",
    );
    assert_false(
        &engine.query_holds("sum(4, 2, 3).").unwrap(),
        "4 = 2 + 3 is FALSE by built-in arithmetic",
    );
}

#[test]
fn ground_conditional_with_existential_conclusion() {
    // `ganai A gi lo mlatu cu barda`: the conclusion existential is skolemized
    // to a GROUND witness at rule-compile time (ground_skolems); firing must
    // derive a queryable witness.
    let engine = engine_with_facts(&["dog(Adam) -> big(some cat).", "dog(Adam)."]);
    assert_true(
        &engine.query_holds("cat($da).").unwrap(),
        "the fired conclusion's skolem witness satisfies the restrictor",
    );
    assert_true(
        &engine.query_holds("big(some cat).").unwrap(),
        "the fired conclusion itself holds",
    );
}

#[test]
fn be_clause_with_tagged_tail_term_compiles_both() {
    // `klama be X be'o fi Y`: `be` binds x2, `fi` tags Y to x3 — both must
    // land (pins the WithArgs merge's positional-tail copy).
    let engine = fresh_engine();
    let buf = engine
        .compile_debug("goes(Adam, Paris, origin: Rom).")
        .expect("be-clause with fi-tagged tail should compile");
    assert!(
        role_has_const(&buf, "goes_x2", "paris"),
        "be must bind x2; buffer: {buf:?}"
    );
    assert!(
        role_has_const(&buf, "goes_x3", "rom"),
        "fi-tagged tail must land in x3; buffer: {buf:?}"
    );
}

#[test]
fn equals_equivalence_transfers_across_tense_flavor() {
    // A du-merged name must answer a FLAVORED query via its equivalent: the
    // equivalence variant lookup must respect the stored flavor.
    let engine = engine_with_facts(&["past dog(Adam).", "Adam = Bob."]);
    assert_true(
        &engine.query_holds("past dog(Bob).").unwrap(),
        "du equivalence transfers the Past fact to the equivalent name",
    );
    assert_false(
        &engine.query_holds("dog(Bob).").unwrap(),
        "the transfer must stay flavor-exact (no bare leak)",
    );
}

#[test]
fn explicitly_tensed_rule_condition_is_flavor_exact() {
    // `ganai pu A gi B` — an EXPLICITLY tensed condition must match only the
    // same-flavor fact (flatten_conjuncts_through_exists threads the flavor
    // into the condition template), for every flavor.
    for tense in ["past", "now", "future"] {
        let engine = engine_with_facts(&[
            &format!("{tense} dog(Rex) -> dead(Rex)."),
            &format!("{tense} dog(Rex)."),
        ]);
        assert_true(
            &engine.query_holds("dead(Rex).").unwrap(),
            "same-flavor condition fact fires the rule",
        );

        let engine2 = engine_with_facts(&[&format!("{tense} dog(Rex) -> dead(Rex)."), "dog(Rex)."]);
        assert_false(
            &engine2.query_holds("dead(Rex).").unwrap(),
            "a bare fact must NOT fire an explicitly tensed condition",
        );
    }
}

#[test]
fn x3_conversion_swaps_x1_and_x3() {
    // `te klama` swaps x1↔x3 — the 3-place conversion arm (sibling of the xe
    // pin above; the swap must actually happen, not silently no-op).
    let engine = fresh_engine();
    let buf = engine
        .compile_debug("goes(origin: Rom, destination: _, goer: Adam).")
        .expect("te klama should compile");
    assert!(
        role_has_const(&buf, "goes_x3", "rom"),
        "te must move the head term to x3 (origin); buffer: {buf:?}"
    );
    assert!(
        role_has_const(&buf, "goes_x1", "adam"),
        "te must move the third term to x1 (goer); buffer: {buf:?}"
    );
}

#[test]
fn numeric_terms_are_not_universal_domain_members() {
    // Current semantics (pinned): a `li` number asserted into a predicate does
    // NOT become a quantifier-domain member — a universal restricted to it is
    // VACUOUSLY true (both compute bodies below, one arithmetically true and
    // one false, give TRUE). This is the sharp edge that keeps the stored-number
    // compute-arg path (GroundTerm::as_f64 on bound variables) surface-
    // unreachable; the literal path is pinned by builtin_arithmetic_verdicts.
    let engine = engine_with_facts(&["big(5)."]);
    assert_true(
        &engine.query_holds("sum(every big, 2, 3).").unwrap(),
        "vacuous universal (numbers are not domain members)",
    );
    assert_true(
        &engine.query_holds("sum(every big, 2, 2).").unwrap(),
        "vacuous even for an arithmetically false body — numbers never enumerate",
    );
}

#[test]
fn lo_under_connective_is_per_occurrence_existential() {
    // `bite(some dog, Adam) & bite(some dog, Bel).` splits over the sentence-
    // level `&` into two propositions, each with a PER-OCCURRENCE existential:
    // each conjunct mints its own witness, so TWO DIFFERENT dogs — one biting
    // Adam, one biting Bel — satisfy it. A shared-witness reading ("one dog
    // bites both") would make this FALSE.
    let engine = engine_with_facts(&[
        "dog(Rex).",
        "dog(Dan).",
        "bite(Rex, Adam).",
        "bite(Dan, Bel).",
    ]);
    assert_true(
        &engine
            .query_holds("bite(some dog, Adam) & bite(some dog, Bel).")
            .unwrap(),
        "per-occurrence reading: a different witness per conjunct suffices",
    );

    // Negative control: each conjunct still needs its own witness.
    let engine2 = engine_with_facts(&["dog(Rex).", "bite(Rex, Adam)."]);
    assert_false(
        &engine2
            .query_holds("bite(some dog, Adam) & bite(some dog, Bel).")
            .unwrap(),
        "an unwitnessed conjunct still fails",
    );
}

#[test]
fn exact_count_collapses_equals_classes() {
    // DECIDED 2026-07-02 (GUARANTEES §Aggregation): `du` means identity, so
    // counting is ENTITY-level — two du-merged names for one entity count as
    // ONE. (This pin previously asserted the opposite, uncollapsed behavior;
    // the decision flipped it deliberately.)
    let engine = engine_with_facts(&[
        "dog(Adam).",
        "dog(Karl).",
        "animal(Adam).",
        "animal(Karl).",
        "Adam = Karl.",
    ]);
    assert_true(
        &engine.query_holds("animal(exactly 1 dog).").unwrap(),
        "collapsed: the merged entity counts as ONE",
    );
    assert_false(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "collapsed: two names for one entity do NOT count as two",
    );
}

#[test]
fn naf_antecedent_rule_fires_and_blocks() {
    // `ro da zo'u ganai ge da gerku gi da na mlatu gi da xagji` — a rule with a
    // POSITIVE and a NEGATED (NAF) condition. Pins the candidate-filter/lookahead
    // polarity (filter_event_candidates): the NAF condition must count as
    // satisfied when the witness is ABSENT and as blocking when PRESENT.
    let engine = engine_with_facts(&[
        "all $da: dog($da) & ~cat($da) -> be_hungry($da).",
        "dog(Rex).",
    ]);
    assert_true(
        &engine.query_holds("be_hungry(Rex).").unwrap(),
        "NAF condition with no witness lets the rule fire",
    );

    let engine2 = engine_with_facts(&[
        "all $da: dog($da) & ~cat($da) -> be_hungry($da).",
        "dog(Rex).",
        "cat(Rex).",
    ]);
    assert_false(
        &engine2.query_holds("be_hungry(Rex).").unwrap(),
        "an asserted witness blocks the NAF condition",
    );
}

// ─── Description opacity (le vs lo) ────────────────────────────────

#[test]
fn description_opacity_definite_vs_indefinite() {
    let engine = engine_with_facts(&["big(the dog)."]);

    // le query should hold (opaque description)
    let (holds, _trace, _json) = engine.query_text_with_proof("big(the dog).").unwrap();
    assert_true(&holds, "le (opaque) query should hold");
}

#[test]
fn la_name_assertion() {
    let engine = engine_with_facts(&["dog(Adam)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("dog(Adam).").unwrap();
    assert_true(&holds, "la name assertion should hold");
}

// ─── Parse error handling ───────────────────────────────────────────

#[test]
fn parse_error_returns_syntax_error() {
    let engine = fresh_engine();
    // The error CLASS is now first-class on the engine API (not merely recoverable
    // from the `[Syntax Error]` Display prefix): a parse failure is the typed
    // `EngineError::Syntax`.
    let err = engine
        .assert_text("not valid lojban at all !!!")
        .expect_err("Invalid Lojban should produce an error");
    assert!(
        matches!(err, EngineError::Syntax(_)),
        "a parse failure must be EngineError::Syntax, got: {err}"
    );
}

#[test]
fn assert_stage_failure_is_reasoning_class() {
    let engine = fresh_engine();
    // A well-formed sentence the reasoner rejects at ASSERTION time (a tense over a
    // whole universal) is a REASONING-class error — the assert is the reasoning
    // stage (the buffer already passed nibli-semantics), so nibli-reason's `assert_fact` classes it
    // `Reasoning`, distinct from a nibli-semantics `Semantic` or a nibli-kr `Syntax` error.
    let err = engine
        .assert_text("past animal(every dog).")
        .expect_err("a whole-rule tense must be rejected");
    assert!(
        matches!(err, EngineError::Reasoning(_)),
        "an assertion-stage rejection is a Reasoning class, got: {err}"
    );
}

#[test]
fn query_parse_error() {
    let engine = fresh_engine();
    let result = engine.query_text_with_proof("blorp bleep !!!");
    assert!(result.is_err(), "Invalid query should produce an error");
}

#[test]
fn partial_parse_fails_closed_for_query() {
    // The unified fail-closed policy: the parser recovers per statement, so this input
    // has a valid first sentence and an unlexable second. A QUERY must abort on
    // the parse error (don't answer when the input didn't fully parse), not
    // silently proceed with the partial parse. `nibli_kr::parse_checked` is shared by
    // every embedder (nibli-engine, nibli-pipeline, nibli-wasm), so all three agree.
    let engine = engine_with_facts(&["dog(Adam)."]);
    let err = engine
        .query_holds("la .adam. cu gerku .i \u{ff}\u{ff}\u{ff}")
        .expect_err("a partial-parse query must fail closed");
    assert!(
        matches!(err, EngineError::Syntax(_)),
        "a parse error must be the Syntax class, got: {err:?}"
    );
}

// ─── Proof trace structure ──────────────────────────────────────────

#[test]
fn proof_trace_contains_asserted_for_ground_fact() {
    let engine = engine_with_facts(&["big(some dog)."]);
    let (holds, trace, json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_true(&holds, "Ground fact proof query should be true");
    assert!(
        trace.contains("Fact:"),
        "Ground fact proof should contain 'Fact:'"
    );
    // JSON should be valid
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("Proof JSON should parse");
    assert!(
        parsed.get("steps").is_some(),
        "JSON should have 'steps' field"
    );
    assert!(
        parsed.get("root").is_some(),
        "JSON should have 'root' field"
    );
}

#[test]
fn proof_trace_json_valid_for_derived_fact() {
    let engine = engine_with_facts(&["animal(every dog).", "dog(Adam)."]);
    let (_holds, _trace, json) = engine.query_text_with_proof("animal(Adam).").unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("Proof JSON should parse");
    let steps = parsed["steps"].as_array().expect("steps should be array");
    assert!(steps.len() > 1, "Derived proof should have multiple steps");
}

// ─── Engine reset ───────────────────────────────────────────────────

#[test]
fn reset_clears_knowledge_base() {
    let engine = engine_with_facts(&["big(some dog)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_true(&holds, "Fact should hold before reset");

    engine.reset();

    let (holds, _trace, _json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_false(&holds, "Fact should not hold after reset");
}

// ─── Multiple facts ─────────────────────────────────────────────────

#[test]
fn multiple_independent_facts() {
    let engine = engine_with_facts(&["big(some dog).", "small(some cat)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_true(&holds, "First fact should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("small(some cat).").unwrap();
    assert_true(&holds, "Second fact should hold");
}

// ─── Multi-sentence assertion ───────────────────────────────────────

#[test]
fn multi_sentence_assertion() {
    let engine = fresh_engine();
    // Assert multiple sentences in one text block (separated by .i)
    engine
        .assert_text("big(some dog). small(some cat).")
        .unwrap();
    let (holds, _trace, _json) = engine.query_text_with_proof("big(some dog).").unwrap();
    assert_true(&holds, "First sentence should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("small(some cat).").unwrap();
    assert_true(&holds, "Second sentence should hold");
}

// ─── Sentence connectives ───────────────────────────────────────────

#[test]
fn universal_rule_with_named_entity() {
    // Universal rules + named entity — the primary use case
    let engine = engine_with_facts(&["animal(every dog).", "dog(Adam)."]);
    let (holds, _trace, _json) = engine.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(&holds, "Named entity should derive through universal rule");
}

#[test]
fn forethought_implication_reasons() {
    // ganai A gi B  ==  A -> B. Assert the conditional + A (gerku), derive B (danlu).
    let engine = engine_with_facts(&["dog(Adam) -> animal(Adam).", "dog(Adam)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(
        &holds,
        "ganai: danlu should derive from gerku (modus ponens)",
    );

    // Negative control: without the antecedent, the consequent is not derivable.
    let only_rule = engine_with_facts(&["dog(Adam) -> animal(Adam)."]);
    let (holds, _t, _j) = only_rule.query_text_with_proof("animal(Adam).").unwrap();
    assert_false(&holds, "ganai: danlu must NOT hold without gerku");
}

#[test]
fn forethought_biconditional_go_gi_reasons_both_directions() {
    // go A gi B  ==  A <-> B. Reasons from either side (no CycleCut).
    let fwd = engine_with_facts(&["dog(Adam) <-> animal(Adam).", "dog(Adam)."]);
    let (holds, _t, _j) = fwd.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(
        &holds,
        "go biconditional: gerku should derive danlu (forward)",
    );

    let rev = engine_with_facts(&["dog(Adam) <-> animal(Adam).", "animal(Adam)."]);
    let (holds, _t, _j) = rev.query_text_with_proof("dog(Adam).").unwrap();
    assert_true(
        &holds,
        "go biconditional: danlu should derive gerku (reverse)",
    );
}

#[test]
fn afterthought_biconditional_jo_reasons_both_directions() {
    // S1 .i jo S2  ==  S1 <-> S2.
    let fwd = engine_with_facts(&["dog(Adam) <-> animal(Adam).", "dog(Adam)."]);
    let (holds, _t, _j) = fwd.query_text_with_proof("animal(Adam).").unwrap();
    assert_true(
        &holds,
        ".i jo biconditional: gerku should derive danlu (forward)",
    );

    let rev = engine_with_facts(&["dog(Adam) <-> animal(Adam).", "animal(Adam)."]);
    let (holds, _t, _j) = rev.query_text_with_proof("dog(Adam).").unwrap();
    assert_true(
        &holds,
        ".i jo biconditional: danlu should derive gerku (reverse)",
    );
}

// ─── Conversion (se) ────────────────────────────────────────────────

#[test]
fn x2_conversion_assertion_and_query() {
    let engine = engine_with_facts(&["owned(Adam, some dog)."]);
    let (holds, _trace, _json) = engine
        .query_text_with_proof("owned(Adam, some dog).")
        .unwrap();
    assert_true(&holds, "se-converted assertion should be queryable");
}

#[test]
fn connected_arguments_under_x1_tag_hold_for_both() {
    // `fa mi .e do klama` parses as Tagged(Fa, Connected(mi, Je, do)). The tag
    // distributes over BOTH operands, so both `mi` and `do` are goers. Before
    // the fix, the right operand `do` was silently dropped → `do klama` FALSE.
    let engine = engine_with_facts(&["goes(me) & goes(you)."]);
    let (mi_holds, _, _) = engine.query_text_with_proof("goes(me).").unwrap();
    assert_true(&mi_holds, "me must be a goer");
    let (do_holds, _, _) = engine.query_text_with_proof("goes(you).").unwrap();
    assert_true(
        &do_holds,
        "do must be a goer (right operand was dropped before the fix)",
    );
}

#[test]
fn connected_under_x1_tag_negative_control() {
    // Only `mi` asserted → `do klama` must be FALSE (the fix must not over-assert).
    let engine = engine_with_facts(&["goes(me)."]);
    let (do_holds, _, _) = engine.query_text_with_proof("goes(you).").unwrap();
    assert_false(&do_holds, "do was never asserted as a goer");
}

#[test]
fn cll_place_counter_x3_tag_then_untagged() {
    // `klama fi le zarci do` — CLL: `fi` sets the place counter to x3 (le zarci),
    // and the following UNTAGGED `do` resumes at x4 (NOT x1, the pre-fix bug).
    let engine = fresh_engine();
    let buf = engine
        .compile_debug("goes(origin: the market, route: you).")
        .expect("`klama fi le zarci do` should compile");
    assert!(
        role_has_const(&buf, "goes_x4", "you"),
        "untagged `you` must fill x4 after the route tag; buffer: {buf:?}"
    );
    assert!(
        !role_has_const(&buf, "goes_x1", "you"),
        "you must NOT land in x1 (pre-fix `first free slot` bug); buffer: {buf:?}"
    );
}

#[test]
fn x5_conversion_swaps_x1_and_x5() {
    // `xe klama` swaps x1↔x5 (mutation-baseline kill: the 5-place conversion arm
    // in nibli-semantics's apply_predicate was exercised by no per-mutant-suite test). All
    // five places are filled (`zo'e` middles) so the swap is observable: the
    // head term must land in x5 (vehicle) and the tail term in x1 (goer).
    let engine = fresh_engine();
    let buf = engine
        .compile_debug("goes(means: Ford, destination: _, origin: _, route: _, goer: Adam).")
        .expect("xe klama with five places should compile");
    assert!(
        role_has_const(&buf, "goes_x5", "ford"),
        "xe must move the head term to x5 (vehicle); buffer: {buf:?}"
    );
    assert!(
        role_has_const(&buf, "goes_x1", "adam"),
        "xe must move the fifth term to x1 (goer); buffer: {buf:?}"
    );
    assert!(
        !role_has_const(&buf, "goes_x1", "ford"),
        "xe must not leave the head term in x1; buffer: {buf:?}"
    );
}

#[test]
fn query_holds_matches_proof_query_boolean() {
    let engine = engine_with_facts(&["animal(every dog).", "dog(Adam)."]);

    let via_bool = engine
        .query_holds("animal(Adam).")
        .expect("Boolean query should succeed");
    let (via_proof, _trace, _json) = engine
        .query_text_with_proof("animal(Adam).")
        .expect("Proof query should succeed");

    assert_eq!(
        via_bool, via_proof,
        "Boolean query API and proof query API must agree on whether a fact holds"
    );
}

#[test]
fn reset_then_reassert_replaces_previous_kb_contents() {
    let engine = engine_with_facts(&["dog(Adam)."]);
    assert!(
        engine
            .query_holds("dog(Adam).")
            .expect("Initial fact should be queryable")
            .is_true()
    );

    engine.reset();
    engine
        .assert_text("cat(Elis).")
        .expect("New fact should assert after reset");

    assert!(
        engine
            .query_holds("dog(Adam).")
            .expect("Old fact query should still run")
            .is_false(),
        "Reset should remove prior KB contents before new facts are asserted"
    );
    assert!(
        engine
            .query_holds("cat(Elis).")
            .expect("New fact should be queryable")
            .is_true(),
        "Facts asserted after reset should become the whole active KB"
    );
}

#[test]
fn persistent_engine_replays_asserted_facts_after_reopen() {
    let path = temp_db_path("replay_after_reopen");
    cleanup(&path);

    {
        let engine = fresh_open(&path, "Persistent engine should open");
        engine
            .assert_text("animal(every dog).")
            .expect("Rule should persist");
        engine
            .assert_text("dog(Adam).")
            .expect("Fact should persist");
        assert!(
            engine
                .query_holds("animal(Adam).")
                .expect("Derived query should run before reopen")
                .is_true()
        );
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("animal(Adam).")
                .expect("Derived query should run after reopen")
                .is_true(),
            "Reopened engine should replay persisted rule and fact"
        );
    }

    cleanup(&path);
}

#[test]
fn persistent_engine_honors_store_retractions_after_reopen() {
    let path = temp_db_path("retract_then_reopen");
    cleanup(&path);

    let fact_id = {
        let engine = fresh_open(&path, "Persistent engine should open");
        // Single sentence → exactly one fact id.
        engine
            .assert_text("dog(Adam).")
            .expect("Fact should persist")[0]
    };

    {
        let mut store = NibliStore::open(&path, "local".into()).expect("Store should open");
        store
            .retract_fact(fact_id)
            .expect("Retracting persisted fact should succeed");
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("dog(Adam).")
                .expect("Query should run after reopen")
                .is_false(),
            "Retracted facts must not replay into the reopened engine"
        );
    }

    cleanup(&path);
}

/// Regression: retracting through the *engine* API (not the store directly)
/// must durably tombstone the fact so it does not resurrect on reopen.
///
/// Before the fix, `NibliEngine::retract_fact` only mutated the in-memory KB and
/// never propagated the tombstone to the persistent `NibliStore`, so `open()`'s
/// replay of `all_active_facts()` brought the retracted fact back to life.
#[test]
fn persistent_engine_retraction_via_engine_api_survives_reopen() {
    let path = temp_db_path("engine_api_retract_then_reopen");
    cleanup(&path);

    let fact_id = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let id = engine
            .assert_text("dog(Adam).")
            .expect("Fact should persist")[0];
        assert!(
            engine
                .query_holds("dog(Adam).")
                .expect("Query should run before retraction")
                .is_true(),
            "Fact should hold immediately after assertion"
        );

        // Retract through the engine API (the path the REPL / server use), NOT
        // by reaching into the store directly.
        engine
            .retract_fact(id)
            .expect("Engine-level retraction should succeed");
        assert!(
            engine
                .query_holds("dog(Adam).")
                .expect("Query should run after retraction")
                .is_false(),
            "Retracted fact must not hold in the live engine"
        );
        id
    };

    // The store must have recorded the tombstone durably.
    {
        let store = NibliStore::open(&path, "local".into()).expect("Store should reopen");
        let record = store
            .get_fact(fact_id)
            .expect("Store read should succeed")
            .expect("Retracted fact record should still exist as a tombstone");
        assert!(
            record.retracted,
            "Engine-level retraction must durably tombstone the persisted fact"
        );
    }

    // Reopening a fresh engine must NOT resurrect the retracted fact.
    {
        let reopened = fresh_open(&path, "Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("dog(Adam).")
                .expect("Query should run after reopen")
                .is_false(),
            "Facts retracted via the engine API must stay retracted after reopen"
        );
    }

    cleanup(&path);
}

// ════════════════════════════════════════════════════════════════════
// GDPR compliance engine (Chapter 20 case study)
//
// Every assertion below uses a construct verified to reason end-to-end. The
// corpus file (gdpr.lojban) is the single source of truth; these tests pin the
// behaviour the chapter narrates so prose and engine cannot drift.
// ════════════════════════════════════════════════════════════════════

/// Every non-comment line of gdpr.lojban asserts cleanly through the pipeline.
#[test]
fn gdpr_file_loads_clean() {
    let corpus = include_str!("../../gdpr.nibli");
    let engine = fresh_engine();
    for (line_num, line) in corpus.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        engine.assert_text(trimmed).unwrap_or_else(|e| {
            panic!(
                "gdpr.lojban line {} failed to assert: {:?}\n{}",
                line_num + 1,
                trimmed,
                e
            )
        });
    }
}

/// The GDPR overlay reads the lawful-basis proof in legal-domain terms — the
/// `se curmi` conclusion as "has a lawful basis for processing", with the data
/// subject named — instantiated and `X`-free. The dictionary fallback stays
/// literal ("permits"). Confirms the DRY overlay->fallback chain generalizes
/// beyond the drug corpus.
#[test]
fn gdpr_why_lawful_basis_is_domain_termed() {
    let engine = engine_with_facts(&[
        "permitted(every person where approves).",
        "person(Adam).",
        "approves(Adam).",
    ]);
    let (_r, trace) = engine.query_text_raw_proof("permitted(Adam).").unwrap();

    let overlay = summarize_proof_with(&trace, Register::Spec, Some(&GDPR_OVERLAY))
        .expect("lawful-basis proof has a why summary");
    assert!(overlay.contains("Adam consents"), "why: {overlay}");
    assert!(
        overlay.contains("Adam has a lawful basis for processing"),
        "why: {overlay}"
    );
    assert!(!overlay.contains('X'), "bare variable leaked: {overlay}");

    let fallback = summarize_proof_with(&trace, Register::Spec, None).unwrap();
    assert!(
        !fallback.contains("lawful basis"),
        "fallback must stay literal: {fallback}"
    );
    assert!(!fallback.contains('X'), "bare variable leaked: {fallback}");
}

/// THE HEADLINE: consent-withdrawal belief revision.
/// With consent, processing has a lawful basis (Art 6) and there is no erasure
/// right. Retract consent and BOTH flip: no lawful basis remains, so the right
/// to erasure (Art 17(1)(b)) arises. The erasure verdict is derived by
/// negation-as-failure and the proof carries the NAF dependency flag.
#[test]
fn gdpr_belief_revision_consent_withdrawal() {
    let engine = fresh_engine();
    engine.assert_text("person(Adam).").unwrap();
    engine
        .assert_text("permitted(every person where approves).")
        .unwrap(); // Art 6(1)(a)
    let consent_id = engine.assert_text("approves(Adam).").unwrap()[0];

    // ── Consent present ──
    assert_true(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "With consent, Adam's processing has a lawful basis",
    );
    assert_false(
        &engine.query_holds("~permitted(Adam).").unwrap(),
        "With consent, there is no right to erasure",
    );

    // ── Withdraw consent ──
    engine.retract_fact(consent_id).unwrap();

    assert_false(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "After withdrawal, no lawful basis remains",
    );
    let (erasure, trace, json) = engine.query_text_with_proof("~permitted(Adam).").unwrap();
    assert_true(
        &erasure,
        "After withdrawal, the right to erasure (Art 17) is triggered",
    );
    assert!(!trace.is_empty(), "Erasure proof trace should be non-empty");
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("Erasure proof JSON should parse");
    assert_eq!(
        parsed["naf_dependent"],
        serde_json::Value::Bool(true),
        "Erasure verdict must be flagged as negation-as-failure dependent"
    );
}

/// Art 6(1)(b): a contract is an independent lawful basis. A subject bound by a
/// contract reaches lawful processing without consent; a subject with neither
/// basis does not (negative control).
#[test]
fn gdpr_lawful_basis_via_contract() {
    let engine = engine_with_facts(&[
        "permitted(every person where promise).",
        "person(Adam).",
        "promise(Adam).",
        "person(Bet).", // a person with no lawful basis
    ]);
    assert_true(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "Contract is a lawful basis (Art 6(1)(b))",
    );
    assert_false(
        &engine.query_holds("permitted(Bet).").unwrap(),
        "A subject with no lawful basis has no lawful processing",
    );
}

/// Art 9: special-category (health) data requires a stricter, specific basis;
/// ordinary personal data does not (negative control / DPIA triage).
#[test]
fn gdpr_special_category_requires_stricter_basis() {
    let engine = engine_with_facts(&[
        "obligated(every healthy data, event { exact() }).",
        "healthy data(Kanrek).",
        "data(Ordrek).",
    ]);
    assert_true(
        &engine
            .query_holds("obligated(Kanrek, event { exact() }).")
            .unwrap(),
        "Health data requires a stricter basis (Art 9)",
    );
    assert_false(
        &engine
            .query_holds("obligated(Ordrek, event { exact() }).")
            .unwrap(),
        "Ordinary data does not require the special-category basis",
    );
}

/// Art 5: principles (here, accuracy) apply to ALL personal data, reached through
/// a category -> data -> obligation chain (multi-hop inference over special data).
#[test]
fn gdpr_art5_accuracy_applies_to_health_data() {
    let engine = engine_with_facts(&[
        "data(every healthy data).",
        "obligated(every data, event { correct() }).",
        "healthy data(Kanrek).",
    ]);
    let (holds, trace, _json) = engine
        .query_text_with_proof("obligated(Kanrek, event { correct() }).")
        .unwrap();
    assert_true(
        &holds,
        "Accuracy obligation reaches health data via kanro datni -> datni -> drani",
    );
    assert!(
        trace.contains("Rule"),
        "Accuracy proof should show a derivation chain"
    );
}

/// Art 15: every data subject has a right of access (DSAR); a non-subject does
/// not (negative control).
#[test]
fn gdpr_right_of_access_dsar() {
    let engine = engine_with_facts(&[
        "permitted(every person, event { data discovers() }).",
        "person(Adam).",
        "data governs(Akmes).", // a controller, not a data subject
    ]);
    assert_true(
        &engine
            .query_holds("permitted(Adam, event { data discovers() }).")
            .unwrap(),
        "A data subject has the right of access (Art 15)",
    );
    assert_false(
        &engine
            .query_holds("permitted(Akmes, event { data discovers() }).")
            .unwrap(),
        "A controller (non-subject) does not acquire the access right",
    );
}

/// Art 33: a controller that suffers a breach must notify; a controller with no
/// breach has no such obligation (negative control / audit evidence).
#[test]
fn gdpr_breach_notification() {
    let engine = engine_with_facts(&[
        "obligated(every data governs where flaw, event { message() }).",
        "data governs(Akmes).",
        "data governs(Gugli).",
        "flaw(Akmes).", // only AkmeCorp breached
    ]);
    assert_true(
        &engine
            .query_holds("obligated(Akmes, event { message() }).")
            .unwrap(),
        "A breached controller must notify (Art 33)",
    );
    assert_false(
        &engine
            .query_holds("obligated(Gugli, event { message() }).")
            .unwrap(),
        "A controller with no breach has no notification obligation",
    );
}

/// Article 17 in its NATURAL Lojban form: a person who does NOT consent is
/// obligated to be erased — a NEGATED, event-decomposed relative-clause restrictor
/// (`poi na zanru`) that compiles to a negation-as-failure check over an
/// existential. This was fail-closed-rejected before the fix (the rule was
/// modeled only as the query-time negation `na se curmi`); now the rule itself
/// fires, and consent withdrawal flips the obligation. Mirrors
/// `gdpr_belief_revision_consent_withdrawal` but at the RULE level.
#[test]
fn gdpr_erasure_rule_via_negated_consent_restrictor() {
    let engine = fresh_engine();
    engine.assert_text("person(Adam).").unwrap();
    engine
        .assert_text("obligated(every person where ~approves, event { removes() }).")
        .expect("the negated-restrictor erasure rule must now compile");

    // ── No consent → the erasure obligation arises (NAF: no consent witness). ──
    assert_true(
        &engine
            .query_holds("obligated(Adam, event { removes() }).")
            .unwrap(),
        "No consent → erasure obligation holds (Art 17 as a stored rule)",
    );

    // ── Consent present → the negated restrictor is false → no obligation. ──
    let consent_id = engine.assert_text("approves(Adam).").unwrap()[0];
    assert_false(
        &engine
            .query_holds("obligated(Adam, event { removes() }).")
            .unwrap(),
        "Consent present → no erasure obligation",
    );

    // ── Withdraw consent → the obligation re-arises, flagged NAF-dependent. ──
    engine.retract_fact(consent_id).unwrap();
    let (holds, trace, json) = engine
        .query_text_with_proof("obligated(Adam, event { removes() }).")
        .unwrap();
    assert_true(&holds, "After withdrawal, the erasure obligation re-arises");
    assert!(!trace.is_empty(), "Erasure proof trace should be non-empty");
    let parsed: serde_json::Value =
        serde_json::from_str(&json).expect("Erasure proof JSON should parse");
    assert_eq!(
        parsed["naf_dependent"],
        serde_json::Value::Bool(true),
        "Erasure-rule verdict rests on a negation-as-failure dependency",
    );
}

/// The negated-restrictor erasure rule is PER-SUBJECT, not global: a consenting
/// person is not obligated while a non-consenting one is — the NAF check binds the
/// universal `x` before evaluating the existential.
#[test]
fn gdpr_erasure_rule_is_per_subject() {
    let engine = fresh_engine();
    engine.assert_text("person(Adam).").unwrap();
    engine.assert_text("person(Bet).").unwrap();
    engine
        .assert_text("obligated(every person where ~approves, event { removes() }).")
        .unwrap();
    engine.assert_text("approves(Bet).").unwrap(); // bet consents; adam does not

    assert_true(
        &engine
            .query_holds("obligated(Adam, event { removes() }).")
            .unwrap(),
        "adam (no consent) is obligated to be erased",
    );
    assert_false(
        &engine
            .query_holds("obligated(Bet, event { removes() }).")
            .unwrap(),
        "bet (consented) is NOT obligated — the rule is per-subject, not global",
    );
}

/// PERF REGRESSION PIN (Ch 20 reproducibility): the chapter tells readers to
/// load the FULL shipped gdpr.lojban and run `la .adam. cu se curmi`. Before
/// the 2026-06 backward-chaining fixes in nibli-reason (lazy candidate build,
/// index-decidable filter pruning, depth-horizon provability lookahead), this
/// query did not return within 240 seconds in a debug build: at the depth
/// horizon every unbound-event-variable filter check returned ResourceExceeded
/// and pessimistically kept the entire members^k candidate cartesian product
/// alive. Post-fix the full Ch 20 sequence — lawful-basis query, consent
/// withdrawal, and BOTH post-retraction verdicts (the worst case: a definitive
/// False cannot short-circuit the search) — completes in seconds. The
/// 120-second budget is deliberately generous so CI never flakes; its job is
/// to catch a regression back to the cartesian-blowup complexity class.
#[test]
fn gdpr_full_corpus_lawful_basis_query_completes() {
    let start = std::time::Instant::now();
    let corpus = include_str!("../../gdpr.nibli");
    let engine = fresh_engine();
    let mut consent_id = None;
    for (line_num, line) in corpus.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let id = engine.assert_text(trimmed).unwrap_or_else(|e| {
            panic!(
                "gdpr.lojban line {} failed to assert: {:?}\n{}",
                line_num + 1,
                trimmed,
                e
            )
        });
        if trimmed == "approves(Adam)." {
            // Single-sentence corpus line → one id.
            consent_id = id.first().copied();
        }
    }

    // Ch 20's first lawful-basis query, against the FULL loaded corpus.
    assert_true(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "Against the full corpus, Adam's processing has a lawful basis (Art 6)",
    );

    // The consent-withdrawal belief-revision flip, also against the full corpus.
    engine
        .retract_fact(consent_id.expect("consent line present in gdpr.lojban"))
        .unwrap();
    assert_false(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "After withdrawal, no lawful basis remains (full-corpus exhaustive search)",
    );
    assert_true(
        &engine.query_holds("~permitted(Adam).").unwrap(),
        "After withdrawal, the right to erasure (Art 17) is triggered",
    );
    // (The Art 17 erasure RULE now lives in the shipped corpus; its belief-revision
    // flip is exercised end-to-end by `gdpr_erasure_rule_via_negated_consent_restrictor`
    // on a small engine. Querying `se bilga lo nu se vimcu` against the FULL corpus
    // is deliberately NOT done here — it fans out across every Art 5/9 obligation
    // rule, which would dominate this timing pin without testing anything new.)

    let elapsed = start.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(120),
        "full-corpus Ch 20 sequence took {elapsed:?} (budget 120s) — the \
         backward-chaining candidate search has regressed"
    );
}

// ════════════════════════════════════════════════════════════════════
// Corpus transcript pins (book Ch 20 / Ch 21 reproducibility)
// ════════════════════════════════════════════════════════════════════

/// Load a corpus string exactly the way nibli-host's `:load` does: trim each line,
/// count blanks and `#` comments as skipped, assert everything else (any
/// assert error fails the test — the book transcripts print `0 errors`).
/// Returns the (asserted, skipped) counters plus every asserted line's
/// returned fact id, in file order.
fn load_corpus_like_host(engine: &NibliEngine, corpus: &str) -> (u32, u32, Vec<(String, u64)>) {
    let mut asserted = 0u32;
    let mut skipped = 0u32;
    let mut ids = Vec::new();
    for (line_num, line) in corpus.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            skipped += 1;
            continue;
        }
        let id = engine.assert_text(trimmed).unwrap_or_else(|e| {
            panic!(
                "corpus line {} failed to assert (book pins 0 errors): {:?}\n{}",
                line_num + 1,
                trimmed,
                e
            )
        });
        asserted += 1;
        // Corpus lines are single-sentence (no medial `.i`) → exactly one id.
        ids.push((trimmed.to_string(), id[0]));
    }
    (asserted, skipped, ids)
}

fn pinned_id(ids: &[(String, u64)], line: &str) -> u64 {
    let hits: Vec<u64> = ids
        .iter()
        .filter(|(l, _)| l == line)
        .map(|&(_, id)| id)
        .collect();
    assert!(
        hits.len() == 1,
        "expected exactly one corpus occurrence of {line:?}, found {}",
        hits.len()
    );
    hits[0]
}

/// TRANSCRIPT PIN (book Ch 20): the chapter's captured REPL sessions print
/// `[Load] Done: 24 asserted, 77 skipped, 0 errors`, retract the consent fact
/// by id (#21), and — in the multi-basis walkthrough — assert `la .adam. cu
/// nupre` right after the load and later retract it as #24. A corpus reorder,
/// insertion, or deletion silently invalidates those printed ids and counts;
/// this pin breaks loudly instead. If it fails: gdpr.lojban changed — recapture
/// the Ch 20 transcripts (book repo) together with these expected values.
#[test]
fn gdpr_corpus_transcript_pins() {
    let engine = fresh_engine();
    let (asserted, skipped, ids) = load_corpus_like_host(&engine, include_str!("../../gdpr.nibli"));
    assert_eq!(
        (asserted, skipped),
        (24, 77),
        "Ch 20 pins `[Load] Done: 24 asserted, 77 skipped, 0 errors`"
    );
    assert_eq!(
        pinned_id(&ids, "approves(Adam)."),
        21,
        "Ch 20 retracts the consent fact as id #21"
    );
    // The multi-basis walkthrough asserts the contract fact immediately after
    // the corpus load and later retracts it as #24.
    let contract_id = engine.assert_text("promise(Adam).").unwrap()[0];
    assert_eq!(
        contract_id, 24,
        "Ch 20 retracts the post-load contract fact as id #24"
    );
}

/// TRANSCRIPT PIN (book Ch 21): the chapter's captured REPL sessions print
/// `[Load] Done: 16 asserted, 78 skipped, 0 errors` and retract two facts by
/// id — the inhibition fact (#4, fluconazole discontinued) and the regimen
/// fact (#10, warfarin stopped). Same contract as the Ch 20 pin above: a
/// corpus edit must break this test, not silently drift the book.
#[test]
fn ddi_corpus_transcript_pins() {
    let engine = fresh_engine();
    let (asserted, skipped, ids) =
        load_corpus_like_host(&engine, include_str!("../../drug-interactions.nibli"));
    assert_eq!(
        (asserted, skipped),
        (16, 78),
        "Ch 21 pins `[Load] Done: 16 asserted, 78 skipped, 0 errors`"
    );
    assert_eq!(
        pinned_id(&ids, "prevents(Flukonazol, Siptucin)."),
        4,
        "Ch 21 retracts the inhibition fact as id #4"
    );
    assert_eq!(
        pinned_id(&ids, "uses(Adam, Varfarin)."),
        10,
        "Ch 21 retracts the warfarin regimen fact as id #10"
    );
}

// ════════════════════════════════════════════════════════════════════
// Stacked relative-clause restrictor: conjunction, not overwrite
// ════════════════════════════════════════════════════════════════════

/// Regression: stacked `poi` relative clauses must CONJOIN, not overwrite. A
/// universal whose restrictor stacks two clauses fires only when BOTH clause
/// predicates hold. Pre-fix, the earlier clause (`zenba`) was silently dropped,
/// so the rule degenerated to `cinla -> ckape` and a cinla-only drug wrongly
/// triggered the conclusion.
#[test]
fn stacked_where_clauses_conjoin_both() {
    let engine = engine_with_facts(&[
        "dangerous(every chemical where increases where thin).",
        "chemical(Alfan).",
        "increases(Alfan).",
        "thin(Alfan).", // both conditions hold
        "chemical(Betan).",
        "increases(Betan).", // zenba only
        "chemical(Gaman).",
        "thin(Gaman).", // cinla only
    ]);
    assert_true(
        &engine.query_holds("dangerous(Alfan).").unwrap(),
        "both zenba and cinla -> ckape",
    );
    assert_false(
        &engine.query_holds("dangerous(Betan).").unwrap(),
        "zenba only (cinla missing) -> NOT ckape",
    );
    assert_false(
        &engine.query_holds("dangerous(Gaman).").unwrap(),
        "cinla only (zenba missing) -> NOT ckape (the pre-fix bug)",
    );
}

// ════════════════════════════════════════════════════════════════════
// Drug-drug interaction (DDI) safety engine (Chapter 21 case study)
//
// Every assertion below uses a construct verified to reason end-to-end. The
// corpus file (drug-interactions.lojban) is the single source of truth; these
// tests pin the behaviour Chapter 21 narrates so prose and engine cannot drift.
//
// Mechanism: fluconazole inhibits CYP2C9; warfarin/phenytoin (narrow therapeutic
// index) are CYP2C9 substrates -> concentration rises -> toxicity risk -> alert.
// Apixaban (CYP3A4 substrate) is the negative control: no alert.
// ════════════════════════════════════════════════════════════════════

/// Load every non-comment line of drug-interactions.lojban into a fresh engine.
fn engine_with_ddi_corpus() -> NibliEngine {
    let corpus = include_str!("../../drug-interactions.nibli");
    let engine = fresh_engine();
    for (line_num, line) in corpus.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        engine.assert_text(trimmed).unwrap_or_else(|e| {
            panic!(
                "drug-interactions.lojban line {} failed to assert: {:?}\n{}",
                line_num + 1,
                trimmed,
                e
            )
        });
    }
    engine
}

/// Every non-comment line of drug-interactions.lojban asserts cleanly.
#[test]
fn ddi_file_loads_clean() {
    let _ = engine_with_ddi_corpus();
}

/// THE HEADLINE: the warfarin + fluconazole interaction derives a safety alert
/// through the full mechanism chain (inhibition + metabolism -> concentration
/// increase -> toxicity risk -> alert). Apixaban, metabolised by a different
/// enzyme that fluconazole does not inhibit, derives NO alert — a real, deduced
/// False, not an absence of data.
#[test]
fn ddi_headline_warfarin_fluconazole_alert() {
    let engine = engine_with_ddi_corpus();

    // Step 1: concentration increase (derived from the grounded mechanism).
    assert_true(
        &engine.query_holds("increases(Varfarin).").unwrap(),
        "Warfarin concentration rises (fluconazole inhibits CYP2C9, warfarin is a substrate)",
    );
    // Step 2: toxicity risk (general rule: increased concentration + narrow index).
    assert_true(
        &engine.query_holds("dangerous(Varfarin).").unwrap(),
        "Warfarin is at toxicity risk (increased concentration + narrow therapeutic index)",
    );
    // Step 3: safety alert (general rule: toxicity risk -> alert), with proof.
    let (alert, trace, _json) = engine.query_text_with_proof("warns(Varfarin).").unwrap();
    assert_true(&alert, "Warfarin co-prescription warrants a safety alert");
    assert!(
        trace.contains("Rule"),
        "Alert proof should show a derivation chain, got:\n{trace}"
    );

    // Negative control: apixaban (CYP3A4) — fluconazole does not inhibit CYP3A4.
    assert_false(
        &engine.query_holds("increases(Apiksaban).").unwrap(),
        "Apixaban concentration does not rise (CYP3A4 not inhibited by fluconazole)",
    );
    assert_false(
        &engine.query_holds("warns(Apiksaban).").unwrap(),
        "Apixaban co-administration produces NO alert (deduced False, not unknown)",
    );
}

/// The plain-English "why" of the toxicity-risk proof reads in real DOMAIN terms
/// under the curated overlay — instantiated with the real entities (warfarin,
/// CYP2C9), never a bare variable `X`. The dictionary-fallback (no overlay) is
/// likewise concrete and `X`-free; it just keeps the engine's literal glosses.
#[test]
fn ddi_why_toxicity_is_concrete_and_domain_termed() {
    let engine = engine_with_ddi_corpus();
    let (_r, trace) = engine.query_text_raw_proof("dangerous(Varfarin).").unwrap();

    let overlay = summarize_proof_with(&trace, Register::Spec, Some(&DRUG_INTERACTIONS_OVERLAY))
        .expect("toxicity proof has a why summary");
    // Real domain language + real names, sourced from the proof's own entities.
    assert!(
        overlay.contains("fluconazole inhibits CYP2C9"),
        "why: {overlay}"
    );
    assert!(
        overlay.contains("warfarin is metabolized by CYP2C9"),
        "why: {overlay}"
    );
    assert!(
        overlay.contains("warfarin is at toxicity risk"),
        "why: {overlay}"
    );
    assert!(
        overlay.contains("narrow therapeutic index"),
        "why: {overlay}"
    );
    // No bare algebra variable, and no raw transliterated cmevla leaked.
    assert!(!overlay.contains('X'), "bare variable leaked: {overlay}");
    assert!(
        !overlay.contains("varfarin"),
        "raw cmevla leaked: {overlay}"
    );
    assert!(
        !overlay.contains("siptucin"),
        "raw cmevla leaked: {overlay}"
    );

    // Fallback (no overlay): concrete + X-free, with the engine's literal glosses.
    let fallback = summarize_proof_with(&trace, Register::Spec, None).unwrap();
    assert!(
        fallback.contains("varfarin is in danger"),
        "why: {fallback}"
    );
    assert!(!fallback.contains('X'), "bare variable leaked: {fallback}");
    assert!(
        !fallback.contains("toxicity risk"),
        "fallback must stay literal: {fallback}"
    );

    // The collapsed tree's universal rule reads "every drug …", not "if X …".
    let tree = render_collapsed_text_with(
        &trace,
        Register::Spec,
        0,
        false,
        Some(&DRUG_INTERACTIONS_OVERLAY),
    );
    assert!(
        tree.contains("every drug that has a raised concentration and has a narrow therapeutic index is at toxicity risk"),
        "tree:\n{tree}"
    );
    assert!(!tree.contains('X'), "bare variable leaked in tree:\n{tree}");
}

/// The 3-hop safety-alert "why" chains all the way to the alert, instantiated and
/// patient-gated ("Adam takes warfarin"), with no bare variable.
#[test]
fn ddi_why_alert_chains_to_the_regimen() {
    let engine = engine_with_ddi_corpus();
    let (_r, trace) = engine.query_text_raw_proof("warns(Varfarin).").unwrap();
    let why = summarize_proof_with(&trace, Register::Spec, Some(&DRUG_INTERACTIONS_OVERLAY))
        .expect("alert proof has a why summary");
    assert!(why.contains("warfarin is at toxicity risk"), "why: {why}");
    assert!(why.contains("Adam takes warfarin"), "why: {why}");
    assert!(
        why.contains("warfarin warrants a safety alert"),
        "why: {why}"
    );
    assert!(!why.contains('X'), "bare variable leaked: {why}");
}

/// The toxicity rule is GENERAL: phenytoin, a different narrow-index CYP2C9
/// substrate, reaches toxicity risk (ckape) through the SAME general rule as
/// warfarin (no per-drug rule). But the ALERT is patient-gated — phenytoin is NOT
/// in Adam's regimen, so it warrants no alert. Pharmacological risk is general;
/// the actionable alert is patient-specific.
#[test]
fn ddi_general_rules_fire_for_second_drug() {
    let engine = engine_with_ddi_corpus();
    assert_true(
        &engine.query_holds("dangerous(Fenitoin).").unwrap(),
        "Phenytoin reaches toxicity risk via the same general toxicity rule as warfarin",
    );
    assert_false(
        &engine.query_holds("warns(Fenitoin).").unwrap(),
        "But phenytoin warrants NO alert: Adam does not take it (the alert is regimen-gated)",
    );
}

/// The toxicity step requires BOTH a concentration increase AND a narrow
/// therapeutic index. Two negative controls confirm the conjunction is real:
/// (a) a wide-margin drug whose concentration rises is NOT flagged; (b) a
/// narrow-index drug with no interaction (no concentration rise) is NOT flagged.
#[test]
fn ddi_toxicity_requires_both_conditions() {
    // (a) concentration rises, but NOT narrow-index -> no toxicity risk.
    // The toxicity step is the general conjunctive universal rule.
    let wide = engine_with_facts(&[
        "chemical(Raxitidin).",
        "increases(Raxitidin).", // concentration rises
        "dangerous(every chemical where increases where thin).",
        "warns(every chemical where dangerous).",
    ]);
    assert_false(
        &wide.query_holds("dangerous(Raxitidin).").unwrap(),
        "A wide-margin drug with raised concentration is not at toxicity risk",
    );
    assert_false(
        &wide.query_holds("warns(Raxitidin).").unwrap(),
        "A wide-margin drug with raised concentration warrants no alert",
    );

    // (b) narrow-index, but NO interaction (no concentration rise) -> no risk.
    // This is the discriminating control: it fails if the toxicity step ignores
    // the concentration-increase premise.
    let narrow = engine_with_facts(&[
        "chemical(Narotil).",
        "thin(Narotil).", // narrow index, but no interaction
        "dangerous(every chemical where increases where thin).",
        "warns(every chemical where dangerous).",
    ]);
    assert_false(
        &narrow.query_holds("dangerous(Narotil).").unwrap(),
        "A narrow-index drug with no interaction is not at toxicity risk",
    );
    assert_false(
        &narrow.query_holds("warns(Narotil).").unwrap(),
        "A narrow-index drug with no interaction warrants no alert",
    );
}

/// Belief revision (non-monotonic), mechanism-side: an alert is not "baked in" —
/// it is re-derived from current facts. The clinically canonical move: the
/// interacting drug is discontinued. Retracting "fluconazole inhibits CYP2C9"
/// removes the mechanism's entry premise, so the concentration rise, the toxicity
/// risk, and the alert all dissolve in one step. This mirrors the shipped corpus:
/// warfarin is on Adam's chart (so it alerts), phenytoin is NOT (so it reaches
/// toxicity RISK but no alert — the regimen gate). The shared inhibitor means
/// retracting it dissolves the toxicity risk for BOTH substrates at once, and
/// warfarin's alert with it.
#[test]
fn ddi_belief_revision_discontinue_inhibitor() {
    let engine = fresh_engine();
    for line in [
        "chemical(Varfarin).",
        "chemical(Fenitoin).",
        "chemical(Flukonazol).",
        "metabolized_by(Varfarin, Siptucin).",
        "metabolized_by(Fenitoin, Siptucin).",
        "thin(Varfarin).",
        "thin(Fenitoin).",
        "uses(Adam, Varfarin).",
    ] {
        engine.assert_text(line).unwrap();
    }
    let inhibits_id = engine
        .assert_text("prevents(Flukonazol, Siptucin).")
        .unwrap()[0];
    for line in [
        "prevents(Flukonazol, Siptucin) & metabolized_by(Varfarin, Siptucin) -> increases(Varfarin).",
        "prevents(Flukonazol, Siptucin) & metabolized_by(Fenitoin, Siptucin) -> increases(Fenitoin).",
        "dangerous(every chemical where increases where thin).",
        "all $da: dangerous($da) & uses(Adam, $da) -> warns($da).",
    ] {
        engine.assert_text(line).unwrap();
    }

    // ── Before discontinuation: warfarin alerts; phenytoin is at risk but not on
    //    the chart, so it reaches ckape without an alert (the regimen gate) ──
    assert_true(
        &engine.query_holds("warns(Varfarin).").unwrap(),
        "Warfarin alerts: at risk via the inhibitor AND on Adam's chart",
    );
    assert_true(
        &engine.query_holds("dangerous(Fenitoin).").unwrap(),
        "Phenytoin is at toxicity risk via the same shared inhibitor",
    );
    assert_false(
        &engine.query_holds("warns(Fenitoin).").unwrap(),
        "But phenytoin raises no alert: Adam does not take it (regimen-gated)",
    );

    // ── Discontinue fluconazole: retract the inhibition fact ──
    engine.retract_fact(inhibits_id).unwrap();

    assert_false(
        &engine.query_holds("increases(Varfarin).").unwrap(),
        "After discontinuation, warfarin's concentration no longer rises",
    );
    assert_false(
        &engine.query_holds("dangerous(Varfarin).").unwrap(),
        "After discontinuation, warfarin's toxicity basis is gone",
    );
    assert_false(
        &engine.query_holds("warns(Varfarin).").unwrap(),
        "After discontinuation, the warfarin alert is automatically withdrawn",
    );
    assert_false(
        &engine.query_holds("dangerous(Fenitoin).").unwrap(),
        "Discontinuing the shared inhibitor also clears phenytoin's toxicity risk",
    );
}

/// Belief revision (non-monotonic), patient-side: discontinuing a drug from the
/// REGIMEN withdraws its alert while the drug-level toxicity risk stays derivable.
/// Retracting "Adam takes warfarin" flips the warfarin alert FALSE, but warfarin is
/// still pharmacologically at risk (ckape) — the alert is gated on the regimen, the
/// risk is not. This is the patient-specific belief-revision move the regimen-gated
/// alert rule enables (and it exercises retract+rebuild over a `pilno` ground fact
/// without the historical ground-conditional hang).
#[test]
fn ddi_belief_revision_discontinue_drug() {
    let engine = fresh_engine();
    for line in [
        "chemical(Varfarin).",
        "chemical(Flukonazol).",
        "metabolized_by(Varfarin, Siptucin).",
        "thin(Varfarin).",
        "prevents(Flukonazol, Siptucin).",
    ] {
        engine.assert_text(line).unwrap();
    }
    let takes_id = engine.assert_text("uses(Adam, Varfarin).").unwrap()[0];
    for line in [
        "prevents(Flukonazol, Siptucin) & metabolized_by(Varfarin, Siptucin) -> increases(Varfarin).",
        "dangerous(every chemical where increases where thin).",
        "all $da: dangerous($da) & uses(Adam, $da) -> warns($da).",
    ] {
        engine.assert_text(line).unwrap();
    }

    // ── Before: warfarin is at risk AND Adam takes it → alert ──
    assert_true(
        &engine.query_holds("dangerous(Varfarin).").unwrap(),
        "Warfarin is at toxicity risk",
    );
    assert_true(
        &engine.query_holds("warns(Varfarin).").unwrap(),
        "Adam takes warfarin, so its alert fires",
    );

    // ── Discontinue warfarin for Adam: retract the regimen fact ──
    engine.retract_fact(takes_id).unwrap();

    assert_true(
        &engine.query_holds("dangerous(Varfarin).").unwrap(),
        "Warfarin is STILL pharmacologically at toxicity risk (drug-level, not regimen-gated)",
    );
    assert_false(
        &engine.query_holds("warns(Varfarin).").unwrap(),
        "But the alert is withdrawn: Adam no longer takes warfarin",
    );
}

/// Witness extraction: enumerate which drugs are CYP2C9 substrates. The query
/// finds the entities bound to the existential variable across the fact store.
#[test]
fn ddi_witness_cyp2c9_substrates() {
    let engine = engine_with_ddi_corpus();
    let witnesses = engine
        .query_find_text("metabolized_by($da, Siptucin).")
        .unwrap();
    // Collect the entity bound to `da` in each witness set.
    let mut substrates: Vec<String> = witnesses
        .iter()
        .filter_map(|set| {
            set.iter()
                .find(|b| b.variable == "$da")
                .map(|b| nibli_engine::display_term(&b.term))
        })
        .collect();
    substrates.sort();
    substrates.dedup();
    assert!(
        substrates.iter().any(|s| s.contains("varfarin")),
        "warfarin should be a CYP2C9 substrate witness, got {substrates:?}"
    );
    assert!(
        substrates.iter().any(|s| s.contains("fenitoin")),
        "phenytoin should be a CYP2C9 substrate witness, got {substrates:?}"
    );
    assert!(
        !substrates.iter().any(|s| s.contains("apiksaban")),
        "apixaban (CYP3A4) must NOT appear as a CYP2C9 substrate, got {substrates:?}"
    );
}

/// Aggregation API: count the drugs in the patient's regimen (polypharmacy
/// count). Exercises NibliEngine::count_witnesses_text added for this case study.
#[test]
fn ddi_regimen_count_aggregation() {
    let engine = engine_with_ddi_corpus();
    let n = engine.count_witnesses_text("uses(Adam, $da).").unwrap();
    assert_eq!(
        n, 2,
        "Adam's regimen contains exactly two drugs (warfarin + fluconazole)"
    );
}

/// Aggregation API: sum a numeric property across witnesses. Exercises
/// NibliEngine::aggregate_text over event-decomposed numeric facts.
#[test]
fn ddi_dose_sum_aggregation() {
    // quantity(drug, amount): "drug measures <amount>" (the curated klani alias).
    let engine = engine_with_facts(&[
        "quantity(Varfarin, 5).", // 5
        "quantity(Fenitoin, 7).", // 7
    ]);
    let total = engine
        .aggregate_text("quantity($da, $de).", "$de", EngineAggregateOp::Sum)
        .unwrap();
    assert_eq!(total, Some(12.0), "Summed dose across drugs should be 12");
}

/// Regression (query-level DoS): cyclic rules through the FULL pipeline must not hang
/// the witness search. `ro lo gerku cu danlu` + `ro lo danlu cu gerku` is a
/// relation-level cycle; before the `cycle_key` backward-chain guard,
/// `count_witnesses_text("dog($da).")` spun at ~100% CPU for 30+ minutes (each step
/// mints a fresh event Skolem, so the raw cycle guard never fired). Now the cycle is
/// cut → enumeration incomplete → count REFUSES with `Err`. Watchdog-guarded so a
/// regression FAILS rather than hangs CI.
#[test]
fn cyclic_rules_do_not_hang_count() {
    use std::sync::mpsc;
    use std::time::Duration;
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let engine = engine_with_facts(&["animal(every dog).", "dog(every animal).", "cat(Rex)."]);
        let _ = tx.send(engine.count_witnesses_text("dog($da).").is_err());
    });
    match rx.recv_timeout(Duration::from_secs(20)) {
        Ok(true) => {}
        Ok(false) => panic!("cyclic count_witnesses_text must refuse (Err), not undercount"),
        Err(_) => panic!(
            "cyclic count_witnesses_text did NOT terminate within 20s \
             — the backward-chain cycle guard regressed"
        ),
    }
}

/// Temporal reasoning: a present-tense alert holds; a past-tense query for the
/// same alert does not (tense discrimination), matching the engine's temporal
/// contract used elsewhere in the book.
#[test]
fn ddi_temporal_alert_discrimination() {
    let engine = engine_with_facts(&["now warns(Varfarin)."]);
    assert_true(
        &engine.query_holds("now warns(Varfarin).").unwrap(),
        "A present-tense alert holds",
    );
    assert_false(
        &engine.query_holds("past warns(Varfarin).").unwrap(),
        "There was no alert in the past (tense discrimination)",
    );
}

// ─── Determinism pin (todo.md: witness/proof output ordering) ────────

#[test]
fn find_witness_output_order_is_deterministic() {
    // Full-pipeline pin for the HashSet-derived-ordering item: witness
    // candidates and domain members were iterated straight out of HashSets,
    // so `ma` find output order varied with the hasher seed. Two fresh
    // engines (each with its own RandomState instances) loading the same
    // corpus must produce identical ordered find results, and a repeated
    // query on one engine must be order-stable — binding sets are sorted
    // canonically at the nibli-reason query_find boundary.
    //
    // NOTE: the corpus is asserted in the SAME order in both engines because
    // event-existential Skolem names (sk_N) are assertion-order dependent by
    // design; cross-order canonicalization is pinned at the nibli-reason level on
    // Skolem-free ground facts. An in-process pin is weaker than two true
    // processes (different global seeds), but the sort makes the order
    // seed-independent by construction.
    let lines = ["dog(Zod).", "dog(Alis).", "dog(Mik).", "dog(Bob)."];
    let e1 = engine_with_facts(&lines);
    let e2 = engine_with_facts(&lines);

    let render = |engine: &NibliEngine| -> Vec<String> {
        engine
            .query_find_text("dog(?).")
            .unwrap()
            .iter()
            .map(|bindings| {
                bindings
                    .iter()
                    .map(|b| format!("{} = {:?}", b.variable, b.term))
                    .collect::<Vec<_>>()
                    .join(", ")
            })
            .collect()
    };

    let r1a = render(&e1);
    let r1b = render(&e1);
    let r2 = render(&e2);

    assert!(!r1a.is_empty(), "ma gerku should find witnesses");
    assert_eq!(r1a, r1b, "repeated find on one engine must be order-stable");
    assert_eq!(
        r1a, r2,
        "a fresh engine on the same corpus must produce identical find order"
    );
}

#[test]
fn find_dependent_skolem_witness_event_decomposed_is_bound() {
    // Ch9 verify-book-capture regression, through the REAL event-decomposed
    // pipeline (the flat nibli-reason unit test does not exercise Neo-Davidsonian
    // event decomposition). `?? la .adam. nelci ma` over `gerku(adam)` +
    // `ro lo gerku cu nelci lo mlatu` must return witnesses whose dependent
    // Skolem terms are BOUND (`sk_N(adam)`), never the unbound conclusion
    // template (`sk_N(_)` / `sk_N(?..)`), with no duplicate binding sets.
    let engine = engine_with_facts(&["dog(Adam).", "likes(every dog, some cat)."]);
    let witnesses = engine.query_find_text("likes(Adam, ?).").unwrap();
    assert!(!witnesses.is_empty(), "the rule provides a witness cat");

    let terms: Vec<String> = witnesses
        .iter()
        .flat_map(|set| set.iter())
        .map(|b| nibli_engine::display_term(&b.term))
        .collect();
    assert!(
        terms.iter().all(|t| !t.contains("(_)") && !t.contains('?')),
        "no witness term may be an unbound dependent Skolem, got {terms:?}"
    );
    assert!(
        terms.iter().any(|t| t.contains("(adam)")),
        "the dependent witness must be bound to its dependency adam, got {terms:?}"
    );

    // No duplicate binding sets (the dedup at the query_find boundary).
    let mut seen = std::collections::HashSet::new();
    for set in &witnesses {
        let key: Vec<(String, String)> = set
            .iter()
            .map(|b| (b.variable.clone(), nibli_engine::display_term(&b.term)))
            .collect();
        assert!(
            seen.insert(key),
            "duplicate binding set in find output: {witnesses:?}"
        );
    }
}

// ════════════════════════════════════════════════════════════════════
// Surface-numeric evaluation (todo.md: event decomposition shadowed the
// numeric evaluators — every surface arithmetic/comparison query was FALSE)
// ════════════════════════════════════════════════════════════════════

#[test]
fn surface_numeric_pilji_true_and_false() {
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("product(10, 2, 5).").unwrap(),
        "10 = 2 × 5 must be derivable through surface Lojban",
    );
    assert_false(
        &engine.query_holds("product(11, 2, 5).").unwrap(),
        "11 = 2 × 5 must be FALSE through surface Lojban",
    );
}

// Module-level stubs for the per-instance compute-dispatch test below.
// A trivial backend that "knows" only `tenfa` (exponentiation), which nibli-reason has
// no built-in for — so the query can only succeed via the registered dispatch.
fn stub_tenfa_eval(rel: &str, _args: &[EngineLogicalTerm]) -> Result<bool, String> {
    Ok(rel == "exponential")
}

fn stub_tenfa_batch(reqs: &[EngineComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter()
        .map(|r| Ok(r.relation == "exponential"))
        .collect()
}

#[test]
fn per_instance_compute_dispatch_is_isolated() {
    // engine_a registers a per-instance dispatch → external `tenfa` resolves TRUE.
    let mut engine_a = fresh_engine();
    engine_a.register_compute_predicate("exponential".to_string());
    engine_a.set_compute_dispatch(stub_tenfa_eval, stub_tenfa_batch);
    assert_true(
        &engine_a.query_holds("exponential(8, 2, 3).").unwrap(),
        "an engine with per-instance dispatch must resolve external `tenfa`",
    );

    // engine_b: SAME compute-predicate registration, but NO dispatch set. With the
    // old THREAD-LOCAL dispatch, engine_a's registration would leak to engine_b on
    // the same thread; per-instance dispatch keeps them independent → `tenfa` is
    // unresolved (no built-in, no backend) and the query is not TRUE.
    let mut engine_b = fresh_engine();
    engine_b.register_compute_predicate("exponential".to_string());
    let r = engine_b.query_holds("exponential(8, 2, 3).").unwrap();
    // Isolation: engine_a's dispatch must NOT leak here, so `tenfa` stays unresolved.
    assert!(
        !r.is_true(),
        "an engine WITHOUT dispatch must not resolve external `tenfa`: got {r:?}"
    );
    // And an unresolved compute predicate is UNKNOWN(backend-unavailable), never a
    // definitive FALSE (a backend we cannot consult is not a derived falsehood).
    assert_eq!(
        r.detail_label(),
        Some("backend-unavailable"),
        "unresolved compute dispatch must surface backend-unavailable, not FALSE: got {r:?}"
    );
}

#[test]
fn overflowing_numeric_literal_fails_closed_at_parse() {
    // A numeric literal too large for an f64 (~320 nines → +inf) is rejected AT
    // THE PARSE BOUNDARY (fail closed, mirroring the u32 quantifier guard): it
    // never becomes a Number(inf) inside the pipeline. This supersedes this
    // test's previous vehicle for the NonFinite contract — a giant `li` literal
    // reaching `dunli` and surfacing UNKNOWN(non-finite) — because the literal
    // now cannot enter at all, which is strictly stronger for this input class.
    // The downstream UNKNOWN(non-finite) catches remain for non-finite values
    // arising IN-pipeline (flat buffers can still carry non-finite Numbers) but
    // are now pinned by NO test — regaining that pin at the nibli-reason flat level is
    // owned by the try_numeric_comparison tracker bullet.
    let nines = "so ".repeat(320); // 999…9 > f64::MAX → +inf pre-guard
    let engine = fresh_engine();
    let err = engine
        .query_holds(&format!("li {nines}cu dunli li {nines}"))
        .expect_err("an overflowing numeric literal must be a parse error, not a verdict");
    assert!(
        matches!(err, EngineError::Syntax(_)),
        "the overflow rejection must be the typed syntax error, got: {err}"
    );
}

#[test]
fn surface_numeric_sumji_dilcu() {
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("sum(5, 2, 3).").unwrap(),
        "5 = 2 + 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("sum(6, 2, 3).").unwrap(),
        "6 = 2 + 3 must be FALSE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("quotient(3, 6, 2).").unwrap(),
        "3 = 6 / 2 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("quotient(3, 6, 0).").unwrap(),
        "division by zero must be FALSE, not an error",
    );
}

#[test]
fn surface_numeric_float_tolerance() {
    // `li no pi ci` = 0.3, `li no pi pa` = 0.1, `li no pi re` = 0.2 (the `pi`
    // decimal point). 0.1 + 0.2 = 0.30000000000000004 in IEEE-754, but the
    // engine uses tolerant equality, so `0.3 = 0.1 + 0.2` is TRUE end-to-end
    // through nibli-kr → nibli-semantics → nibli-reason (not the surprising exact-`==` FALSE).
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("sum(0.3, 0.1, 0.2).").unwrap(),
        "0.3 = 0.1 + 0.2 must be TRUE (tolerant float equality)",
    );
}

/// A local TCP server that replies with a fixed JSON line to each request line —
/// stands in for the Python compute backend (`python/nibli_backend.py`).
fn mock_compute_server(response: &str) -> String {
    use std::io::{BufRead, BufReader, Write};
    use std::net::TcpListener;
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    let resp = response.to_string();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(stream) = stream else { continue };
            let mut reader = BufReader::new(stream);
            loop {
                let mut line = String::new();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        let mut r = resp.clone();
                        r.push('\n');
                        if reader.get_mut().write_all(r.as_bytes()).is_err() {
                            break;
                        }
                        let _ = reader.get_mut().flush();
                    }
                }
            }
        }
    });
    addr
}

#[test]
fn native_compute_backend_dispatches_external_predicate() {
    // `tenfa` (exponent) is NOT built-in arithmetic, so it dispatches to the
    // external backend. With the native client wired to a mock that returns
    // `{"result": true}`, the query routes engine → nibli-reason → native client → mock.
    // (`li bi` = 8, `li re` = 2, `li ci` = 3 → "is 8 = 2^3?")
    let addr = mock_compute_server(r#"{"result": true}"#);
    let mut engine = fresh_engine();
    engine.enable_compute_backend(&addr);
    engine.register_compute_predicate("exponential".to_string());
    assert_true(
        &engine.query_holds("exponential(8, 2, 3).").unwrap(),
        "tenfa dispatches through the native TCP client to the backend",
    );
}

#[test]
fn native_compute_backend_is_opt_in() {
    // Without `enable_compute_backend`, an external predicate stays unprovable —
    // the dispatch hook is unregistered (per-instance isolation).
    let mut engine = fresh_engine();
    engine.register_compute_predicate("exponential".to_string());
    let r = engine.query_holds("exponential(8, 2, 3).").unwrap();
    assert!(
        !r.is_true(),
        "tenfa with no backend wired must not be TRUE: {r:?}"
    );
}

/// End-to-end against the REAL Python reference backend (`python/nibli_backend.py`),
/// which actually computes `tenfa` (exponent). Opt-in (needs python3 + the script);
/// run with `cargo test -p nibli-engine --test integration -- --ignored`.
#[test]
#[ignore = "starts the Python compute backend; run with --ignored from the repo root"]
fn native_compute_backend_real_python_tenfa() {
    let port = "15556";
    let addr = format!("127.0.0.1:{port}");
    // The test CWD is the crate dir, so resolve the script from the workspace root.
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/../python/nibli_backend.py");
    let mut child = std::process::Command::new("python3")
        .args([script, "--port", port])
        .spawn()
        .expect("failed to start python3 (needs python3 on PATH)");
    // Wait for the backend to accept connections.
    let mut ready = false;
    for _ in 0..50 {
        if std::net::TcpStream::connect(&addr).is_ok() {
            ready = true;
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    let run = || {
        let mut engine = fresh_engine();
        engine.enable_compute_backend(&addr);
        engine.register_compute_predicate("exponential".to_string());
        // 8 = 2^3 (TRUE); 9 = 2^3 (FALSE) — the backend does the arithmetic.
        let t = engine.query_holds("exponential(8, 2, 3).").unwrap();
        let f = engine.query_holds("exponential(9, 2, 3).").unwrap();
        (t, f)
    };
    let result = std::panic::catch_unwind(run);
    let _ = child.kill();
    let _ = child.wait(); // reap the child so it doesn't linger as a zombie
    assert!(ready, "Python backend did not start on {addr}");
    let (t, f) = result.expect("query panicked");
    assert_true(&t, "8 = 2^3 must be TRUE through the real Python backend");
    assert_false(&f, "9 = 2^3 must be FALSE through the real Python backend");
}

#[test]
fn surface_numeric_comparison_greater_less_num_equal() {
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("greater(5, 3).").unwrap(),
        "5 > 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("greater(3, 5).").unwrap(),
        "3 > 5 must be FALSE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("less(2, 3).").unwrap(),
        "2 < 3 must be TRUE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("num_equal(3, 3).").unwrap(),
        "3 == 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("num_equal(3, 2).").unwrap(),
        "3 == 2 must be FALSE through surface Lojban",
    );
}

#[test]
fn assert_numeric_comparison_rejected() {
    // A zmadu/mleca/dunli comparison over numeric literals is computed ground
    // truth, not an assertable fact — the engine evaluates it at query time and
    // the computed value always wins, so an asserted fact could only ever be a
    // shadowed (unreachable) fact. Fail closed at assert time rather than store it.
    let engine = fresh_engine();
    for line in ["greater(3, 5).", "less(5, 3).", "num_equal(5, 3)."] {
        let err = engine
            .assert_text(line)
            .expect_err("asserting a numeric comparison must be rejected");
        assert!(
            err.to_string().contains("computed comparison"),
            "expected the computed-comparison rejection for `{line}`, got: {err}"
        );
    }

    // GUARD: a NON-numeric comparison is a relational fact (the taller-than
    // reading) and still asserts + stores normally.
    engine
        .assert_text("greater(Alis, Bob).")
        .expect("a non-numeric relational comparison must still assert");

    // GUARD: the QUERY path is unchanged — comparisons still compute.
    assert_true(
        &engine.query_holds("greater(5, 3).").unwrap(),
        "5 > 3 must still compute TRUE at query time",
    );
}

#[test]
fn surface_numeric_negation() {
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("~greater(3, 5).").unwrap(),
        "NOT(3 > 5) must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("~greater(5, 3).").unwrap(),
        "NOT(5 > 3) must be FALSE through surface Lojban",
    );
}

#[test]
fn surface_numeric_traced_verdicts_agree() {
    // The traced path must agree with the untraced verdict (both evaluators
    // carry the numeric-group hook) and record a compute-check step.
    let engine = fresh_engine();
    let (verdict, trace, _json) = engine.query_text_with_proof("product(10, 2, 5).").unwrap();
    assert_true(&verdict, "traced 10 = 2 × 5 must be TRUE");
    assert!(
        trace.contains("product"),
        "trace should mention the computed relation: {trace}"
    );
}

#[test]
fn closed_world_false_carries_cwa_note_but_numeric_false_does_not() {
    let engine = fresh_engine();
    // Absence-driven FALSE: `gerku(adam)` is simply not derivable → a closed-world FALSE,
    // which must carry the CWA caveat (the dual of the NAF note) so a reader does not
    // mistake "not derivable" for "proved false".
    let (v1, proof1, _) = engine.query_text_with_proof("dog(Adam).").unwrap();
    assert!(v1.is_false(), "a missing fact must be FALSE: got {v1:?}");
    assert!(
        proof1.contains("FALSE is closed-world"),
        "an absence-driven FALSE must carry the closed-world caveat: {proof1}"
    );
    // Numeric-decided FALSE: `5 = 3` is genuinely false (a decided computation), NOT
    // closed-world — it must NOT carry the caveat.
    let (v2, proof2, _) = engine.query_text_with_proof("num_equal(5, 3).").unwrap();
    assert!(v2.is_false(), "`5 = 3` must be FALSE: got {v2:?}");
    assert!(
        !proof2.contains("FALSE is closed-world"),
        "a numeric-decided FALSE must NOT carry the closed-world caveat: {proof2}"
    );
}

// ════════════════════════════════════════════════════════════════════
// Direct-injected facts are text-queryable (event-decompose at injection)
// ════════════════════════════════════════════════════════════════════

#[test]
fn injected_fact_matches_surface_text_query() {
    // A directly-injected fact must now match a surface text query — the public
    // injection API event-decomposes to the same shape text assertion produces.
    // RED before fix: flat gerku(adam) vs the query's ∃ev. gerku(ev) ∧
    // gerku_x1(ev, adam) ∧ gerku_x2(ev, zo'e) never matched.
    let engine = fresh_engine();
    engine
        .assert_fact_direct(
            "dog".to_string(),
            vec![nibli_engine::EngineLogicalTerm::Constant(
                "adam".to_string(),
            )],
        )
        .unwrap();
    assert_true(
        &engine.query_holds("dog(Adam).").unwrap(),
        "directly-injected gerku(adam) must satisfy the surface text query",
    );
}

#[test]
fn injected_fact_multiplace_arity_padding_matches_text_query() {
    // klama is 5-place. Injecting only x1,x2 must pad x3..x5 with zo'e to the
    // SAME shape `la .adam. cu klama la .paris.` compiles to, so it matches.
    let engine = fresh_engine();
    engine
        .assert_fact_direct(
            "goes".to_string(),
            vec![
                nibli_engine::EngineLogicalTerm::Constant("adam".to_string()),
                nibli_engine::EngineLogicalTerm::Constant("paris".to_string()),
            ],
        )
        .unwrap();
    assert_true(
        &engine.query_holds("goes(Adam, Paris).").unwrap(),
        "injecting a 5-place predicate with 2 args must pad and still match the text query",
    );
}

#[test]
fn injected_known_over_arity_fails_closed() {
    // `product` has corpus arity 3 — injecting a 4th argument must ERROR
    // (the injected-arity policy), never silently drop it (pre-policy
    // behavior: fit_args truncated with no signal).
    let engine = fresh_engine();
    let e = engine
        .assert_fact_direct(
            "product".to_string(),
            (0..4)
                .map(|n| nibli_engine::EngineLogicalTerm::Number(n as f64))
                .collect(),
        )
        .unwrap_err();
    let msg = format!("{e}");
    assert!(
        msg.contains("arity 3") && msg.contains("4 arguments"),
        "{msg}"
    );
}

#[test]
fn injected_unknown_arity_is_callers_count() {
    // An unknown relation takes the caller's argument count as ground truth
    // (no arity-2 guess): a 3-arg injection is ACCEPTED — pre-policy it was
    // silently truncated to 2 args. The decomposed SHAPE (exactly 3 role
    // predicates, no phantom x2 for a 1-arg fact) is pinned at the seam that
    // decides it: nibli-semantics's `injected_fact_tests`. (The strict-mode
    // signature registry cannot observe this — each decomposed role predicate
    // registers its own arity, so a role-count difference is a different
    // relation SET, not an arity conflict.)
    let engine = fresh_engine();
    let args: Vec<_> = ["a", "b", "c"]
        .iter()
        .map(|n| nibli_engine::EngineLogicalTerm::Constant(n.to_string()))
        .collect();
    engine
        .assert_fact_direct("zzz_unknown_rel".to_string(), args)
        .expect("a 3-arg unknown injected fact must be accepted at arity 3");
}

#[test]
fn injected_fact_is_findable_as_witness() {
    // The injected fact must also be discoverable through witness extraction.
    let engine = fresh_engine();
    engine
        .assert_fact_direct(
            "dog".to_string(),
            vec![nibli_engine::EngineLogicalTerm::Constant(
                "adam".to_string(),
            )],
        )
        .unwrap();
    let witnesses = engine.query_find_text("dog(?).").unwrap();
    assert!(
        !witnesses.is_empty(),
        "injected gerku(adam) should yield a witness binding"
    );
    let mentions_adam = witnesses
        .iter()
        .flat_map(|set| set.iter())
        .any(|b| nibli_engine::display_term(&b.term).contains("adam"));
    assert!(
        mentions_adam,
        "the discovered witness should be adam: {witnesses:?}"
    );
}

#[test]
fn belief_does_not_leak_as_actuality() {
    // Referential opacity: asserting `mi krici lo du'u mi klama` ("I believe that I
    // go") must NOT make the bare actuality `mi klama` ("I go") hold — believing P
    // does not entail P. The belief itself stays queryable, and believing a DIFFERENT
    // proposition is not satisfied (abstraction content is not conflated).
    let engine = fresh_engine();
    engine
        .assert_text("believe(me, fact { goes(me) }).")
        .unwrap();

    assert_false(
        &engine.query_holds("goes(me).").unwrap(),
        "believing P must not entail P (no abstraction-content leak)",
    );
    assert_true(
        &engine
            .query_holds("believe(me, fact { goes(me) }).")
            .unwrap(),
        "the belief itself is preserved and queryable",
    );
    assert_false(
        &engine
            .query_holds("believe(me, fact { eats(me) }).")
            .unwrap(),
        "believing P must not satisfy a query about believing a different proposition",
    );
}

#[test]
fn abstraction_subject_does_not_leak_inner_predicate() {
    // The review's example: `lo du'u mi klama kei cu barda` ("the fact-that-I-go is
    // big") must not assert `mi klama` ("I go") as a queryable truth.
    let engine = fresh_engine();
    engine.assert_text("big(fact { goes(me) }).").unwrap();
    assert_false(
        &engine.query_holds("goes(me).").unwrap(),
        "an abstraction used as a subject must not leak its inner predicate",
    );
}

// ─── post-reset fail-closed queries (the pro-claim machinery died at THE DROP) ───

#[test]
fn unresolvable_query_after_reset_errors() {
    // The Lojban-era `go'i` (repeat-last-claim) machinery is gone; the spelling
    // is now just an unresolvable word. Pin that a reset engine fails such a
    // query CLOSED (a compile error, never a fabricated verdict).
    let engine = engine_with_facts(&["dog(Adam)."]);
    engine.reset();
    assert!(
        engine.query_holds("go'i").is_err(),
        "an unresolvable spelling must error, not answer"
    );
}

#[test]
fn predicate_less_clause_rejected() {
    // A bare argument / predicate-less clause (`ro lo gerku`) is NOT a complete proposition.
    // nibli-kr rejects it at PARSE with a clear, distinct Syntax error, instead of
    // fabricating a `go'i` that fail-closes downstream with the cryptic "go'i has no
    // antecedent". This is what `nibli-validate` / the book's verify tool now see.
    let engine = fresh_engine();
    let err = engine.assert_text("every dog").unwrap_err();
    assert!(
        matches!(err, EngineError::Syntax(_)),
        "a bare sumti must be a Syntax error, got {err:?}"
    );
    assert!(
        err.to_string().contains("expected a predicate word"),
        "expected the bare-term parse rejection, got: {err}"
    );
    // A complete proposition still asserts fine (the change is scoped to predicate-less clauses).
    assert!(engine.assert_text("dog(Adam).").is_ok());
}
