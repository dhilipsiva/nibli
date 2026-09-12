//! Integration tests for the nibli-engine: full pipeline (parse → compile → reason).
//!
//! Each test creates a fresh NibliEngine, asserts Lojban text, and queries with proof.
//! No WASM, no HTTP — exercises nibli-kr+nibli-semantics+nibli-reason directly via Rust crate calls.

use nibli_engine::{
    EngineAggregateOp, EngineAggregateOutcome, EngineComputeRequest, EngineError,
    EngineLogicBuffer, EngineLogicNode, EngineLogicalTerm, EngineQueryResult, EngineUnknownReason,
    EngineWitnessOrigin, NibliEngine,
};
use nibli_render::{
    DRUG_INTERACTIONS_OVERLAY, GDPR_OVERLAY, Register, render_collapsed_text_with,
    summarize_proof_with,
};
use nibli_store::NibliStore;
use redb::{Database, TableDefinition};
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

fn engine_with_import_facts(enabled: bool, lines: &[&str]) -> NibliEngine {
    let engine = fresh_engine();
    engine
        .set_existential_import(enabled)
        .expect("fresh engine must accept the requested import profile");
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
    let _ = fs::remove_file(path.with_extension("typed.redb"));
}

// ─── Basic assertion and query ──────────────────────────────────────

#[test]
fn stacked_tense_deontic_is_a_fail_closed_surface_error() {
    let engine = fresh_engine();
    let valid_id = engine.assert_text("dog(Rex).").unwrap()[0];

    for text in [
        "must past dog(Rex).",
        "past must dog(Rex).",
        "all $x: must past dog($x) -> animal($x).",
        "all $x: dog($x) -> past must animal($x).",
        "all $x: person($x) & must past ~dog($x) -> animal($x).",
        "all $x: person($x) & past must ~dog($x) -> animal($x).",
    ] {
        let error = engine
            .assert_text(text)
            .expect_err("stacked assertion/rule must fail closed");
        assert!(
            error.to_string().contains("cannot be stacked"),
            "{text}: {error}"
        );
    }
    assert_eq!(
        engine.list_facts().unwrap().len(),
        1,
        "rejected source mutated KB"
    );

    for query in ["must past dog(Rex).", "past must dog(Rex)."] {
        let error = engine
            .query_holds(query)
            .expect_err("stacked query must fail closed");
        assert!(
            error.to_string().contains("cannot be stacked"),
            "{query}: {error}"
        );
        let error = engine
            .query_text_with_proof(query)
            .expect_err("stacked proof query must fail before producing a trace");
        assert!(
            error.to_string().contains("cannot be stacked"),
            "{query}: {error}"
        );
    }

    engine.retract_fact(valid_id).unwrap();
    assert!(engine.list_facts().unwrap().is_empty());
    assert_false(
        &engine.query_holds("dog(Rex).").unwrap(),
        "ordinary retraction must remain sound after rejected stacks",
    );
}

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

// ─── Post-DROP invariant: no Lojban in reader-facing proof output ───

/// Every reader-facing rendering of a trace, for one query.
///
/// `[Why]` (`summarize_proof`), the default collapsed proof view, and the
/// `:proof-verbose` full trace — the three surfaces nibli-host prints and the
/// UI mirrors. Returns them labelled so a failure names the leaking surface.
fn rendered_proof_surfaces(engine: &NibliEngine, query: &str) -> Vec<(&'static str, String)> {
    let (_r, trace) = engine.query_text_raw_proof(query).unwrap();
    let mut out = vec![
        (
            "collapsed",
            render_collapsed_text_with(&trace, Register::Spec, 2, true, None),
        ),
        (
            "verbose",
            nibli_render::render_proof_text(&trace, Register::Spec),
        ),
    ];
    if let Some(why) = nibli_render::summarize_proof(&trace, Register::Spec) {
        out.push(("why", why));
    }
    out
}

/// THE DROP invariant (CLAUDE.md): "proof traces and all user-facing output
/// contain no Lojban". Two term renderers used to leak a gismu/cmavo spelling
/// into the `[Why]` narrative and the rendered proof:
///
/// - `GroundTerm::Description` rendered as `le {s}` (nibli-reason `kb.rs`) —
///   now `the {s}`, matching `LogicalTerm::Description`'s `trace_display`.
/// - the equality-substitution note joined its pairs with `" du "`
///   (nibli-reason `reasoning.rs`) — now `" = "`, the KR surface operator.
///
/// Both flow through `humanize_fact`/`equality_facts` into reader-facing text,
/// so this asserts on the RENDERED strings, not on the internal identifiers
/// (`DU_VARIANT_BOUND` and friends are a sanctioned residual).
#[test]
fn rendered_proofs_carry_no_lojban_description_or_identity_spelling() {
    // Case 1: a description term in the goal — exercised the `le {s}` path.
    let desc = engine_with_facts(&["dog(the cat)."]);
    // Case 2: identity substitution — exercised the `" du "` note.
    let ident = engine_with_facts(&["Adam = Bob.", "dog(Adam)."]);

    let cases = [
        ("description", &desc, "dog(the cat).", "the cat"),
        ("identity", &ident, "dog(Bob).", "bob = adam"),
    ];

    for (case, engine, query, expected) in cases {
        assert_true(
            &engine.query_holds(query).unwrap(),
            &format!("{case}: query must hold for the proof to be populated"),
        );
        let mut saw_expected = false;
        for (surface, text) in rendered_proof_surfaces(engine, query) {
            assert!(
                !text.contains("le "),
                "{case}/{surface}: Lojban description article leaked: {text}"
            );
            assert!(
                !text.contains(" du "),
                "{case}/{surface}: Lojban identity spelling leaked: {text}"
            );
            saw_expected |= text.contains(expected);
        }
        // Positive control: the replacement spelling really is what renders, so
        // a renderer that silently stopped emitting the term cannot pass.
        assert!(
            saw_expected,
            "{case}: expected {expected:?} in some rendered surface"
        );
    }
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
    // rex eats (bare/unqualified) — must not satisfy a PAST antecedent.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past eats(it)).",
        "dog(Rex).",
        "eats(Rex).",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_false(&holds, "a bare premise must not satisfy a Past antecedent");
}

// ── Tensed NEGATED restrictor (tense × NAF). `where past ~eats(it)` compiles
// to a Past-flavored NegatedExistsGroup ("has not past-eaten"). The NAF check
// is flavor-exact, symmetric with the positive `where past eats(it)` above: a
// PAST witness blocks it, a bare/future witness does NOT. ──

#[test]
fn tensed_negated_restrictor_fires_without_witness() {
    // rex is a dog that has NOT past-eaten → `past ~eats` holds → rule fires.
    let engine = engine_with_facts(&["be_hungry(every dog where past ~eats(it)).", "dog(Rex)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_true(
        &holds,
        "a tensed NAF restrictor fires when no matching-flavor witness exists",
    );
}

#[test]
fn tensed_negated_restrictor_blocked_by_past_witness() {
    // rex DID past-eat → `past ~eats` is FALSE for rex → the rule must NOT fire.
    // (The soundness fix: pre-fix the Past witness was invisible to the tenseless
    // NAF and the rule over-fired.)
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past ~eats(it)).",
        "dog(Rex).",
        "past eats(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_false(
        &holds,
        "a Past witness blocks a `past ~P` NAF restrictor (flavor-exact)",
    );
}

#[test]
fn tensed_negated_restrictor_bare_witness_does_not_block() {
    // rex has a BARE eating but no PAST eating → `past ~eats` (checks PAST) still
    // holds → rule fires. (The flavor-exactness: a bare witness must not block a
    // Past NAF — the mirror of `tensed_restrictor_bare_premise_control`.)
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past ~eats(it)).",
        "dog(Rex).",
        "eats(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_true(
        &holds,
        "a bare witness must not block a Past NAF restrictor",
    );
}

#[test]
fn tensed_negated_restrictor_future_witness_does_not_block() {
    // rex WILL eat (future) but has no PAST eating → `past ~eats` holds → fires.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where past ~eats(it)).",
        "dog(Rex).",
        "future eats(Rex).",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("be_hungry(Rex).").unwrap();
    assert_true(
        &holds,
        "a Future witness must not block a Past NAF restrictor",
    );
}

#[test]
fn bare_negated_restrictor_rule_does_not_answer_tensed_goal() {
    // The head and both restrictors are bare. A Past query cannot activate the
    // rule, regardless of whether a same-flavor NAF witness exists.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where ~eats(it)).",
        "past dog(Rex).",
        "past eats(Rex).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("past be_hungry(Rex).")
        .unwrap();
    assert_false(&holds, "a bare NAF rule must not answer a Past query");
}

#[test]
fn bare_negated_restrictor_stays_bare_under_tensed_query() {
    // A bare witness would block this rule for a bare query. It does not matter
    // here because the bare rule head cannot unify with the Past goal.
    let engine = engine_with_facts(&[
        "be_hungry(every dog where ~eats(it)).",
        "past dog(Rex).",
        "eats(Rex).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("past be_hungry(Rex).")
        .unwrap();
    assert_false(&holds, "a tensed goal must not re-flavor a bare NAF rule");
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
// be soundly compiled to an unqualified backward-chaining rule, so it is rejected.

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
    // INSIDE the universal. Pre-fix it was silently stripped to a Bare rule.
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
    // The existential-import presupposition for `ro lo gerku cu pendo ro lo
    // mlatu` must assert a dog witness and a cat witness as DISTINCT entities — NOT
    // one phantom entity that is both. So "is some dog a cat?" is FALSE. RED before
    // the per-universal-witness fix (a single shared witness satisfied both).
    let engine = engine_with_import_facts(true, &["friend(every dog, every cat)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("cat(some dog).").unwrap();
    assert_false(&holds, "no single xorlo witness is both a dog and a cat");
}

#[test]
fn object_position_count_object_fails_closed() {
    // An exact-count object is still a CountNode inside the asserted rule and
    // therefore query-only; nesting cannot bypass the assertion boundary.
    let engine = fresh_engine();
    let err = engine
        .assert_text("friend(every dog, exactly 3 cat).")
        .expect_err("an exact-count object position must be rejected");
    assert!(
        err.to_string().contains("query-only") && err.to_string().contains("cannot be asserted"),
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
fn taxonomy_temporal_propagation_must_be_declared_per_rule() {
    for tense in ["past", "now", "future"] {
        let bare = engine_with_facts(&["animal(every dog).", &format!("{tense} dog(Rex).")]);
        assert_false(
            &bare.query_holds(&format!("{tense} animal(Rex).")).unwrap(),
            "a bare taxonomy rule must not inherit the query flavor",
        );

        let declared = engine_with_facts(&[
            &format!("all $x: {tense} dog($x) -> {tense} animal($x)."),
            &format!("{tense} dog(Rex)."),
        ]);
        assert_true(
            &declared
                .query_holds(&format!("{tense} animal(Rex)."))
                .unwrap(),
            "an explicitly same-flavor taxonomy rule must fire",
        );
    }

    let bare = engine_with_facts(&["animal(every dog).", "dog(Rex)."]);
    assert_true(
        &bare.query_holds("animal(Rex).").unwrap(),
        "removing temporal lifting must not change ordinary bare rule firing",
    );
}

#[test]
fn causal_temporal_mapping_must_be_declared_per_rule() {
    // Eating at a past episode does not license projecting a bare causal rule
    // into that same undifferentiated flavor.
    let implicit = engine_with_facts(&["all $x: eats($x) -> be_hungry($x).", "past eats(Rex)."]);
    assert_false(
        &implicit.query_holds("past be_hungry(Rex).").unwrap(),
        "a bare causal rule must not be projected into Past",
    );

    let declared = engine_with_facts(&[
        "all $x: past eats($x) -> now be_hungry($x).",
        "past eats(Rex).",
    ]);
    assert_true(
        &declared.query_holds("now be_hungry(Rex).").unwrap(),
        "the author-declared Past-to-Present causal mapping must fire",
    );
    assert_false(
        &declared.query_holds("past be_hungry(Rex).").unwrap(),
        "a cross-flavor rule must derive only its declared conclusion flavor",
    );
}

#[test]
fn stratification_conservatively_collapses_temporal_flavors() {
    let engine = fresh_engine();
    let error = engine
        .assert_text("all $x: person($x) & past ~dog($x) -> now dog($x).")
        .expect_err("cross-flavor negative recursion remains conservatively rejected");
    let message = error.to_string();
    assert!(
        message.contains("Unstratifiable") && message.contains("dog"),
        "the surface-relation negative cycle must be explicit: {message}"
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
fn validate_is_compile_only_while_assert_text_enforces_admission() {
    for statement in [
        "big(exactly 1 dog).",
        "product(10, 2, 5).",
        "exponential(8, 2, 3).",
    ] {
        let engine = fresh_engine();
        engine.validate(statement).unwrap_or_else(|error| {
            panic!("compile-only validate rejected `{statement}`: {error}")
        });
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "validate must not mutate the assertion registry for `{statement}`"
        );

        let error = engine
            .assert_text(statement)
            .expect_err("assertion admission must reject query-only IR");
        assert!(
            error.to_string().contains("query-only"),
            "expected query-only assertion rejection for `{statement}`, got: {error}"
        );
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "rejected assertion must remain atomic for `{statement}`"
        );
        assert_eq!(
            engine.assert_text("person(Adam).").unwrap(),
            vec![0],
            "validation and rejected admission must consume no assertion id"
        );
    }
}

#[test]
fn exact_count_assertions_are_query_only_in_every_import_profile() {
    for import_enabled in [false, true] {
        for statement in [
            "big(exactly 1 dog).",
            "big(no dog).",
            "exactly 2 dog $d: big($d).",
            "past big(exactly 1 dog).",
            "person(Adam) & big(exactly 1 dog).",
            "all $x: dog($x) -> big(exactly 1 dog).",
        ] {
            let engine = fresh_engine();
            engine.set_existential_import(import_enabled).unwrap();
            let error = engine
                .assert_text(statement)
                .expect_err("every asserted CountNode must fail closed");
            assert!(
                error.to_string().contains("query-only")
                    && error.to_string().contains("cannot be asserted"),
                "{statement} under import={import_enabled}: {error}"
            );
            assert!(
                engine.list_facts().unwrap().is_empty(),
                "rejection must be atomic for {statement}"
            );
            assert_false(
                &engine.query_holds("person(Adam).").unwrap(),
                "a sibling conjunct must not half-land",
            );
            assert_eq!(
                engine.assert_text("person(Adam).").unwrap(),
                vec![0],
                "a rejected count must not consume an assertion id"
            );
        }
    }
}

#[test]
fn exact_count_queries_observe_current_facts_and_provenance() {
    let engine = fresh_engine();
    assert_true(
        &engine.query_holds("big(no dog).").unwrap(),
        "zero is true in the initially empty current model",
    );

    let rejected = engine
        .assert_text("big(no dog).")
        .expect_err("zero is a query too, never a stored prohibition");
    assert!(rejected.to_string().contains("query-only"), "{rejected}");

    let adam = engine
        .assert_text("dog(Adam) & big(Adam).")
        .expect("ordinary matching facts remain assertable")[0];
    assert_true(
        &engine.query_holds("big(exactly 1 dog).").unwrap(),
        "one explicit matching entity makes the snapshot count one",
    );
    assert_false(&engine.query_holds("big(no dog).").unwrap(), "zero flips");

    let (one, _, proof_json) = engine.query_text_with_proof("big(exactly 1 dog).").unwrap();
    assert_true(&one, "proof query must agree");
    let proof = nibli_protocol::proof_trace_from_json(&proof_json).unwrap();
    assert!(proof.steps.iter().any(|step| matches!(
        &step.rule,
        nibli_protocol::ProofRule::CountResult {
            expected: 1,
            actual: 1,
            existential_imported: 0,
        }
    )));

    let adam_duplicate = engine
        .assert_text("dog(Adam) & big(Adam).")
        .expect("duplicate derivations do not create another entity")[0];
    assert_true(
        &engine.query_holds("big(exactly 1 dog).").unwrap(),
        "duplicate facts for one entity still count once",
    );

    let bel = engine
        .assert_text("dog(Bel) & big(Bel).")
        .expect("a second explicit entity is allowed; no hidden constraint exists")[0];
    assert_false(
        &engine.query_holds("big(exactly 1 dog).").unwrap(),
        "the current count changes from one to two",
    );
    assert_true(
        &engine.query_holds("big(exactly 2 dog).").unwrap(),
        "the new snapshot reports two",
    );

    engine.retract_fact(bel).unwrap();
    assert_true(
        &engine.query_holds("big(exactly 1 dog).").unwrap(),
        "retracting the second supporting assertion restores one",
    );
    engine.retract_fact(adam).unwrap();
    engine.retract_fact(adam_duplicate).unwrap();
    assert_true(
        &engine.query_holds("big(no dog).").unwrap(),
        "retraction restores zero",
    );
}

#[test]
fn explicit_import_counts_imported_witness() {
    // The explicit legacy profile has one coherent logical domain: two asserted
    // dogs plus the description-import witness count as three everywhere.
    let engine =
        engine_with_import_facts(true, &["dog(Adam).", "dog(Karl).", "animal(every dog)."]);
    assert_true(
        &engine.query_holds("animal(exactly 3 dog).").unwrap(),
        "two asserted dogs plus one imported dog count as three",
    );
    assert_false(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "the imported logical witness cannot disappear from exact count",
    );
}

#[test]
fn existential_import_profiles_are_algebraically_coherent_and_retractable() {
    for enabled in [false, true] {
        let engine = fresh_engine();
        engine.set_existential_import(enabled).unwrap();
        let description_id = engine.assert_text("animal(every dog).").unwrap()[0];

        let some = engine.query_holds("dog(some dog).").unwrap();
        let all_dogs_are_cats = engine.query_holds("cat(every dog).").unwrap();
        let found = engine.query_find_text("dog($d).").unwrap();
        let counted = engine.count_witnesses_text("dog($d).").unwrap();
        let exactly_zero = engine.query_holds("dog(no dog).").unwrap();
        let (exactly_one, _, one_proof_json) =
            engine.query_text_with_proof("dog(exactly 1 dog).").unwrap();
        let one_proof = nibli_protocol::proof_trace_from_json(&one_proof_json).unwrap();

        assert_eq!(some.is_true(), enabled, "some/profile mismatch");
        assert_eq!(
            all_dogs_are_cats.is_true(),
            !enabled,
            "forall/profile mismatch: clean-core is vacuous, import supplies a non-cat dog"
        );
        assert_eq!(found.len(), usize::from(enabled), "find/profile mismatch");
        assert_eq!(counted, usize::from(enabled), "count/profile mismatch");
        assert_eq!(exactly_zero.is_true(), !enabled, "exactly-0 mismatch");
        assert_eq!(exactly_one.is_true(), enabled, "exactly-1 mismatch");

        if enabled {
            assert!(
                found
                    .iter()
                    .flatten()
                    .any(|binding| { binding.origin == EngineWitnessOrigin::ExistentialImport })
            );
            assert!(one_proof.steps.iter().any(|step| {
                matches!(
                    &step.rule,
                    nibli_protocol::ProofRule::CountResult {
                        actual: 1,
                        existential_imported: 1,
                        ..
                    }
                )
            }));
            let (_, _, some_proof_json) = engine.query_text_with_proof("dog(some dog).").unwrap();
            let some_proof = nibli_protocol::proof_trace_from_json(&some_proof_json).unwrap();
            assert!(some_proof.steps.iter().any(|step| {
                matches!(
                    &step.rule,
                    nibli_protocol::ProofRule::ExistsWitness {
                        origin: EngineWitnessOrigin::ExistentialImport,
                        ..
                    }
                )
            }));
        }

        engine.retract_fact(description_id).unwrap();
        assert_false(
            &engine.query_holds("dog(some dog).").unwrap(),
            "post-retract some",
        );
        assert_eq!(engine.query_find_text("dog($d).").unwrap().len(), 0);
        assert_eq!(engine.count_witnesses_text("dog($d).").unwrap(), 0);
        assert_true(
            &engine.query_holds("dog(no dog).").unwrap(),
            "post-retract zero",
        );
        assert_false(
            &engine.query_holds("dog(exactly 1 dog).").unwrap(),
            "post-retract one",
        );
    }
}

#[test]
fn existential_import_profile_applies_to_aggregate_enumeration() {
    for (enabled, expected) in [
        (false, EngineAggregateOutcome::Empty),
        (
            true,
            EngineAggregateOutcome::Value {
                value: 5.0,
                witnesses: 1,
            },
        ),
    ] {
        let engine = fresh_engine();
        engine.set_existential_import(enabled).unwrap();
        engine.assert_text("quantity(every dog, 5).").unwrap();

        assert_eq!(
            engine
                .aggregate_text(
                    "quantity($dog, $amount).",
                    "$amount",
                    EngineAggregateOp::Sum,
                )
                .unwrap(),
            expected,
            "aggregate/profile mismatch with existential import {enabled}"
        );
    }
}

#[test]
fn existential_import_profile_switch_rebuilds_loaded_rules_immediately() {
    let engine = engine_with_facts(&["animal(every dog).", "cat(Milo)."]);
    assert!(!engine.is_existential_import());
    assert_false(
        &engine.query_holds("dog(some dog).").unwrap(),
        "default clean-core",
    );

    engine.set_existential_import(true).unwrap();
    assert!(engine.is_existential_import());
    assert_true(
        &engine.query_holds("dog(some dog).").unwrap(),
        "OFF to ON rebuild",
    );
    assert_eq!(engine.count_witnesses_text("dog($d).").unwrap(), 1);

    engine.set_existential_import(false).unwrap();
    assert_false(
        &engine.query_holds("dog(some dog).").unwrap(),
        "ON to OFF rebuild",
    );
    assert_eq!(engine.count_witnesses_text("dog($d).").unwrap(), 0);

    let cat_id = engine
        .list_facts()
        .unwrap()
        .into_iter()
        .find(|fact| fact.label == "cat(Milo).")
        .expect("unrelated fact")
        .id;
    engine.retract_fact(cat_id).unwrap();
    assert_false(
        &engine.query_holds("dog(some dog).").unwrap(),
        "unrelated retraction must preserve the active profile",
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
fn count_inside_opaque_abstraction_is_content_not_an_assertion() {
    let engine = engine_with_facts(&["believe(me, fact { big(exactly 1 dog) })."]);
    assert_true(
        &engine
            .query_holds("believe(me, fact { big(exactly 1 dog) }).")
            .unwrap(),
        "the opaque proposition itself remains assertable and queryable",
    );
    assert_false(
        &engine.query_holds("dog($da).").unwrap(),
        "quoted exact-count content must not mint a dog in the outer KB",
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
    let witnesses = engine.query_find_text("cat($c).").unwrap();
    assert!(witnesses.iter().flatten().any(|binding| {
        binding.variable == "$c" && binding.origin == EngineWitnessOrigin::GeneratedWitness
    }));
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
fn numeric_terms_are_universal_domain_members() {
    // A number asserted into a predicate IS a quantifier-domain member
    // (GUARANTEES §Disclosed Sharp Edges, the numbers-join-the-domain change):
    // the universal below is TRUE by CHECKING 5, not vacuously, and an
    // arithmetically false body finds 5 as its counterexample. Pre-change both
    // answered TRUE — the disclosed vacuous-universal sharp edge this replaces.
    let engine = engine_with_facts(&["big(5)."]);
    assert_true(
        &engine.query_holds("sum(every big, 2, 3).").unwrap(),
        "5 = 2 + 3 holds of the one member",
    );
    assert_false(
        &engine.query_holds("sum(every big, 2, 2).").unwrap(),
        "5 ≠ 2 + 2 — the number is enumerated and fails the body",
    );
}

#[test]
fn exact_count_ranges_over_asserted_numbers() {
    // The TODO §Reasoning/evaluation repro verbatim: with `big(5). dog(5).`
    // entailed, `dog(no big).` used to answer TRUE (the count enumerated a
    // number-free domain) while `dog(some big).` answered TRUE via the index —
    // jointly inconsistent verdicts. The count now ranges over the numbers.
    let engine = engine_with_facts(&["big(5).", "dog(5).", "dog(Rex)."]);
    assert_false(
        &engine.query_holds("dog(no big).").unwrap(),
        "5 is big and a dog — 'no big thing is a dog' must be FALSE",
    );
    assert_true(
        &engine.query_holds("dog(exactly 1 big).").unwrap(),
        "exactly one big thing (5) is a dog",
    );
    assert_true(
        &engine.query_holds("dog(some big).").unwrap(),
        "the existential agrees with the count",
    );
}

#[test]
fn imported_and_numeric_witnesses_share_one_counting_algebra() {
    // Explicit import adds one logical big witness alongside the asserted 5.
    let engine = engine_with_import_facts(true, &["big(5).", "animal(every big)."]);
    assert_true(
        &engine.query_holds("animal(exactly 2 big).").unwrap(),
        "the asserted number and imported witness both count",
    );
    assert_true(
        &engine.query_holds("dog(exactly 0 big).").unwrap(),
        "5 is not a dog — the member is enumerated and fails the body",
    );
}

#[test]
fn compute_role_predicates_do_not_anchor_existential_narrowing() {
    // `sum_x1` (role predicate of a compute relation) has no complete store
    // extension because its truth is evaluated at query time, so admitting it as a
    // MANDATORY anchor let its empty candidate set win the min-cardinality
    // narrowing pick: `sum(some big, 2, 3).` answered a definitive FALSE while
    // both `big(5).` and `sum(5, 2, 3).` are TRUE (TODO §Reasoning/evaluation,
    // wrong-verdict face 2). The witness must come from the `big_x1` index.
    let engine = engine_with_facts(&["big(5)."]);
    assert_true(
        &engine.query_holds("sum(some big, 2, 3).").unwrap(),
        "the existential must reach the number 5 via the big_x1 index",
    );
    assert_false(
        &engine.query_holds("sum(some big, 2, 2).").unwrap(),
        "an arithmetically false body still fails — the fix widens candidates, not truth",
    );
}

#[test]
fn naf_over_a_numeric_existential_inverts_the_corrected_verdict() {
    // `~` purely negates the inner verdict, so the anchor bug's wrong FALSE
    // surfaced as a wrong definitive TRUE — strictly worse, since a definitive
    // TRUE reads as a positive finding. Pin both directions post-fix.
    let engine = engine_with_facts(&["big(5)."]);
    assert_false(
        &engine.query_holds("~sum(some big, 2, 3).").unwrap(),
        "NAF over the now-TRUE existential must be FALSE",
    );
    assert_true(
        &engine.query_holds("~sum(some big, 2, 2).").unwrap(),
        "NAF over the arithmetically false body stays TRUE",
    );
}

#[test]
fn entity_existentials_are_untouched_by_the_anchor_fix() {
    // Controls: ordinary store-backed narrowing is unchanged. A public
    // non-numeric witness is a valid external-compute argument, so without a
    // backend the compute body is unresolved rather than closed-world FALSE.
    let engine = engine_with_facts(&["big(5).", "dog(Rex)."]);
    assert_true(
        &engine.query_holds("dog(some dog).").unwrap(),
        "entity narrowing control",
    );
    assert_false(
        &engine.query_holds("dog(some big).").unwrap(),
        "nothing big is a dog — the 5 candidate fails the dog body",
    );
    assert_eq!(
        engine.query_holds("sum(some dog, 2, 3).").unwrap(),
        EngineQueryResult::Unknown(EngineUnknownReason::BackendUnavailable),
        "a non-numeric public witness requires the unavailable external backend",
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
    let engine = engine_with_facts(&["dog(Adam).", "dog(Karl).", "animal(Adam).", "animal(Karl)."]);
    engine
        .assert_text("dog(Adam).")
        .expect("a duplicate name/fact must not change entity cardinality");
    assert_true(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "two distinct entities count as two before identity collapse",
    );
    let equality_id = engine.assert_text("Adam = Karl.").unwrap()[0];
    assert_true(
        &engine.query_holds("animal(exactly 1 dog).").unwrap(),
        "collapsed: the merged entity counts as ONE",
    );
    assert_false(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "collapsed: two names for one entity do NOT count as two",
    );
    engine.retract_fact(equality_id).unwrap();
    assert_true(
        &engine.query_holds("animal(exactly 2 dog).").unwrap(),
        "retracting the identity link restores two equivalence classes",
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
fn named_query_variable_corefers_across_conjuncts() {
    let shared = "bite($x, Bel) & bite($x, Dana).";
    let shared_with_gap = "bite($x, Bel) & bite(Ann, Bel) & bite($x, Dana).";
    let distinct = "bite($p, Bel) & bite($q, Dana).";

    let split = engine_with_facts(&["bite(Ann, Bel).", "bite(Cy, Dana)."]);
    assert_false(
        &split.query_holds(shared).unwrap(),
        "one shared `$x` cannot be satisfied by two different biters",
    );
    assert_false(
        &split.query_holds(shared_with_gap).unwrap(),
        "an intervening ordinary clause must not split the shared `$x` scope",
    );
    assert_false(
        &split.query_text_with_proof(shared).unwrap().0,
        "the proof-producing query path must use the same shared binder",
    );
    assert!(
        split.query_find_text(shared).unwrap().is_empty(),
        "find must not manufacture a joint `$x` witness from split facts"
    );
    assert_eq!(
        split.count_witnesses_text(shared).unwrap(),
        0,
        "count must share the same statement-wide query binding"
    );
    assert_true(
        &split.query_holds(distinct).unwrap(),
        "different names remain independent and may use different witnesses",
    );

    let joint = engine_with_facts(&["bite(Ann, Bel).", "bite(Ann, Dana)."]);
    assert_true(
        &joint.query_holds(shared).unwrap(),
        "one entity satisfying both conjuncts is a valid shared witness",
    );
    assert_true(
        &joint.query_holds(shared_with_gap).unwrap(),
        "a joint witness remains valid across an intervening ordinary clause",
    );
    let witnesses = joint.query_find_text(shared).unwrap();
    assert_eq!(
        witnesses.len(),
        1,
        "exactly one joint witness: {witnesses:?}"
    );
    assert!(
        witnesses[0].iter().any(|binding| {
            binding.variable == "$x"
                && matches!(&binding.term, EngineLogicalTerm::Constant(name) if name == "ann")
        }),
        "the shared `$x` binding must be Ann: {witnesses:?}"
    );

    let numeric = engine_with_facts(&[
        "quantity(Varfarin, 5).",
        "quantity(Fenitoin, 7).",
        "year(Term, 5).",
    ]);
    assert_eq!(
        numeric
            .aggregate_text(
                "quantity($drug, $dose) & year(Term, $dose).",
                "$dose",
                EngineAggregateOp::Sum,
            )
            .unwrap(),
        EngineAggregateOutcome::Value {
            value: 5.0,
            witnesses: 1
        },
        "aggregate must use only numeric witnesses shared across both clauses"
    );
}

#[test]
fn named_assertion_variable_corefers_across_conjuncts_and_rules() {
    let joint_rule = "all $w: bite($w, Bel) & bite($w, Dana) -> animal($w).";

    let shared = engine_with_facts(&["bite($x, Bel) & bite($x, Dana).", joint_rule]);
    assert_true(
        &shared
            .query_holds("bite($w, Bel) & bite($w, Dana).")
            .unwrap(),
        "one shared assertion name must store one joint witness",
    );
    assert_true(
        &shared.query_holds("animal($who).").unwrap(),
        "a downstream rule requiring the joint witness must fire",
    );

    let distinct = engine_with_facts(&["bite($p, Bel) & bite($q, Dana).", joint_rule]);
    assert_false(
        &distinct
            .query_holds("bite($w, Bel) & bite($w, Dana).")
            .unwrap(),
        "different assertion names must mint independent witnesses",
    );
    assert_false(
        &distinct.query_holds("animal($who).").unwrap(),
        "the joint-witness rule must not combine independent assertion names",
    );
    assert_true(
        &distinct
            .query_holds("bite($p, Bel) & bite($q, Dana).")
            .unwrap(),
        "the two independently stored witnesses remain queryable",
    );

    let separate = fresh_engine();
    assert_eq!(
        separate
            .assert_text("bite($x, Bel). bite($x, Dana).")
            .unwrap()
            .len(),
        2,
        "period-terminated statements are separate fact and binder scopes"
    );
    assert_false(
        &separate
            .query_holds("bite($w, Bel) & bite($w, Dana).")
            .unwrap(),
        "the same spelling in separate statements must not co-refer",
    );
    assert_true(
        &separate
            .query_holds("bite($p, Bel) & bite($q, Dana).")
            .unwrap(),
        "separate statements retain their independent witnesses",
    );
}

#[test]
fn assertion_coreference_is_shared_inside_one_explicit_universal_scope() {
    let shared = engine_with_facts(&[
        "dog(Bel).",
        "all $owner: dog($owner) -> bite($w, $owner) & loves($w, $owner).",
    ]);
    assert_true(
        &shared
            .query_holds("bite($w, Bel) & loves($w, Bel).")
            .unwrap(),
        "both universal conclusions must expose the same dependent witness",
    );

    let distinct = engine_with_facts(&[
        "dog(Bel).",
        "all $owner: dog($owner) -> bite($p, $owner) & loves($q, $owner).",
    ]);
    assert_false(
        &distinct
            .query_holds("bite($w, Bel) & loves($w, Bel).")
            .unwrap(),
        "different conclusion names must remain different dependent witnesses",
    );
}

#[test]
fn assertion_coreference_rejects_universal_scope_crossings_atomically() {
    for text in [
        "bite(every person, $x) & bite($x, Dana).",
        "bite($x, Dana) & bite(every person, $x).",
    ] {
        let engine = fresh_engine();
        let err = engine
            .assert_text(text)
            .expect_err("a ground/dependent witness choice must not depend on operand order");
        assert!(
            matches!(err, EngineError::Semantic(_)),
            "scope rejection must retain its Semantic error class: {err}"
        );
        assert!(
            err.to_string().contains("de-re/de-dicto"),
            "scope rejection must explain the ambiguity: {err}"
        );
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "a rejected compound assertion must ingest no partial fact"
        );
        assert_eq!(
            engine.assert_text("dog(Adam).").unwrap(),
            vec![0],
            "compile-time rejection must not consume a fact id"
        );
    }
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

    engine.reset().unwrap();

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

// ── Reversed material conditional (`A | ~B` — negation on the RIGHT operand) ──
// `goes(Adam) | ~eats(Adam).` compiles to Or(Q, Not P) ≡ eats→goes. The reversed
// arm now routes through the same rule compiler as the forward `~B | A` spelling
// (adversarial-review finding 2026-07-10: it used to register an INERT rule whose
// condition templates froze the assertion's own event Skolems).

#[test]
fn reversed_disjunction_reasons_modus_ponens() {
    // eats(Adam) + (eats→goes) ⊢ goes(Adam) — the Q→P + Q ⊢ P case.
    let engine = engine_with_facts(&["goes(Adam) | ~eats(Adam).", "eats(Adam)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("goes(Adam).").unwrap();
    assert_true(
        &holds,
        "A | ~B: goes should derive from eats (modus ponens through the reversed arm)",
    );

    // Negative control: without the premise, the consequent is not derivable.
    let only_rule = engine_with_facts(&["goes(Adam) | ~eats(Adam)."]);
    let (holds, _t, _j) = only_rule.query_text_with_proof("goes(Adam).").unwrap();
    assert_false(&holds, "A | ~B: goes must NOT hold without eats");

    // Wrong-entity control: the real constant stays constant in the template —
    // only the EVENT variable generalizes. A different entity's eating must not fire.
    let wrong = engine_with_facts(&["goes(Adam) | ~eats(Adam).", "eats(Bel)."]);
    let (holds, _t, _j) = wrong.query_text_with_proof("goes(Adam).").unwrap();
    assert_false(&holds, "A | ~B: eats(Bel) must not derive goes(Adam)");
}

#[test]
fn reversed_disjunction_assertion_order_invariant() {
    // Backward chaining fires at query time, so premise-first works too.
    let engine = engine_with_facts(&["eats(Adam).", "goes(Adam) | ~eats(Adam)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("goes(Adam).").unwrap();
    assert_true(
        &holds,
        "A | ~B: premise asserted BEFORE the disjunction must still derive",
    );
}

#[test]
fn trailing_negation_multi_disjunct_registers_constraint() {
    // `A | B | ~C.` left-folds to Or(Or(A,B), Not C) — the reversed arm with a
    // DISJUNCTIVE consequent. It used to fail ("no extractable conclusions");
    // now it swaps into the same DisjunctiveConstraint path as the grouped
    // forward spelling: C → A∨B, an integrity constraint (deriving a disjunct
    // would be unsound), violated when C holds and both disjuncts are denied.
    let engine = engine_with_facts(&[
        "goes(Adam) | walks(Adam) | ~eats(Adam).",
        "eats(Adam).",
        "~goes(Adam).",
        "~walks(Adam).",
    ]);
    let v = engine.check_contradictions();
    assert!(
        v.iter()
            .any(|m| m.contains("Disjunctive constraint violated")),
        "eats holds and both positive disjuncts denied → constraint violation: {v:?}"
    );
}

// ── Mutation-audit kill-tests (2026-07-18 re-cut): each pins a behavior a
// surviving mutant showed to be untested. ──

#[test]
fn tensed_find_enumerates_witnesses_per_flavor() {
    // find_witnesses' Past/Present/Future arms: a tensed find query must
    // enumerate the flavor's witnesses (deleting an arm degrades to a
    // verdict-only walk with an EMPTY binding set — wrong [Find]/count output).
    let engine = engine_with_facts(&["past dog(Dan).", "now dog(Adam).", "future dog(Bel)."]);
    for (q, who) in [
        ("past dog($da).", "dan"),
        ("now dog($da).", "adam"),
        ("future dog($da).", "bel"),
    ] {
        let tuples = engine.query_find_text(q).unwrap();
        assert_eq!(tuples.len(), 1, "{q}: exactly one witness expected");
        let bound = format!("{:?}", tuples[0]).to_lowercase();
        assert!(
            bound.contains(who),
            "{q}: binding must name {who}, got {bound}"
        );
    }
}

#[test]
fn now_and_future_naf_restrictors_blocked_by_matching_witness() {
    // collect_group_event_candidates' Present/Future condition arms: the
    // candidate NARROWING must stay flavor-consistent with the witness check —
    // deleting a flavor arm anchors the group tenseless, misses the flavored
    // witness, and fires the rule on a spurious "no witness" (a WRONG TRUE).
    // The Past twin is pinned by tensed_negated_restrictor_blocked_by_past_witness.
    for flavor in ["now", "future"] {
        let engine = engine_with_facts(&[
            &format!("beautiful(every person where {flavor} ~dog(it))."),
            "person(Adam).",
            &format!("{flavor} dog(Adam)."),
        ]);
        let (holds, _t, _j) = engine.query_text_with_proof("beautiful(Adam).").unwrap();
        assert_false(
            &holds,
            &format!("a `{flavor}` witness must block the `{flavor} ~dog` restrictor"),
        );

        // Fires-side control: a different person with no witness derives.
        let fires = engine_with_facts(&[
            &format!("beautiful(every person where {flavor} ~dog(it))."),
            "person(Bel).",
        ]);
        let (holds, _t, _j) = fires.query_text_with_proof("beautiful(Bel).").unwrap();
        assert_true(&holds, "no witness → the tensed NAF restrictor fires");
    }
}

#[test]
fn deontic_negated_fact_asserts_ok() {
    // find_negation_body's deontic arm: `must ~P.` is legal KR (deontic outside,
    // `~` innermost) — deleting the arm flips the assertion to a zero-ingest
    // rejection. Pin that it asserts cleanly.
    let engine = fresh_engine();
    let ids = engine
        .assert_text("must ~eats(Adam).")
        .expect("`must ~eats(Adam).` is a legal, representable assertion");
    assert!(!ids.is_empty(), "the deontic negation must ingest a record");
}

#[test]
fn negated_tail_xor_forward_half_reasons() {
    // `goes(me) ^ ~eats(me).` flattens to And(Or(K, Not C), Not(And(K, Not C))):
    // the inner Or hits the reversed arm, so its K↔C forward half (eats→goes) now
    // FIRES — sound (Xor(K,¬C) ≡ K↔C entails C→K). Previously the half was inert.
    let engine = engine_with_facts(&["goes(me) ^ ~eats(me).", "eats(me)."]);
    let (holds, _t, _j) = engine.query_text_with_proof("goes(me).").unwrap();
    assert_true(
        &holds,
        "negated-tail xor: eats should derive goes (the K↔C forward half)",
    );
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

#[test]
fn second_witness_family_survives_skolem_registry_dedup() {
    // Kills rules.rs `replace == with != in compile_forall_to_rule` (the
    // skolem_fn_registry dedup `any(|e| e.base_name == *base)`). Under the
    // mutant, once the FIRST rule occupies the registry every LATER distinct
    // witness base is skipped, so a base with dep_count 2 falls back to the
    // `unwrap_or(1)` default and its candidates are built with the wrong
    // dependency shape (`sk(a)` instead of `sk((a, b))`) — the second
    // family's entailment and find silently die.
    let engine = engine_with_facts(&[
        "loves(every dog, some cat).",
        "gives(every person, recipient: every dog, gift: some book).",
        "dog(Rex).",
        "person(Adam).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("loves(Rex, some cat).")
        .unwrap();
    assert_true(&holds, "first family: the dog's loved-cat witness derives");
    let (holds, _t, _j) = engine
        .query_text_with_proof("gives(Adam, some book, Rex).")
        .unwrap();
    assert_true(
        &holds,
        "second family: the (person, dog)-dependent book witness derives",
    );
    let tuples = engine.query_find_text("gives(Adam, $b, Rex).").unwrap();
    assert_eq!(
        tuples.len(),
        1,
        "find must enumerate the dep-2 book witness: {tuples:?}"
    );
    let tuples = engine.query_find_text("loves(Rex, $c).").unwrap();
    assert_eq!(
        tuples.len(),
        1,
        "find must enumerate the dep-1 cat witness: {tuples:?}"
    );
}

#[test]
fn existentially_scoped_ground_conditional_registers_and_chains() {
    // Kills kb.rs `replace match guard subs.contains_key(v.as_str()) with false
    // in register_ground_material_conditional`: the root ∃ of a prenex-some
    // conditional must be peeled (its variable IS in the Skolem subs) so the
    // inner Or(Not P, Q) registers as a backward-chaining rule. Under the
    // mutant the assertion still ingests the positive person leaf (no error),
    // but the conditional silently vanishes and the entailment below is lost.
    let engine = engine_with_facts(&[
        "some person $p: goes($p) -> eats($p).",
        "goes(every person).",
        "person(Kim).",
    ]);
    let (holds, _t, _j) = engine
        .query_text_with_proof("some person $p: eats($p).")
        .unwrap();
    assert_true(
        &holds,
        "the ∃-witness person goes (universal) hence eats (the ∃-scoped conditional)",
    );
}

#[test]
fn impure_negation_body_stays_fail_closed() {
    // Kills kb.rs `replace && with || in negation_body_purely_representable`
    // (both sites). A negation body carrying a disjunction cannot be
    // represented by the negative-fact registry (`collect_ground_facts` drops
    // Or leaves — recording would STRENGTHEN ¬(dog ∧ (walks ∨ goes)) to
    // ¬(dog ∧ …)), so the assertion must stay a loud zero-ingest rejection.
    // Under either || mutant the pure siblings (And site) or the skolemized ∃
    // guard (Exists site) short-circuit the walk to `true` and the assert
    // wrongly succeeds.
    let engine = fresh_engine();
    let err = engine
        .assert_text("~eats(some dog where walks(it) | goes(it)).")
        .expect_err("a disjunctive negation body must be rejected fail-closed");
    assert!(
        err.to_string().contains("no representable content"),
        "expected the zero-ingest rejection, got: {err}"
    );
    // Control: the pure-conjunction body is representable and asserts fine.
    assert!(
        engine
            .assert_text("~eats(some dog where walks(it) & goes(it)).")
            .is_ok(),
        "a pure-conjunction negation body must stay assertable"
    );
    // Second observable for the And site: the Xor lowering's Not(And(K, ¬C))
    // half is impure too — recording its strengthened body would fabricate a
    // ¬goes group and flag a contradiction on this CONSISTENT KB.
    let xor = engine_with_facts(&["goes(me) ^ ~eats(me).", "goes(me)."]);
    assert!(
        xor.check_contradictions().is_empty(),
        "no negative group may be recorded from the impure Xor half: {:?}",
        xor.check_contradictions()
    );
}

#[test]
fn find_expands_du_aliases_from_the_index() {
    // Kills kb.rs `delete ! in extract_from_index` (the
    // `!equivalence_parent.is_empty()` guard; the `!tense_matches` twin dies
    // too). The dog index holds the raw alias `kim`; the du link Kim = Adam
    // must expand the candidate set with the canonical name, and the
    // deterministic dedup then keeps the canonical-name tuple. Without the
    // expansion the surviving binding displays `kim` (equivalence mutant) or
    // the index yields nothing at all (tense mutant).
    let engine = engine_with_facts(&["dog(Kim).", "dog(Bel).", "Kim = Adam."]);
    let tuples = engine.query_find_text("dog($da).").unwrap();
    assert_eq!(tuples.len(), 2, "two distinct dogs expected: {tuples:?}");
    let bound = format!("{tuples:?}").to_lowercase();
    assert!(
        bound.contains("adam") && bound.contains("bel"),
        "du-expanded canonical witness (adam) + the plain dog (bel) expected, got {bound}"
    );
}

#[test]
fn negated_conjunct_inside_existential_records_for_contradictions() {
    // Kills kb.rs `replace match guard subs.contains_key(v.as_str()) with false
    // in record_negative_conjuncts`: the ∃-root must be peeled so the negated
    // conjunct INSIDE the existential's And-spine reaches the negative-fact
    // registry. Under the mutant the walk falls to the single-negation arm,
    // which sees a non-negation And and records nothing — the later contrary
    // positive then sails through check_contradictions.
    let engine = engine_with_facts(&["some person $p: goes($p) & ~dog(Kim).", "dog(Kim)."]);
    let v = engine.check_contradictions();
    assert!(
        v.iter()
            .any(|m| m.contains("Negation contradiction") && m.contains("dog")),
        "the ∃-scoped ~dog(Kim) must be recorded and contradicted by dog(Kim): {v:?}"
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

    engine.reset().unwrap();
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
fn persistent_duplicate_assertion_citations_survive_reopen_and_retraction() {
    fn assertion_sources(engine: &NibliEngine) -> Vec<(u64, String)> {
        let (result, trace) = engine
            .query_text_raw_proof("Adam = Bob.")
            .expect("the persisted identity should remain queryable");
        assert_true(&result, "the persisted identity should hold");
        match &trace.steps[trace.root as usize].rule {
            nibli_protocol::ProofRule::Asserted { sources, .. } => sources
                .iter()
                .map(|source| (source.id, source.label.clone()))
                .collect(),
            other => panic!("an exact direct identity must be Asserted, got {other:?}"),
        }
    }

    let path = temp_db_path("duplicate_origin_replay");
    cleanup(&path);

    let (first, second, expected) = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let first = engine.assert_text("Adam = Bob.").unwrap()[0];
        let second = engine.assert_text("Adam = Bob.").unwrap()[0];
        let expected = vec![
            (first, "Adam = Bob.".to_string()),
            (second, "Adam = Bob.".to_string()),
        ];
        assert_eq!(assertion_sources(&engine), expected);
        (first, second, expected)
    };

    {
        let reopened = fresh_open(&path, "Duplicate assertion sources should replay");
        assert_eq!(
            assertion_sources(&reopened),
            expected,
            "reopen must preserve both durable source ids and labels"
        );
        reopened
            .retract_fact(first)
            .expect("one duplicate source should retract independently");
        assert_eq!(
            assertion_sources(&reopened),
            vec![(second, "Adam = Bob.".to_string())],
            "retracting one source must not erase or relabel its duplicate"
        );
    }

    {
        let reopened = fresh_open(&path, "Duplicate-source retraction should persist");
        assert_eq!(
            assertion_sources(&reopened),
            vec![(second, "Adam = Bob.".to_string())],
            "the retracted citation must not resurrect on a second replay"
        );
    }

    cleanup(&path);
}

#[test]
fn persistent_engine_never_journals_proof_local_compute_results() {
    let path = temp_db_path("proof_local_compute_not_persisted");
    cleanup(&path);

    {
        let engine = fresh_open(&path, "persistent engine should open");
        assert_true(
            &engine.query_holds("product(6, 2, 3).").unwrap(),
            "built-in compute must answer before reopen",
        );
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "a compute query must not create a live registry row"
        );
    }
    {
        let store = NibliStore::open(&path, "local".into()).expect("store should reopen");
        assert!(
            store.all_active_facts().unwrap().is_empty(),
            "a compute query must not create a durable journal row"
        );
    }
    {
        let reopened = fresh_open(&path, "empty compute-only store should reopen");
        assert!(reopened.list_facts().unwrap().is_empty());
        assert_true(
            &reopened.query_holds("product(6, 2, 3).").unwrap(),
            "the reopened engine recomputes rather than replays a premise",
        );
    }

    cleanup(&path);
}

#[test]
fn persistent_direct_and_text_assertions_share_source_ids_and_replay() {
    let path = temp_db_path("persistent_direct_shared_ids");
    cleanup(&path);

    let (direct_id, text_id) = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let direct_id = engine
            .assert_fact_direct(
                "dog".to_string(),
                vec![EngineLogicalTerm::Constant("adam".to_string())],
            )
            .expect("direct assertion should use the persistent path");
        let text_id = engine
            .assert_text("cat(Elis).")
            .expect("text assertion should share the allocator")[0];

        assert_eq!(direct_id, 0);
        assert_eq!(text_id, 1);
        assert_true(
            &engine.query_holds("dog(Adam).").unwrap(),
            "direct assertion should hold before reopen",
        );
        assert_true(
            &engine.query_holds("cat(Elis).").unwrap(),
            "text assertion should hold before reopen",
        );
        (direct_id, text_id)
    };

    {
        let reopened = fresh_open(&path, "both assertion forms should replay");
        assert_true(
            &reopened.query_holds("dog(Adam).").unwrap(),
            "direct assertion must be durable",
        );
        assert_true(
            &reopened.query_holds("cat(Elis).").unwrap(),
            "text assertion must remain durable",
        );
        reopened
            .retract_fact(direct_id)
            .expect("the direct assertion should retract by its durable id");
    }

    {
        let reopened = fresh_open(&path, "direct retraction should survive reopen");
        assert_false(
            &reopened.query_holds("dog(Adam).").unwrap(),
            "retracted direct assertion must not resurrect",
        );
        assert_true(
            &reopened.query_holds("cat(Elis).").unwrap(),
            "the independently sourced text fact must remain",
        );
        assert_eq!(
            reopened
                .list_facts()
                .unwrap()
                .into_iter()
                .map(|fact| fact.id)
                .collect::<Vec<_>>(),
            vec![text_id]
        );
    }

    cleanup(&path);
}

#[test]
fn rejected_persistent_assertion_never_commits_or_consumes_an_id() {
    let path = temp_db_path("persistent_assertion_rollback");
    cleanup(&path);

    {
        let engine = fresh_open(&path, "Persistent engine should open");
        assert_eq!(
            engine
                .assert_text("derived_only(\"permits\").")
                .expect("closure declaration should persist"),
            vec![0]
        );

        let error = engine
            .assert_fact_direct(
                "permits".to_string(),
                vec![
                    EngineLogicalTerm::Constant("review".to_string()),
                    EngineLogicalTerm::Constant("sock".to_string()),
                ],
            )
            .expect_err("direct assertion of a derived-only relation must fail");
        assert!(error.to_string().contains("derived-only"), "{error}");

        // Candidate allocation is discarded together with its rejected fact.
        // Neither a durable record nor a live source was ever published.
        assert_eq!(
            engine
                .assert_text("person(Adam).")
                .expect("a later assertion should remain usable"),
            vec![1]
        );
    }

    {
        let store = NibliStore::open(&path, "local".into()).expect("store should reopen");
        assert!(
            store.get_fact(2).unwrap().is_none(),
            "a rejected assertion must leave no extra durable row"
        );
    }

    {
        let reopened = fresh_open(&path, "rollback should leave a replayable registry");
        assert_false(
            &reopened.query_holds("permits(Review, Sock).").unwrap(),
            "a failed assertion must not resurrect from persistence",
        );
        assert_true(
            &reopened.query_holds("person(Adam).").unwrap(),
            "later successful state must replay",
        );
    }

    cleanup(&path);
}

#[test]
fn rejected_persistent_count_leaves_no_row_and_quoted_count_reopens() {
    let path = temp_db_path("persistent_count_query_only");
    cleanup(&path);

    {
        let engine = fresh_open(&path, "persistent engine should open");
        let error = engine
            .assert_text("person(Adam). big(exactly 1 dog).")
            .expect_err("a later count root must reject the whole persistent call");
        assert!(error.to_string().contains("query-only"), "{error}");
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "the ordinary first root must not land before the later rejection"
        );
    }
    {
        let store = NibliStore::open(&path, "local".into()).expect("store should reopen");
        assert!(
            store.all_active_facts().unwrap().is_empty(),
            "preflight must prevent every row in the rejected call from being written"
        );
    }
    {
        let engine = fresh_open(&path, "clean registry should replay");
        assert_eq!(
            engine.assert_text("dog(Adam) & big(Adam).").unwrap(),
            vec![0],
            "rejection must not consume the durable or live id"
        );
        assert_true(
            &engine.query_holds("big(exactly 1 dog).").unwrap(),
            "ordinary facts support the query before reopen",
        );
        assert_eq!(
            engine
                .assert_text("believe(me, fact { big(exactly 1 dog) }).")
                .unwrap(),
            vec![1],
            "the same CountNode remains legal as opaque quoted content"
        );
    }
    {
        let reopened = fresh_open(&path, "ordinary facts should replay");
        assert_true(
            &reopened.query_holds("big(exactly 1 dog).").unwrap(),
            "the same snapshot count must hold after reopen",
        );
        assert_true(
            &reopened
                .query_holds("believe(me, fact { big(exactly 1 dog) }).")
                .unwrap(),
            "opaque quoted count content must replay without becoming a constraint",
        );
    }

    cleanup(&path);
}

#[test]
fn legacy_persisted_count_buffer_fails_replay_without_deleting_the_row() {
    let path = temp_db_path("legacy_count_assertion");
    cleanup(&path);

    let compiler = fresh_engine();
    let count = compiler
        .compile_debug("big(exactly 1 dog).")
        .expect("count query syntax must still compile");
    let payload = postcard::to_allocvec(&count).expect("fixture should serialize");
    {
        let mut store = NibliStore::open(&path, "local".into()).expect("store should open");
        store
            .insert_fact(7, "legacy count assertion".into(), payload)
            .expect("legacy fixture should persist");
    }

    let error = match NibliEngine::open(&path) {
        Ok(_) => panic!("a legacy count assertion must not regenerate witnesses"),
        Err(error) => error,
    };
    assert!(
        error.contains("Replay error (fact 7)")
            && error.contains("query-only")
            && error.contains("cannot be asserted"),
        "replay failure must identify the row and migration contract: {error}"
    );
    {
        let store = NibliStore::open(&path, "local".into()).expect("store should reopen");
        assert!(
            store.get_fact(7).unwrap().is_some(),
            "failed replay is non-destructive; the operator must repair/re-import explicitly"
        );
    }

    cleanup(&path);
}

#[test]
fn assertion_coreference_survives_rebuild_reopen_and_retraction() {
    let path = temp_db_path("assertion_coreference_replay");
    cleanup(&path);

    let shared_id = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let spacer_id = engine.assert_text("cat($spacer).").unwrap()[0];
        let shared_id = engine
            .assert_text("bite($x, Bel) & bite($x, Dana).")
            .unwrap()[0];
        engine
            .assert_text("all $w: bite($w, Bel) & bite($w, Dana) -> animal($w).")
            .unwrap();
        assert_true(
            &engine.query_holds("animal($who).").unwrap(),
            "the stored compound must initially expose one joint witness",
        );

        engine
            .retract_fact(spacer_id)
            .expect("retracting an earlier existential must rebuild the KB");
        assert_true(
            &engine.query_holds("animal($who).").unwrap(),
            "Skolem renumbering during rebuild must preserve co-reference",
        );
        shared_id
    };

    {
        let reopened = fresh_open(&path, "Persistent engine should replay the compound");
        assert_true(
            &reopened.query_holds("animal($who).").unwrap(),
            "serialized-buffer replay must preserve the joint witness",
        );
        reopened
            .retract_fact(shared_id)
            .expect("the shared compound must retract as one fact");
        assert_false(
            &reopened.query_holds("animal($who).").unwrap(),
            "retracting the compound must remove the joint derivation",
        );
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should retain the tombstone");
        assert_false(
            &reopened.query_holds("animal($who).").unwrap(),
            "the retracted compound must not resurrect after reopen",
        );
    }

    cleanup(&path);
}

#[test]
fn internal_skolem_and_user_sk_0_remain_distinct_across_reopen_and_retraction() {
    let path = temp_db_path("typed_skolem_identity_replay");
    cleanup(&path);

    let (generated_id, user_id) = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let generated_id = engine
            .assert_text("dog($generated).")
            .expect("generated witness should persist")[0];
        let user_id = engine
            .assert_text("dog(\"sk_0\").")
            .expect("equal-looking user constant should persist")[0];

        let found = engine.query_find_text("dog($d).").unwrap();
        assert_eq!(found.len(), 2, "both semantic identities must enumerate");
        assert_eq!(
            found
                .iter()
                .flatten()
                .filter(|binding| {
                    binding.variable == "$d"
                        && binding.origin == EngineWitnessOrigin::GeneratedWitness
                })
                .count(),
            1
        );
        assert_eq!(
            found
                .iter()
                .flatten()
                .filter(|binding| {
                    binding.variable == "$d" && binding.origin == EngineWitnessOrigin::KnowledgeBase
                })
                .count(),
            1
        );
        assert_eq!(engine.count_witnesses_text("dog($d).").unwrap(), 2);
        assert_true(
            &engine.query_holds("dog(\"sk_0\").").unwrap(),
            "the user-authored constant must be queryable by its own spelling",
        );
        (generated_id, user_id)
    };

    {
        let reopened = fresh_open(&path, "Persistent engine should replay both identities");
        assert_eq!(reopened.count_witnesses_text("dog($d).").unwrap(), 2);
        reopened
            .retract_fact(user_id)
            .expect("the user-authored constant should retract independently");
        assert_eq!(reopened.count_witnesses_text("dog($d).").unwrap(), 1);
        assert_false(
            &reopened.query_holds("dog(\"sk_0\").").unwrap(),
            "an internal witness with the same display label must not satisfy the user query",
        );
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should retain the user tombstone");
        let found = reopened.query_find_text("dog($d).").unwrap();
        assert_eq!(found.len(), 1);
        let subject = found[0]
            .iter()
            .find(|binding| binding.variable == "$d")
            .expect("the requested witness variable must be returned");
        assert_eq!(subject.origin, EngineWitnessOrigin::GeneratedWitness);
        reopened
            .retract_fact(generated_id)
            .expect("the generated witness assertion should retract independently");
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should retain both tombstones");
        assert_eq!(reopened.count_witnesses_text("dog($d).").unwrap(), 0);
    }

    cleanup(&path);
}

#[test]
fn opaque_abstraction_identity_survives_persistence_and_retraction() {
    let path = temp_db_path("opaque_abstraction_identity");
    cleanup(&path);

    let belief_id = {
        let engine = fresh_open(&path, "Persistent engine should open");
        let belief_id = engine
            .assert_text("believe(me, fact { goes(Adam) }).")
            .expect("opaque proposition should persist")[0];
        assert_true(
            &engine
                .query_holds("believe(me, fact { goes(Adam) }).")
                .unwrap(),
            "same-content assertion/query compiles must agree",
        );
        assert_false(
            &engine
                .query_holds("believe(me, fact { goes(Bel) }).")
                .unwrap(),
            "different bodies must remain distinct",
        );
        assert_false(
            &engine
                .query_holds("believe(me, event { goes(Adam) }).")
                .unwrap(),
            "different abstraction kinds must remain distinct",
        );
        assert_false(
            &engine.query_holds("goes(Adam).").unwrap(),
            "the abstraction body must remain opaque",
        );
        belief_id
    };

    {
        let reopened = fresh_open(&path, "Persistent engine should replay the abstraction");
        assert_true(
            &reopened
                .query_holds("believe(me, fact { goes(Adam) }).")
                .unwrap(),
            "a fresh compiler session must match the persisted full identity",
        );
        assert_false(
            &reopened
                .query_holds("believe(me, fact { goes(Bel) }).")
                .unwrap(),
            "reopen must not conflate a different full identity",
        );
        reopened
            .retract_fact(belief_id)
            .expect("the persisted abstraction should retract");
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should retain the tombstone");
        assert_false(
            &reopened
                .query_holds("believe(me, fact { goes(Adam) }).")
                .unwrap(),
            "a retracted opaque proposition must not resurrect",
        );
    }

    cleanup(&path);
}

#[test]
fn nested_opaque_abstraction_identity_survives_persistence() {
    let path = temp_db_path("nested_opaque_abstraction_identity");
    cleanup(&path);

    let asserted = "believe(me, fact { believe(Bel, fact { goes(Adam) }) }).";
    {
        let engine = fresh_open(&path, "Persistent engine should open");
        engine
            .assert_text(asserted)
            .expect("nested opaque proposition should persist");
        assert_true(
            &engine.query_holds(asserted).unwrap(),
            "same nested proposition must match",
        );
        assert_false(
            &engine
                .query_holds("believe(me, fact { believe(Bel, fact { goes(Gia) }) }).")
                .unwrap(),
            "a changed nested body must remain distinct",
        );
        assert_false(
            &engine
                .query_holds("believe(me, fact { believe(Bel, event { goes(Adam) }) }).")
                .unwrap(),
            "a changed nested abstraction kind must remain distinct",
        );
        assert_false(
            &engine
                .query_holds("believe(Bel, fact { goes(Adam) }).")
                .unwrap(),
            "the nested proposition must not leak as an actual belief",
        );
    }

    {
        let reopened = fresh_open(&path, "Persistent engine should replay nested identity");
        assert_true(
            &reopened.query_holds(asserted).unwrap(),
            "fresh-session compilation must match the persisted nested key",
        );
        assert_false(
            &reopened
                .query_holds("believe(me, fact { believe(Bel, fact { goes(Gia) }) }).")
                .unwrap(),
            "reopen must not conflate a changed nested body",
        );
    }

    cleanup(&path);
}

#[test]
fn persistent_engine_rejects_legacy_hash_only_abstraction_rows() {
    let path = temp_db_path("legacy_hash_only_abstraction");
    cleanup(&path);

    let compiler = fresh_engine();
    let mut legacy = compiler
        .compile_debug("believe(me, fact { goes(Adam) }).")
        .expect("fixture should compile");
    for node in &mut legacy.nodes {
        if let EngineLogicNode::Predicate((relation, _)) = node
            && relation.starts_with("__abs_v1_")
        {
            *relation = "__abs_0123456789abcdef".to_string();
        }
    }
    let payload = postcard::to_allocvec(&legacy).expect("fixture should serialize");
    {
        let mut store = NibliStore::open(&path, "local".into()).expect("store should open");
        let id = store.next_fact_id().expect("store should mint an id");
        store
            .insert_fact(id, "legacy opaque proposition".into(), payload)
            .expect("legacy fixture should persist");
    }

    let error = match NibliEngine::open(&path) {
        Ok(_) => panic!("a hash-only opaque identity must not replay silently"),
        Err(error) => error,
    };
    assert!(
        error.contains("legacy hash-only opaque-abstraction marker")
            && error.contains("recompile/re-import"),
        "the migration failure must be explicit and actionable: {error}"
    );

    cleanup(&path);
}

#[test]
fn persistent_engine_discards_legacy_typed_mirror_before_registry_replay() {
    use nibli_reason::kb::{GroundFact, GroundTerm, StoredFact};

    const TYPED_FACTS: TableDefinition<u64, &[u8]> = TableDefinition::new("typed_facts");

    let path = temp_db_path("legacy_typed_mirror_abstraction");
    cleanup(&path);
    {
        let engine = fresh_open(&path, "persistent engine should open");
        engine
            .assert_text("believe(me, fact { goes(Adam) }).")
            .expect("canonical registry fact should persist");
    }

    // Inject an old hash-only row into the disposable compiled-fact mirror.
    // Direct RedbFactStore::open correctly rejects this row; NibliEngine must
    // instead discard the entire mirror without decoding it, then rebuild from
    // the canonical LogicBuffer registry above.
    let typed_path = path.with_extension("typed.redb");
    {
        let db = Database::create(&typed_path).unwrap();
        let txn = db.begin_write().unwrap();
        {
            let mut facts = txn.open_table(TYPED_FACTS).unwrap();
            let legacy = StoredFact::Bare(GroundFact::new(
                "__abs_0123456789abcdef",
                vec![GroundTerm::Constant("opaque".to_string())],
            ));
            let bytes = postcard::to_allocvec(&legacy).unwrap();
            facts.insert(9999, bytes.as_slice()).unwrap();
        }
        txn.commit().unwrap();
    }

    let reopened = fresh_open(
        &path,
        "legacy typed mirror must be recoverable from the authoritative registry",
    );
    assert_true(
        &reopened
            .query_holds("believe(me, fact { goes(Adam) }).")
            .unwrap(),
        "registry replay must restore the canonical abstraction fact",
    );

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
// Schema v3 migration (finalize_v3 restamp; Text→Buffer recompile-once)
// ════════════════════════════════════════════════════════════════════

/// Stamp `schema_version = 2` into an existing DB, simulating a pre-v3 database.
/// The table name mirrors nibli-store's private `META_TABLE` (a stable on-disk name).
fn v2_meta_downgrade(path: &Path) {
    use redb::{Database, TableDefinition};
    const META: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata");
    let db = Database::create(path).unwrap();
    let txn = db.begin_write().unwrap();
    {
        let mut meta = txn.open_table(META).unwrap();
        let bytes = postcard::to_allocvec(&2u32).unwrap();
        meta.insert("schema_version", bytes.as_slice()).unwrap();
    }
    txn.commit().unwrap();
}

/// Seed a fresh v2 HOST DB with exactly one active `StoredAssertion::Text` row
/// (table names mirror nibli-store's stable `FACTS_TABLE` / `META_TABLE`).
fn seed_v2_host_text_row(path: &Path, id: u64, text: &str) {
    use nibli_store::{StoredAssertion, StoredFactRecord};
    use redb::{Database, TableDefinition};
    const FACTS: TableDefinition<u64, &[u8]> = TableDefinition::new("facts");
    const META: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata");
    let record = StoredFactRecord {
        id,
        payload: postcard::to_allocvec(&StoredAssertion::Text(text.to_string())).unwrap(),
        label: text.to_string(),
        retracted: false,
        node_id: "seed".to_string(),
        hlc_timestamp: id,
        predicates: Vec::new(),
    };
    let db = Database::create(path).unwrap();
    let txn = db.begin_write().unwrap();
    {
        let mut facts = txn.open_table(FACTS).unwrap();
        let bytes = postcard::to_allocvec(&record).unwrap();
        facts.insert(id, bytes.as_slice()).unwrap();
        let mut meta = txn.open_table(META).unwrap();
        let vb = postcard::to_allocvec(&2u32).unwrap();
        meta.insert("schema_version", vb.as_slice()).unwrap();
    }
    txn.commit().unwrap();
}

/// A legacy v2 ENGINE DB (bare `LogicBuffer` payloads, no `Text` rows) upgrades to v3
/// by a version restamp (`finalize_v3`) and replays — it is not rejected like v1.
#[test]
fn v2_engine_db_restamps_to_v3_and_replays() {
    let path = temp_db_path("v3_engine_restamp");
    cleanup(&path);
    {
        let engine = fresh_open(&path, "engine should open");
        engine.assert_text("dog(Adam).").expect("fact persists");
    }
    v2_meta_downgrade(&path); // simulate a pre-v3 engine DB
    {
        let store = NibliStore::open(&path, "local".into()).expect("store opens v2");
        assert!(
            store.needs_migration(),
            "downgraded DB should read as migratable"
        );
    }
    {
        let engine = fresh_open(&path, "engine reopens v2 → v3");
        assert!(
            engine.query_holds("dog(Adam).").unwrap().is_true(),
            "a v2 engine DB must replay after the v3 restamp, not be rejected",
        );
    }
    {
        let store = NibliStore::open(&path, "local".into()).expect("store reopens");
        assert!(
            !store.needs_migration(),
            "engine open must have finalized v3"
        );
    }
    cleanup(&path);
}

/// A legacy v2 HOST DB with a `StoredAssertion::Text` row migrates: the source text is
/// recompiled (real compiler — the same chain the host's `compile-debug` uses) into a
/// Buffer row that preserves the WHOLE composite buffer (no `split_roots`), and the
/// migrated buffer replays to the same verdict as asserting the text fresh.
#[test]
fn v2_text_row_migrates_via_real_compiler_and_replays() {
    use nibli_store::StoredAssertion;
    use nibli_types::logic::LogicBuffer;

    let path = temp_db_path("v3_text_fidelity");
    cleanup(&path);
    let text = "dog(Adam). dog(Bel)."; // multi-`.i` composite → one whole fact
    seed_v2_host_text_row(&path, 7, text);

    let preds = nibli_reason::default_compute_predicates();
    let mut store = NibliStore::open(&path, "local".into()).expect("store opens v2");
    assert!(store.needs_migration());
    let migrated = store
        .migrate_v2_text_rows(|t| {
            nibli_session::compile_text(t, &preds)
                .map(|buf| postcard::to_allocvec(&buf).expect("serialize buffer"))
                .map_err(|e| e.to_string())
        })
        .expect("KR text migrates");
    assert_eq!(migrated, 1);
    assert!(!store.needs_migration());

    // Migrated row is a Buffer holding the WHOLE composite (both roots, not split).
    let rec = store.get_fact(7).unwrap().unwrap();
    let inner = match postcard::from_bytes::<StoredAssertion>(&rec.payload).unwrap() {
        StoredAssertion::Buffer(inner) => inner,
        other => panic!("migrated row must be Buffer, got {other:?}"),
    };
    let buf: LogicBuffer = postcard::from_bytes(&inner).expect("inner decodes as LogicBuffer");
    let fresh = nibli_session::compile_text(text, &preds).unwrap();
    assert_eq!(
        buf.roots.len(),
        fresh.roots.len(),
        "whole composite buffer preserved (not split into per-root rows)",
    );
    assert!(
        buf.roots.len() >= 2,
        "the two-sentence composite has multiple roots"
    );
    assert_eq!(
        rec.label, text,
        "label sourced from the recovered payload text"
    );

    // Replay the migrated buffer (as the host's Buffer replay does) → same verdict.
    let core = nibli_session::CoreSession::new();
    core.kb()
        .assert_fact_with_id(buf, text.to_string(), rec.id)
        .expect("replay asserts the migrated buffer");
    assert!(core.query_text("dog(Adam).").unwrap().is_true());
    assert!(core.query_text("dog(Bel).").unwrap().is_true());
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

/// Utopia constitutional corpus: every non-comment line asserts, scenario pins
/// hold, store+derived-negation scan is clean on the shipped scenario.
#[test]
fn utopia_file_loads_and_pins() {
    let corpus = include_str!("../../utopia.nibli");
    let engine = fresh_engine();
    let mut n = 0u32;
    for (line_num, line) in corpus.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        engine.assert_text(trimmed).unwrap_or_else(|e| {
            panic!(
                "utopia.nibli line {} failed to assert: {:?}\n{}",
                line_num + 1,
                trimmed,
                e
            )
        });
        n += 1;
    }
    assert!(n >= 60, "expected a full utopia corpus, got {n} statements");

    let pins: &[(&str, bool)] = &[
        ("person(Adam).", true),
        ("expresses(Adam).", true),
        ("travel(Adam).", false),
        ("travel(Bela).", true),
        ("false(Bela).", true),
        ("reward(Bela).", false),
        ("lose(Points, Bela).", true),
        ("lose(Points, Cira).", true),
        ("false(Dev).", true),
        ("reward(Gia).", true),
        ("false(Lupo).", true),
        ("false(Mira).", false),
        ("reward(Mira).", true),
        ("false(Esa).", false),
        ("reward(Esa).", true),
        ("reward(Quin).", true), // Art 3 work path
        ("reward(Koa).", false),
        ("prisoner(Hano).", true),
        ("dwell(Hano).", true),
        ("prisoner(Jala).", false),
        ("prisoner(Nia).", false),
        ("prisoner(Lalo).", true),
        ("building(HighSec, Lalo).", true),
        ("dwell(Lalo).", true),
        ("prisoner(Nando).", true),
        ("building(LowSec, Nando).", true),
        ("dwell(Nando).", true),
        ("obliged(Adam, event { eats() }).", true),
    ];
    for (q, want_true) in pins {
        let r = engine
            .query_holds(q)
            .unwrap_or_else(|e| panic!("query {q}: {e}"));
        if *want_true {
            assert_true(&r, q);
        } else {
            assert_false(&r, q);
        }
    }

    assert!(
        engine.check_contradictions().is_empty(),
        "shipped utopia scenario must be store+derived-negation clean: {:?}",
        engine.check_contradictions()
    );
}

/// Category-4 cheap middle through the full engine: derived travel vs ~travel.
#[test]
fn utopia_style_derived_negation_contradiction_flagged() {
    let engine = engine_with_facts(&[
        "travel(every person where ~prisoner).",
        "person(Kilo).",
        "~travel(Kilo).",
    ]);
    assert_true(
        &engine.query_holds("travel(Kilo).").unwrap(),
        "travel(Kilo) derived",
    );
    let v = engine.check_contradictions();
    assert!(
        v.iter().any(|m| m.contains("Negation contradiction")),
        "derived positive must flag against asserted negation: {v:?}"
    );
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
        "obliged(every healthy data, event { exact() }).",
        "healthy data(Kanrek).",
        "data(Ordrek).",
    ]);
    assert_true(
        &engine
            .query_holds("obliged(Kanrek, event { exact() }).")
            .unwrap(),
        "Health data requires a stricter basis (Art 9)",
    );
    assert_false(
        &engine
            .query_holds("obliged(Ordrek, event { exact() }).")
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
        "obliged(every data, event { correct() }).",
        "healthy data(Kanrek).",
    ]);
    let (holds, trace, _json) = engine
        .query_text_with_proof("obliged(Kanrek, event { correct() }).")
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
        "obliged(every data governs where flaw, event { message() }).",
        "data governs(Akmes).",
        "data governs(Gugli).",
        "flaw(Akmes).", // only AkmeCorp breached
    ]);
    assert_true(
        &engine
            .query_holds("obliged(Akmes, event { message() }).")
            .unwrap(),
        "A breached controller must notify (Art 33)",
    );
    assert_false(
        &engine
            .query_holds("obliged(Gugli, event { message() }).")
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
        .assert_text("obliged(every person where ~approves, event { removes() }).")
        .expect("the negated-restrictor erasure rule must now compile");

    // ── No consent → the erasure obligation arises (NAF: no consent witness). ──
    assert_true(
        &engine
            .query_holds("obliged(Adam, event { removes() }).")
            .unwrap(),
        "No consent → erasure obligation holds (Art 17 as a stored rule)",
    );

    // ── Consent present → the negated restrictor is false → no obligation. ──
    let consent_id = engine.assert_text("approves(Adam).").unwrap()[0];
    assert_false(
        &engine
            .query_holds("obliged(Adam, event { removes() }).")
            .unwrap(),
        "Consent present → no erasure obligation",
    );

    // ── Withdraw consent → the obligation re-arises, flagged NAF-dependent. ──
    engine.retract_fact(consent_id).unwrap();
    let (holds, trace, json) = engine
        .query_text_with_proof("obliged(Adam, event { removes() }).")
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
        .assert_text("obliged(every person where ~approves, event { removes() }).")
        .unwrap();
    engine.assert_text("approves(Bet).").unwrap(); // bet consents; adam does not

    assert_true(
        &engine
            .query_holds("obliged(Adam, event { removes() }).")
            .unwrap(),
        "adam (no consent) is obligated to be erased",
    );
    assert_false(
        &engine
            .query_holds("obliged(Bet, event { removes() }).")
            .unwrap(),
        "bet (consented) is NOT obligated — the rule is per-subject, not global",
    );
}

/// PERF REGRESSION PIN (book Ch 19 GDPR reproducibility): the chapter tells
/// readers to load the FULL shipped gdpr.nibli and check lawful basis for Adam.
/// Before the 2026-06 backward-chaining fixes in nibli-reason (lazy candidate
/// build, index-decidable filter pruning, depth-horizon provability lookahead),
/// this query did not return within 240 seconds in a debug build: at the depth
/// horizon every unbound-event-variable filter check returned ResourceExceeded
/// and pessimistically kept the entire members^k candidate cartesian product
/// alive. Post-fix the full Ch 19 sequence — lawful-basis query, consent
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
                "gdpr.nibli line {} failed to assert: {:?}\n{}",
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

    // Ch 19's first lawful-basis query, against the FULL loaded corpus.
    assert_true(
        &engine.query_holds("permitted(Adam).").unwrap(),
        "Against the full corpus, Adam's processing has a lawful basis (Art 6)",
    );

    // The consent-withdrawal belief-revision flip, also against the full corpus.
    engine
        .retract_fact(consent_id.expect("consent line present in gdpr.nibli"))
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
    // on a small engine. Querying erasure against the FULL corpus is deliberately NOT
    // done here — it fans out across every Art 5/9 obligation rule, which would
    // dominate this timing pin without testing anything new.)

    let elapsed = start.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(120),
        "full-corpus Ch 19 sequence took {elapsed:?} (budget 120s) — the \
         backward-chaining candidate search has regressed"
    );
}

// ════════════════════════════════════════════════════════════════════
// Derived-only (intensional / IDB) relations — `derived_only("<rel>")`
//
// Without this, a rule only ADDS a derivation path and never REMOVES
// assertability, so a KB that DERIVES a credential
//
//     all $a: choose(Electorate, $a) & ~rotten($a) & ~broken($a)
//             -> permits(Review, $a).
//
// cannot stop anyone from handing themselves one with `permits(Review, Sock).`
// Declaring the relation derived-only closes that route fail-closed at assert
// time, turning "write one fact" into "edit the knowledge base" — a diffable,
// reviewable act. That change in the SHAPE of the attack is the whole point,
// and it is why this rejects rather than lints.
// ════════════════════════════════════════════════════════════════════

/// The credential rule the tests below defend, plus its legitimate seed facts.
const CREDENTIAL_KB: &[&str] = &[
    "derived_only(\"permits\").",
    "all $a: choose(Electorate, $a) & ~rotten($a) & ~broken($a) -> permits(Review, $a).",
    "choose(Electorate, Gia).",
];

/// The derivation route still works — closing a relation must not close the
/// door it exists to protect.
#[test]
fn derived_only_still_derives() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    assert_true(
        &engine.query_holds("permits(Review, Gia).").unwrap(),
        "a seated auditor still derives the credential",
    );
    assert_false(
        &engine.query_holds("permits(Review, Sock).").unwrap(),
        "an unseated one does not",
    );
}

/// The assertion route is closed, fail-closed, with a `Reasoning` error naming
/// the relation.
#[test]
fn derived_only_refuses_direct_assertion() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    let err = engine
        .assert_text("permits(Review, Sock).")
        .expect_err("a closed relation must not be directly assertable");
    assert!(
        matches!(err, EngineError::Reasoning(_)),
        "must be a Reasoning error, not a syntax one: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("permits") && msg.contains("derived-only"),
        "the error must name the relation and the reason: {msg}"
    );
    // And it must not have half-landed.
    assert_false(
        &engine.query_holds("permits(Review, Sock).").unwrap(),
        "the refused fact must leave no trace",
    );
}

/// The refusal is ATOMIC: a conjunction that mixes a legal fact with a closed
/// one must land neither.
#[test]
fn derived_only_refusal_is_atomic() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    assert!(
        engine
            .assert_text("person(Sock) & permits(Review, Sock).")
            .is_err()
    );
    assert_false(
        &engine.query_holds("person(Sock).").unwrap(),
        "the legal conjunct must be rolled back with the illegal one",
    );
}

/// CONSTRAINT: the declaration survives retraction and the fact-store rebuild.
/// A relation must not become assertable again after a replay.
#[test]
fn derived_only_survives_retraction_and_replay() {
    let engine = fresh_engine();
    for line in CREDENTIAL_KB {
        engine.assert_text(line).unwrap();
    }
    let extra = engine.assert_text("choose(Electorate, Bet).").unwrap();
    // Retracting forces the registry rebuild + buffer replay.
    engine.retract_fact(extra[0]).unwrap();
    assert!(
        engine.assert_text("permits(Review, Sock).").is_err(),
        "the closure must survive the rebuild — this is the whole retraction constraint"
    );
    assert_true(
        &engine.query_holds("permits(Review, Gia).").unwrap(),
        "and derivation must still work after the replay",
    );
}

/// The declaration is ordinary KB content: a wiped KB starts with no closures.
/// (Retraction safety does not rely on this — `rebuild_inner` has its own clear
/// list, and replay re-asserts the declaration anyway.)
#[test]
fn derived_only_is_cleared_by_reset() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    assert!(engine.assert_text("permits(Review, Sock).").is_err());
    engine.reset().unwrap();
    engine
        .assert_text("permits(Review, Sock).")
        .expect("a reset KB has no closures");
}

/// Declaring is idempotent and order-independent with respect to the rule.
#[test]
fn derived_only_declaration_order_does_not_matter() {
    let engine = engine_with_facts(&[
        "all $a: choose(Electorate, $a) & ~rotten($a) & ~broken($a) -> permits(Review, $a).",
        "choose(Electorate, Gia).",
        "derived_only(\"permits\").",
        "derived_only(\"permits\").",
    ]);
    assert!(engine.assert_text("permits(Review, Sock).").is_err());
    assert_true(&engine.query_holds("permits(Review, Gia).").unwrap(), "");
}

/// Closing one relation must not close unrelated ones.
#[test]
fn derived_only_is_scoped_to_the_named_relation() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    engine
        .assert_text("person(Adam).")
        .expect("an unrelated relation stays open");
    engine
        .assert_text("choose(Electorate, Bet).")
        .expect("the rule's own antecedent relation stays assertable");
}

/// SECURITY-CRITICAL: closing a relation closes EVERY surface spelling of it,
/// including converted aliases. `permitted` is the x1<->x2 conversion of
/// `permits` and compiles to the same IR relation, so `permitted(Adam).` is
/// refused by a `derived_only("permits")` declaration.
///
/// If it were not, the declaration would be trivially bypassable: an attacker
/// blocked from writing `permits(...)` would simply write `permitted(...)` and
/// get the identical stored fact. The check tests the COMPILED relation, after
/// alias resolution, which is what makes that impossible.
#[test]
fn derived_only_closes_converted_alias_spellings_too() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    let err = engine
        .assert_text("permitted(Adam).")
        .expect_err("the converted alias must not be a bypass");
    assert!(
        err.to_string().contains("permits"),
        "the error names the CANONICAL relation, which is the one actually closed: {err}"
    );
}

/// A declaration placed BELOW the facts it means to close is refused.
///
/// The check fires at assert time, so such a declaration protects nothing — and
/// it used to do so SILENTLY: the KB loaded at zero errors and was
/// indistinguishable from a working closure. That is a false green that could
/// survive indefinitely, so an inert declaration is made unrepresentable rather
/// than merely detectable.
#[test]
fn derived_only_refuses_an_inert_late_declaration() {
    let engine = engine_with_facts(&["permits(Review, Sock)."]);
    let err = engine
        .assert_text("derived_only(\"permits\").")
        .expect_err("a declaration that protects nothing must not look like one that works");
    let msg = err.to_string();
    assert!(
        msg.contains("comes too late") && msg.contains("permits"),
        "the error must say WHY and name the relation: {msg}"
    );
}

/// …but declaring after the RULES is fine. Only ASSERTED facts can make a
/// declaration too late: derivations are computed by backward chaining and never
/// stored, so a relation a rule merely concludes stays declarable. This is the
/// common authoring order and must not be collateral damage.
#[test]
fn derived_only_late_declaration_is_fine_after_rules_only() {
    let engine = engine_with_facts(&[
        "all $a: choose(Electorate, $a) & ~rotten($a) & ~broken($a) -> permits(Review, $a).",
        "choose(Electorate, Gia).",
        "derived_only(\"permits\").",
    ]);
    assert_true(
        &engine.query_holds("permits(Review, Gia).").unwrap(),
        "the derived credential survives a late declaration",
    );
    assert!(
        engine.assert_text("permits(Review, Sock).").is_err(),
        "and the closure is live"
    );
}

/// Re-declaring an already-closed relation stays idempotent even though facts
/// for it may exist — the too-late check must not fire on a no-op.
#[test]
fn derived_only_redeclaration_is_idempotent() {
    let engine = engine_with_facts(&["derived_only(\"permits\").", "person(Adam)."]);
    engine
        .assert_text("derived_only(\"permits\").")
        .expect("re-declaring a closed relation is a no-op, not an error");
}

/// The declaration is itself queryable — the closure list is inspectable rather
/// than hidden engine state.
#[test]
fn derived_only_declaration_is_queryable() {
    let engine = engine_with_facts(CREDENTIAL_KB);
    assert_true(
        &engine.query_holds("derived_only(\"permits\").").unwrap(),
        "the declaration stores like any assertion",
    );
}

// ════════════════════════════════════════════════════════════════════
// Rights-floor stratification firewall (`entitled`)
//
// A constitutional/unconditional rights floor is spelled with the entitled
// party in x1 and the guaranteed event in x2:
//
//     entitled(every person, event { eats() }).
//
// The SAFETY PROPERTY these tests pin: once such a floor is asserted, no rule
// can punish someone for lacking the floor right, because the punishing rule
// closes a negative cycle and is rejected as unstratifiable.
//
// The mechanism is subtle and lives in an ASYMMETRY inside nibli-reason:
// `event { eats() }` compiles to an abstraction, and `rules::flatten_consequent`
// descends BOTH branches of the head's `And` unconditionally — so the
// abstraction body's `eats` atom lands in the rule head and becomes a
// dependency edge `eats -> person`. `rules::collect_ground_facts`, by contrast,
// DOES honour `__abs_` opacity and skips the body. If flatten_consequent were
// ever "fixed" for symmetry, every floor below would silently become
// stratifiable and the punishing rules would start registering — a soundness
// regression with no other test to catch it.
// ════════════════════════════════════════════════════════════════════

/// The floor itself asserts, and the `entitled` place structure routes as
/// committed: x1 = holder, x2 = entitlement, x3 = standard (unfilled here — the
/// floor is deliberately unconditional, and nothing may require a standard).
#[test]
fn rights_floor_entitled_asserts_and_routes() {
    let engine = engine_with_facts(&["entitled(every person, event { eats() }).", "person(Adam)."]);
    assert_true(
        &engine
            .query_holds("entitled(Adam, event { eats() }).")
            .unwrap(),
        "a person is entitled to the floor right",
    );
    // Named-arg routing agrees with the positional form.
    let engine = engine_with_facts(&["entitled(holder: Adam, entitlement: Bread)."]);
    assert_true(
        &engine.query_holds("entitled(Adam, Bread).").unwrap(),
        "named-arg routing must equal positional routing",
    );
    // A label from the deontic sibling `obliged` (bound/duty/standard) must NOT
    // resolve — the two place structures are deliberately distinct.
    assert!(
        fresh_engine()
            .assert_text("entitled(bound: Adam).")
            .is_err(),
        "`entitled` must not accept `obliged`'s place labels"
    );
}

/// THE OTHER HALF of the abstraction asymmetry: the head walk gains `eats` as a
/// dependency edge, but `collect_ground_facts` honours `__abs_` opacity, so the
/// floor must NOT derive that anyone ACTUALLY eats. An entitlement is not an
/// actuality — a floor that fabricated the fact it guarantees would be exactly
/// the hallucination this engine exists to rule out.
///
/// This pins the opacity side deliberately: `rules::collect_ground_facts`'s guard
/// and the `flatten_consequent` walk must stay asymmetric. Making them symmetric
/// in EITHER direction breaks something — drop the opacity guard and the floor
/// starts asserting that everyone eats; honour opacity in the head walk too and
/// the stratification firewall above silently disappears.
#[test]
fn rights_floor_does_not_fabricate_the_actuality() {
    let engine = engine_with_facts(&["entitled(every person, event { eats() }).", "person(Adam)."]);
    assert_true(
        &engine
            .query_holds("entitled(Adam, event { eats() }).")
            .unwrap(),
        "the entitlement itself holds",
    );
    assert_false(
        &engine.query_holds("eats(Adam).").unwrap(),
        "being entitled to eat must NOT derive that Adam eats",
    );
    assert_false(
        &engine.query_holds("eats(some person).").unwrap(),
        "nor that some person eats — the abstraction body stays opaque",
    );
}

/// THE FIREWALL: with the floor + "prisoners remain persons" asserted, a rule
/// that would jail anyone who does not eat is REJECTED as unstratifiable.
/// Cycle: `prisoner ->(neg) eats` (the punishing rule) + `eats -> person` (the
/// floor's abstraction body in the rule head) + `person -> prisoner` (closure).
#[test]
fn rights_floor_blocks_punishment_for_lacking_it() {
    let engine = engine_with_facts(&[
        "entitled(every person, event { eats() }).",
        "all $anyone: prisoner($anyone) -> person($anyone).",
    ]);
    let err = engine
        .assert_text("all $x: person($x) & ~eats($x) -> prisoner($x).")
        .expect_err("a rule punishing the absence of a floor right must be rejected");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("Unstratifiable") && msg.contains("prisoner") && msg.contains("eats"),
        "the rejection must name the prisoner->eats negative cycle, got: {msg}"
    );
}

/// NEGATIVE CONTROL: the rejection above is caused by the floor, not by the
/// punishing rule being intrinsically unstratifiable. Without the floor line the
/// very same rule registers and fires.
#[test]
fn punishment_rule_alone_is_stratifiable() {
    let engine = engine_with_facts(&[
        "all $anyone: prisoner($anyone) -> person($anyone).",
        "all $x: person($x) & ~eats($x) -> prisoner($x).",
        "person(Adam).",
    ]);
    assert_true(
        &engine.query_holds("prisoner(Adam).").unwrap(),
        "with no floor asserted the punishing rule registers and fires",
    );
}

/// PLACEMENT DEPENDENCE: the firewall requires the universal in x1 and the event
/// in x2. Swap them and the floor contributes no `eats -> person` edge, the
/// punishing rule registers, and the protection is GONE. This is the shape a
/// future corpus/place-structure change could silently introduce, so pin it
/// explicitly rather than leaving it as folklore.
#[test]
fn rights_floor_protection_is_placement_dependent() {
    let engine = engine_with_facts(&[
        // Event in x1, universal in x2 — the WRONG spelling for a floor.
        "entitled(event { eats() }, every person).",
        "all $anyone: prisoner($anyone) -> person($anyone).",
    ]);
    assert!(
        engine
            .assert_text("all $x: person($x) & ~eats($x) -> prisoner($x).")
            .is_ok(),
        "universal-in-x2 must NOT build the firewall — if this starts failing, the \
         event-abstraction head walk changed and the x1 requirement may have been \
         relaxed (good news, but the floor docs and NIBLI_KR need updating)"
    );
    // And the danger is concrete, not theoretical: the rule now FIRES, so a person
    // gets jailed for the absence of a floor right. This is exactly the outcome the
    // x1 spelling exists to make unrepresentable.
    engine.assert_text("person(Adam).").unwrap();
    assert_true(
        &engine.query_holds("prisoner(Adam).").unwrap(),
        "with the floor mis-spelled, lacking the right is punishable",
    );
}

// ════════════════════════════════════════════════════════════════════
// Corpus transcript pins (book Ch 19 GDPR / Ch 20 DDI reproducibility)
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

/// TRANSCRIPT PIN (book Ch 19 GDPR): the chapter's captured REPL sessions print
/// `[Load] Done: 24 asserted, 77 skipped, 0 errors`, retract the consent fact
/// by id (#21), and — in the multi-basis walkthrough — assert `promise(Adam).`
/// right after the load and later retract it as #24. A corpus reorder,
/// insertion, or deletion silently invalidates those printed ids and counts;
/// this pin breaks loudly instead. If it fails: gdpr.nibli changed — recapture
/// the Ch 19 transcripts (book repo) together with these expected values.
#[test]
fn gdpr_corpus_transcript_pins() {
    let engine = fresh_engine();
    let (asserted, skipped, ids) = load_corpus_like_host(&engine, include_str!("../../gdpr.nibli"));
    assert_eq!(
        (asserted, skipped),
        (24, 77),
        "Ch 19 pins `[Load] Done: 24 asserted, 77 skipped, 0 errors`"
    );
    assert_eq!(
        pinned_id(&ids, "approves(Adam)."),
        21,
        "Ch 19 retracts the consent fact as id #21"
    );
    // The multi-basis walkthrough asserts the contract fact immediately after
    // the corpus load and later retracts it as #24.
    let contract_id = engine.assert_text("promise(Adam).").unwrap()[0];
    assert_eq!(
        contract_id, 24,
        "Ch 19 retracts the post-load contract fact as id #24"
    );
}

/// TRANSCRIPT PIN (book Ch 20 DDI): the chapter's captured REPL sessions print
/// `[Load] Done: 16 asserted, 78 skipped, 0 errors` and retract two facts by
/// id — the inhibition fact (#4, fluconazole discontinued) and the regimen
/// fact (#10, warfarin stopped). Same contract as the Ch 19 pin above: a
/// corpus edit must break this test, not silently drift the book.
#[test]
fn ddi_corpus_transcript_pins() {
    let engine = fresh_engine();
    let (asserted, skipped, ids) =
        load_corpus_like_host(&engine, include_str!("../../drug-interactions.nibli"));
    assert_eq!(
        (asserted, skipped),
        (16, 78),
        "Ch 20 pins `[Load] Done: 16 asserted, 78 skipped, 0 errors`"
    );
    assert_eq!(
        pinned_id(&ids, "prevents(Flukonazol, Siptucin)."),
        4,
        "Ch 20 retracts the inhibition fact as id #4"
    );
    assert_eq!(
        pinned_id(&ids, "uses(Adam, Varfarin)."),
        10,
        "Ch 20 retracts the warfarin regimen fact as id #10"
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
    assert_eq!(
        total,
        EngineAggregateOutcome::Value {
            value: 12.0,
            witnesses: 2
        },
        "Summed dose across drugs should be 12"
    );
}

/// The boolean verdict and the witness enumeration must AGREE about a numeric
/// comparison. `try_evaluate_numeric_group` used to have exactly one caller — the
/// `ExistsNode` arm of `check_formula_holds_core` — while `find_witnesses` had its own
/// `ExistsNode` arm that peeled the comparison group's `∃_ev` and enumerated domain
/// candidates, so every conjunct degraded to a store lookup that finds nothing. The
/// query then answered TRUE as a boolean and returned ZERO rows from
/// find/count/aggregate, with no error: a jointly inconsistent pair, which is the one
/// failure class this engine exists to prevent.
#[test]
fn numeric_threshold_verdict_and_find_agree() {
    let engine = engine_with_facts(&["quantity(Varfarin, 20).", "quantity(Fenitoin, 7)."]);
    let q = "quantity($da, $de) & greater($de, 15).";

    assert_eq!(
        engine.query_holds(q).unwrap(),
        EngineQueryResult::True,
        "the boolean verdict computes the comparison"
    );
    assert_eq!(
        engine.count_witnesses_text(q).unwrap(),
        1,
        "witness enumeration must find the one drug over the threshold, not zero"
    );
    let rows = engine.query_find_text(q).unwrap();
    assert_eq!(rows.len(), 1, "exactly one row past the threshold");
    assert!(
        rows[0].iter().any(|b| {
            b.variable == "$da" && nibli_engine::display_term(&b.term).contains("varfarin")
        }),
        "the row must be the drug whose quantity exceeds 15, got {rows:?}"
    );
    assert_eq!(
        engine
            .aggregate_text(q, "$de", EngineAggregateOp::Sum)
            .unwrap(),
        EngineAggregateOutcome::Value {
            value: 20.0,
            witnesses: 1
        },
        "aggregate sums only the witnesses past the threshold"
    );
}

/// The arithmetic twin of `numeric_threshold_verdict_and_find_agree`, end to end.
/// Built-in arithmetic decides locally, so it filters witness rows exactly as a
/// comparison does — and a ground group with no user variables must not report zero
/// rows against a TRUE verdict, which is what an empty domain used to produce.
#[test]
fn arithmetic_verdict_and_find_agree_end_to_end() {
    let engine = engine_with_facts(&["quantity(Varfarin, 20).", "quantity(Fenitoin, 7)."]);

    // Ground, no user variables, nothing asserted that matches: still one row.
    assert_eq!(
        engine.query_holds("product(10, 2, 5).").unwrap(),
        EngineQueryResult::True
    );
    assert_eq!(
        engine.count_witnesses_text("product(10, 2, 5).").unwrap(),
        1
    );
    assert_eq!(
        engine.count_witnesses_text("product(11, 2, 5).").unwrap(),
        0
    );

    // As a filtering conjunct over a real join.
    let q = "quantity($da, $de) & product(10, 2, 5).";
    assert_eq!(engine.query_holds(q).unwrap(), EngineQueryResult::True);
    assert_eq!(
        engine.count_witnesses_text(q).unwrap(),
        2,
        "a satisfied arithmetic conjunct filters nothing out"
    );
    assert_eq!(
        engine
            .aggregate_text(q, "$de", EngineAggregateOp::Sum)
            .unwrap(),
        EngineAggregateOutcome::Value {
            value: 27.0,
            witnesses: 2
        },
        "aggregate reaches both rows"
    );
    assert_eq!(
        engine
            .count_witnesses_text("quantity($da, $de) & product(11, 2, 5).")
            .unwrap(),
        0,
        "a false arithmetic conjunct drops every row"
    );
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

// Neutral compute-contract stub. `eats` exercises the text path because it is
// a committed corpus relation; `external_probe` exercises the native BYO-IR path
// because it deliberately is not text vocabulary.
fn stub_text_raw_contract_eval(rel: &str, args: &[EngineLogicalTerm]) -> Result<bool, String> {
    Ok(matches!(
        (rel, args.len()),
        ("eats", 2) | ("external_probe", 1)
    ))
}

fn stub_text_raw_contract_batch(reqs: &[EngineComputeRequest]) -> Vec<Result<bool, String>> {
    reqs.iter()
        .map(|request| stub_text_raw_contract_eval(&request.relation, &request.args))
        .collect()
}

fn root_flavor(buffer: &EngineLogicBuffer) -> &'static str {
    match &buffer.nodes[buffer.roots[0] as usize] {
        EngineLogicNode::PastNode(_) => "past",
        EngineLogicNode::PresentNode(_) => "now",
        EngineLogicNode::FutureNode(_) => "future",
        EngineLogicNode::ObligatoryNode(_) => "must",
        EngineLogicNode::PermittedNode(_) => "may",
        _ => "bare",
    }
}

#[test]
fn text_compute_registration_is_corpus_scoped_arity_checked_and_flavor_preserving() {
    let mut engine = fresh_engine();

    let registration_error = engine
        .register_compute_predicate("external_probe".to_string())
        .expect_err("registration must not declare unknown text vocabulary");
    assert!(
        matches!(registration_error, EngineError::Reasoning(_)),
        "registration policy belongs to the session/reasoning boundary: {registration_error}"
    );
    let registration_message = registration_error.to_string();
    assert!(
        registration_message.contains("not a corpus-resolvable")
            && registration_message.contains("does not declare")
            && registration_message.contains("infer arity"),
        "{registration_message}"
    );
    assert!(
        !engine
            .compute_predicates()
            .iter()
            .any(|name| name == "external_probe")
    );

    let query_error = engine
        .query_holds("external_probe(Sample).")
        .expect_err("unregistered unknown text must fail closed");
    assert!(
        matches!(query_error, EngineError::Syntax(_)),
        "{query_error}"
    );
    assert!(
        query_error
            .to_string()
            .contains("unknown predicate \"external_probe\"")
    );
    let validate_error = engine
        .validate("external_probe(Sample).")
        .expect_err("compile-only validation still enforces vocabulary");
    assert!(
        validate_error.contains("unknown predicate \"external_probe\""),
        "{validate_error}"
    );

    engine
        .register_compute_predicate("eats".to_string())
        .expect("an existing corpus relation may be routed to compute");
    engine.set_compute_dispatch(stub_text_raw_contract_eval, stub_text_raw_contract_batch);

    engine
        .validate("eats(Agent, Meal).")
        .expect("validate remains compile-only for a registered compute query");
    for statement in [
        "eats(Agent, Meal).",
        "all $x: person($x) & eats($x, Meal) -> animal($x).",
        "all $x: person($x) & ~eats($x, Meal) -> animal($x).",
        "all $x: person($x) -> eats($x, Meal).",
    ] {
        let assertion_error = engine
            .assert_text(statement)
            .expect_err("registered compute must be refused in every assertion/rule position");
        assert!(
            assertion_error.to_string().contains("query-only"),
            "{statement}: {assertion_error}"
        );
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "a refused compute-bearing statement must not mutate the KB: {statement}"
        );
    }

    let arity_error = engine
        .query_holds("eats(Agent, Meal, Extra).")
        .expect_err("registration must not override corpus arity");
    assert!(
        matches!(arity_error, EngineError::Syntax(_)),
        "{arity_error}"
    );
    assert!(
        arity_error
            .to_string()
            .contains("too many arguments for \"eats\" (arity 2)"),
        "{arity_error}"
    );

    for (prefix, expected_flavor) in [
        ("", "bare"),
        ("past ", "past"),
        ("now ", "now"),
        ("future ", "future"),
        ("must ", "must"),
        ("may ", "may"),
    ] {
        let text = format!("{prefix}eats(Agent, Meal).");
        let first = engine.compile_debug(&text).unwrap();
        let second = engine.compile_debug(&text).unwrap();
        assert_eq!(
            first, second,
            "registered compilation must be deterministic: {text}"
        );
        assert_eq!(root_flavor(&first), expected_flavor, "{text}: {first:#?}");
        assert!(
            first.nodes.iter().any(
                |node| matches!(node, EngineLogicNode::ComputeNode((name, _)) if name == "eats")
            ),
            "registration must mark the compiled relation without stripping its wrapper: {first:#?}"
        );
        assert_true(
            &engine.query_holds(&text).unwrap(),
            "every supported single flavor must reach the same registered compute check",
        );
    }

    let mut first_order = fresh_engine();
    first_order
        .register_compute_predicate("eats".to_string())
        .unwrap();
    first_order
        .register_compute_predicate("person".to_string())
        .unwrap();
    let mut opposite_order = fresh_engine();
    opposite_order
        .register_compute_predicate("person".to_string())
        .unwrap();
    opposite_order
        .register_compute_predicate("eats".to_string())
        .unwrap();
    assert_eq!(
        first_order.compute_predicates(),
        opposite_order.compute_predicates(),
        "the public registry report is deterministic across insertion order"
    );
    assert_eq!(
        first_order
            .compile_debug("future eats(Agent, Meal).")
            .unwrap(),
        opposite_order
            .compile_debug("future eats(Agent, Meal).")
            .unwrap(),
        "HashSet insertion order must not affect compiled IR"
    );
}

#[test]
fn arbitrary_compute_names_are_native_raw_ir_only_and_remain_query_only() {
    let engine = fresh_engine();
    engine.set_compute_dispatch(stub_text_raw_contract_eval, stub_text_raw_contract_batch);
    let raw = EngineLogicBuffer {
        nodes: vec![EngineLogicNode::ComputeNode((
            "external_probe".to_string(),
            vec![EngineLogicalTerm::Constant("Sample".to_string())],
        ))],
        roots: vec![0],
    };

    assert_true(
        &engine.kb().query_entailment(raw.clone()).unwrap(),
        "an explicit raw ComputeNode supplies its own name and arity and dispatches natively",
    );

    let validation_error = engine
        .kb()
        .validate_assertion(&raw)
        .expect_err("raw compute IR is still query-only at assertion preflight");
    assert!(validation_error.to_string().contains("query-only"));
    let assertion_error = engine
        .kb()
        .assert_fact(raw, "raw compute assertion".to_string())
        .expect_err("raw compute IR must not persist as a fact");
    assert!(assertion_error.to_string().contains("query-only"));
    assert!(engine.list_facts().unwrap().is_empty());
    assert_eq!(engine.kb().next_fact_id().unwrap(), 0);
}

#[test]
fn per_instance_compute_dispatch_is_isolated() {
    // engine_a registers a per-instance dispatch → external `tenfa` resolves TRUE.
    let mut engine_a = fresh_engine();
    engine_a
        .register_compute_predicate("exponential".to_string())
        .expect("fresh-name registration must succeed");
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
    engine_b
        .register_compute_predicate("exponential".to_string())
        .expect("fresh-name registration must succeed");
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
    engine
        .register_compute_predicate("exponential".to_string())
        .expect("fresh-name registration must succeed");
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
    engine
        .register_compute_predicate("exponential".to_string())
        .expect("fresh-name registration must succeed");
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
        engine
            .register_compute_predicate("exponential".to_string())
            .expect("fresh-name registration must succeed");
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
fn executable_compute_is_query_only_in_facts_and_rules() {
    let mut engine = fresh_engine();
    engine
        .register_compute_predicate("exponential".to_string())
        .expect("fresh-name registration must succeed");

    for statement in [
        "sum(5, 2, 3).",
        "all $x: big($x) & sum($x, 2, 3) -> animal($x).",
        "all $x: big($x) & ~sum($x, 2, 3) -> animal($x).",
        "all $x: big($x) -> sum($x, 2, 3).",
        "exponential(8, 2, 3).",
    ] {
        let err = engine
            .assert_text(statement)
            .expect_err("executable compute must be rejected at assertion ingress");
        assert!(
            err.to_string().contains("query-only"),
            "expected query-only rejection for `{statement}`, got: {err}"
        );
        assert!(
            engine.list_facts().unwrap().is_empty(),
            "rejected compute assertion mutated the registry: `{statement}`"
        );
    }

    let direct_err = engine
        .assert_fact_direct(
            "product".to_string(),
            vec![
                nibli_engine::EngineLogicalTerm::Number(6.0),
                nibli_engine::EngineLogicalTerm::Number(2.0),
                nibli_engine::EngineLogicalTerm::Number(3.0),
            ],
        )
        .expect_err("direct injection must share the compute assertion guard");
    assert!(
        direct_err.to_string().contains("query-only"),
        "{direct_err}"
    );
    assert!(engine.list_facts().unwrap().is_empty());

    assert_eq!(
        engine.assert_text("big(5).").unwrap(),
        vec![0],
        "rejected compute assertions must not consume an id"
    );
    assert_true(
        &engine.query_holds("sum(5, 2, 3).").unwrap(),
        "the same compute formula remains valid on the query surface",
    );

    // The reference name gets the SPECIFIC name-guard message even here, in a
    // registered session — the name guard runs before the ComputeNode guard.
    let named_err = engine
        .assert_text("exponential(8, 2, 3).")
        .expect_err("the reference name stays refused");
    assert!(
        named_err
            .to_string()
            .contains("reserved for EXTERNAL COMPUTE"),
        "{named_err}"
    );
}

// ─── Registration-order closure (TODO exit: pinned in BOTH orders) ──────────

/// The static half: a reference external-compute name is query-only with NO
/// registration at all — the exact pre-fix hole (assert → ordinary stored fact
/// → TRUE from the store → unreachable after registration). Registration of
/// the name afterwards is vacuously never blocked.
#[test]
fn an_external_compute_name_is_query_only_even_before_registration() {
    let mut engine = fresh_engine();
    let err = engine
        .assert_text("exponential(2, 3, 8).")
        .expect_err("an UNREGISTERED reference compute name must be refused at ingress");
    assert!(
        err.to_string().contains("reserved for EXTERNAL COMPUTE"),
        "{err}"
    );
    assert!(engine.list_facts().unwrap().is_empty());
    assert_false(
        &engine.query_holds("exponential(2, 3, 8).").unwrap(),
        "unregistered: the necessarily-empty stored extension is closed-world FALSE",
    );

    engine
        .register_compute_predicate("exponential".to_string())
        .expect("a reference name can never have live references, so registration succeeds");
    let r = engine.query_holds("exponential(2, 3, 8).").unwrap();
    assert!(
        !r.is_true() && !r.is_false(),
        "registered with no backend: dispatch surfaces backend-unavailable, never a \
         store answer: {r:?}"
    );
}

/// The registration half, in the assert-then-register order: live stored
/// statements (a fact AND a rule) block registration with their ids; after
/// retracting both, registration succeeds, the name flips to query-only, and
/// no fact id was burned along the way.
#[test]
fn assert_then_register_is_refused_until_the_statements_are_retracted() {
    let mut engine = fresh_engine();
    let fact_id = engine.assert_text("eats(Bela, Cheese).").unwrap()[0];
    let rule_id = engine
        .assert_text("all $x: eats($x, Cheese) -> animal($x).")
        .unwrap()[0];

    let err = engine
        .register_compute_predicate("eats".to_string())
        .expect_err("live references must block registration");
    let message = err.to_string();
    assert!(message.contains("cannot register"), "{message}");
    assert!(
        message.contains(&format!("#{fact_id}")) && message.contains(&format!("#{rule_id}")),
        "the refusal must name both blocking ids: {message}"
    );

    engine.retract_fact(fact_id).unwrap();
    engine
        .register_compute_predicate("eats".to_string())
        .expect_err("the rule alone must still block registration");
    engine.retract_fact(rule_id).unwrap();
    engine
        .register_compute_predicate("eats".to_string())
        .expect("with no live references left, registration succeeds");

    let err = engine
        .assert_text("eats(Bela, Cheese).")
        .expect_err("register-then-assert is closed by the ComputeNode guard");
    assert!(err.to_string().contains("query-only"), "{err}");

    assert_eq!(
        engine.assert_text("big(5).").unwrap(),
        vec![fact_id.max(rule_id) + 1],
        "refused registrations and refused asserts must not consume ids"
    );
}

/// A legacy DB row holding a pre-fix unregistered `exponential` fact (the
/// permanently-unmarked ordinary spelling) fails replay non-destructively —
/// the count-row precedent. Silently replaying it would preserve the
/// unreachable-fact divergence this contract closes.
#[test]
fn legacy_persisted_external_compute_row_fails_replay_without_deleting_the_row() {
    let path = temp_db_path("legacy_external_compute_assertion");
    cleanup(&path);

    // The legacy stored shape: compiled WITHOUT registration, so the anchor is
    // an ordinary Predicate — `compile_debug` never marks what the session has
    // not registered.
    let compiler = fresh_engine();
    let legacy = compiler
        .compile_debug("exponential(2, 3, 8).")
        .expect("the query surface must still compile the unregistered spelling");
    let payload = postcard::to_allocvec(&legacy).expect("fixture should serialize");
    {
        let mut store = NibliStore::open(&path, "local".into()).expect("store should open");
        store
            .insert_fact(7, "legacy external compute".into(), payload)
            .expect("legacy fixture should persist");
    }

    let error = match NibliEngine::open(&path) {
        Ok(_) => panic!("a legacy external-compute row must not replay as an ordinary fact"),
        Err(error) => error,
    };
    assert!(
        error.contains("Replay error (fact 7)") && error.contains("reserved for EXTERNAL COMPUTE"),
        "replay failure must identify the row and the name-guard contract: {error}"
    );
    {
        let store = NibliStore::open(&path, "local".into()).expect("store should reopen");
        assert!(
            store.get_fact(7).unwrap().is_some(),
            "failed replay is non-destructive; the operator must repair/re-import explicitly"
        );
    }

    cleanup(&path);
}

/// The registration scan reads registry state rebuilt from disk: ordinary
/// facts persisted in one session block registration after reopen.
#[test]
fn persisted_ordinary_facts_block_registration_after_reopen() {
    let path = temp_db_path("persisted_facts_block_registration");
    cleanup(&path);

    let fact_id = {
        let engine = NibliEngine::open(&path).expect("fresh persistent engine");
        engine.assert_text("eats(Bela, Cheese).").unwrap()[0]
    };

    let mut engine = fresh_open(&path, "reopen must replay the persisted fact");
    let err = engine
        .register_compute_predicate("eats".to_string())
        .expect_err("the disk-replayed fact must block registration");
    assert!(
        err.to_string().contains(&format!("#{fact_id}")),
        "the refusal must name the replayed id: {err}"
    );
    engine.retract_fact(fact_id).unwrap();
    engine
        .register_compute_predicate("eats".to_string())
        .expect("after retracting the replayed fact, registration succeeds");

    cleanup(&path);
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
    engine.reset().unwrap();
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

/// The deep-chain cliff recovery pin (the nibli-reason depth-cut table),
/// surface-driven: an 8-hop `every`-rule chain query completes TRUE well
/// within a 10 s watchdog (the ch12 pattern — a complexity regression fails
/// on timeout instead of hanging the suite). Pre-table, a release 6-hop
/// chain measured ~47 s; 8 hops did not complete.
#[test]
fn deep_chain_query_completes_within_watchdog() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let engine = nibli_engine::NibliEngine::new();
        engine.assert_text("dog(Adam).").unwrap();
        let chain = [
            "dog", "animal", "alive", "big", "fast", "healthy", "thin", "eats", "goes",
        ];
        for w in chain.windows(2) {
            engine
                .assert_text(&format!("{}(every {}).", w[1], w[0]))
                .unwrap();
        }
        let result = engine.query_holds("goes(Adam).").unwrap();
        tx.send(result.is_true()).unwrap();
    });
    let is_true = rx
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("deep-chain query exceeded the 10 s watchdog (cliff regression)");
    assert!(is_true, "the 8-hop chain must derive TRUE");
}

// ════════════════════════════════════════════════════════════════════
// Closed base vocabulary — `admits("<rel>")`, the dual of `derived_only`
//
// `derived_only` says which relations may NOT be asserted; it says nothing about
// which may, so any corpus name at all still entered a knowledge base fail-open.
// A document claiming "the record has exactly these entries, and a further one
// cannot be written" was therefore claiming something the engine did not check.
// `admits` names the base vocabulary and refuses the rest at assert time.
// ════════════════════════════════════════════════════════════════════

/// A KB that declared nothing stays OPEN — the closure is opt-in, and its absence
/// must be silent or every existing knowledge base breaks.
#[test]
fn an_undeclared_kb_admits_everything() {
    let engine = engine_with_facts(&["person(Adam).", "rich(Adam).", "banana(Adam)."]);
    assert!(!engine.kb().vocabulary_is_closed());
    assert!(engine.kb().admitted_relations().is_empty());
    assert_true(
        &engine.query_holds("rich(Adam).").unwrap(),
        "open KB asserts",
    );
}

/// The first declaration closes it; everything outside is refused atomically.
#[test]
fn admits_closes_the_vocabulary_fail_closed() {
    let engine = engine_with_facts(&["admits(\"person\").", "person(Adam)."]);
    assert!(engine.kb().vocabulary_is_closed());
    assert_eq!(engine.kb().admitted_relations(), vec!["person".to_string()]);

    let err = engine
        .assert_text("rich(Adam).")
        .expect_err("an unadmitted relation must be refused");
    let msg = format!("{err}");
    assert!(
        msg.contains("not admitted vocabulary") && msg.contains("rich"),
        "message must name the relation and the reason: {msg}"
    );
    // ATOMIC: the rejected assertion left nothing behind.
    assert_false(
        &engine.query_holds("rich(Adam).").unwrap(),
        "a refused assertion must not half-land",
    );
}

/// THE CONVERTED DUTY ALIAS, in the shapes the corpora used to carry.
///
/// `obligated_by` swaps its first two places, so `obligated_by(P, event { … })`
/// compiles to `obliged(x1 = <event referent>, x2 = P)` — the event lands in place 1.
/// That is a structurally DIFFERENT decomposition from the plain spelling, and it
/// exercises a different set of paths: the swap in `apply_predicate`'s place routing,
/// the deontic/tense arms of `collect_mandatory_anchors`, the role-anchor matching in
/// `anchor_other_arguments_match`, and the rule-head event minting that
/// `relation_rule_heads_mint_events` gates.
///
/// Until 2026-08-17 that shape was covered INCIDENTALLY, because every duty in the
/// GDPR and utopia corpora was written with this alias. Those corpora moved to the
/// plain `obliged` spelling (the places put the bound party on x1, which is what the
/// renderer must be able to trust), and the coverage went with them — caught by the
/// mutation gate, which lost nine kills. The alias is still shipped and still
/// supported, so the coverage is restored HERE, explicitly and by name, rather than
/// depending on which spelling a corpus happens to prefer.
#[test]
fn the_converted_duty_alias_compiles_and_reasons_in_every_corpus_shape() {
    let engine = engine_with_facts(&[
        "person(Ruk).",
        "person(Adam).",
        "data governs(Akmes).",
        "flaw(Akmes).",
        "approves(Adam).",
        // Plain relational form: the swap must invert the stored places.
        "obligated_by(Bel, Ruk).",
        // Deontic abstraction over a bare universal.
        "obligated_by(every person, event { eats() }).",
        // Restricted universal with a compound restrictor.
        "obligated_by(every data governs where flaw, event { message() }).",
        // Negated restrictor — the Article 17 erasure shape.
        "obligated_by(every person where ~approves, event { removes() }).",
        // Arity 1.
        "obligated_by(every rule).",
    ]);

    // The converse holds: `obligated_by(Bel, Ruk)` IS `obliged(Ruk, Bel)`.
    assert_true(
        &engine.query_holds("obligated_by(Bel, Ruk).").unwrap(),
        "the alias must still assert and answer",
    );
    assert_true(
        &engine.query_holds("obliged(Ruk, Bel).").unwrap(),
        "the same fact under the base spelling, arguments exchanged",
    );
    assert_false(
        &engine.query_holds("obliged(Bel, Ruk).").unwrap(),
        "the alias must still INVERT, not read as the same argument order",
    );

    // The deontic form derives for every person, through the swapped shape.
    assert_true(
        &engine
            .query_holds("obligated_by(Ruk, event { eats() }).")
            .unwrap(),
        "the bare deontic universal must reach every person",
    );
    assert_true(
        &engine
            .query_holds("obligated_by(Adam, event { eats() }).")
            .unwrap(),
        "and not only the first one",
    );

    // The restricted and negated-restrictor universals both fire.
    assert_true(
        &engine
            .query_holds("obligated_by(Akmes, event { message() }).")
            .unwrap(),
        "the compound restrictor `every data governs where flaw` must match Akmes",
    );
    assert_false(
        &engine
            .query_holds("obligated_by(Adam, event { removes() }).")
            .unwrap(),
        "Adam approves, so the negated-restrictor erasure duty must NOT attach",
    );
    assert_true(
        &engine
            .query_holds("obligated_by(Ruk, event { removes() }).")
            .unwrap(),
        "Ruk does not approve, so the erasure duty does attach",
    );
}

/// The two meta-declarations do not count as "ordinary assertions".
///
/// The ordering rule is that the vocabulary must close before any ordinary fact
/// lands; `derived_only` and `admits` rows are themselves declarations, so a file that
/// opens with one and then closes its vocabulary is correctly ordered. Counting them
/// would make the two declaration forms mutually exclusive in the same KB.
#[test]
fn a_prior_declaration_does_not_block_a_later_admits_block() {
    let engine = engine_with_facts(&["derived_only(\"prisoner\")."]);
    engine
        .assert_text("admits(\"person\").")
        .expect("a declaration above the admits block is not an ordinary assertion");
    assert!(engine.kb().vocabulary_is_closed());
}

/// The late-declaration refusal must name a DETERMINISTIC relation, and the store
/// iterates a `HashSet` — so "whichever came first" is a different predicate run to
/// run. `first_non_declaration_relation` takes the minimum for exactly that reason.
///
/// The existing late-declaration tests assert with a SINGLE ordinary fact loaded,
/// where minimum, maximum and first-found all coincide; this one loads several out of
/// alphabetical order, so only the documented choice passes.
#[test]
fn a_late_admits_names_the_alphabetically_first_offender() {
    let engine = engine_with_facts(&[
        "teaches(Ara, Bel).",
        "person(Ara).",
        "judge(Ara, Bel).",
        "reward(Ara).",
    ]);
    let err = engine
        .assert_text("admits(\"person\").")
        .expect_err("an admits block below the facts it would grandfather must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("comes too late"),
        "the refusal must explain the ordering rule: {msg}"
    );
    assert!(
        msg.contains("judge"),
        "the offender named must be the alphabetically first stored relation \
         (judge < person < reward < teaches), not whichever the HashSet yielded: {msg}"
    );
}

/// The closure is EXTENSIONAL only — a rule may still conclude outside the set,
/// exactly as `derived_only` permits derivation while refusing assertion.
#[test]
fn a_closed_vocabulary_still_derives_outside_itself() {
    let engine = engine_with_facts(&[
        "admits(\"person\").",
        "person(Adam).",
        "all $x: person($x) -> prisoner($x).",
    ]);
    assert_true(
        &engine.query_holds("prisoner(Adam).").unwrap(),
        "closing the base vocabulary must not close the derived one",
    );
    assert!(engine.assert_text("prisoner(Bela).").is_err());
}

/// ORDER IS LOAD-BEARING, and enforced. An `admits` below the facts would silently
/// grandfather them — the mirror of `derived_only`'s "comes too late".
#[test]
fn an_admits_block_below_the_facts_is_refused() {
    let engine = engine_with_facts(&["person(Adam)."]);
    let err = engine
        .assert_text("admits(\"person\").")
        .expect_err("a late declaration must be refused, not silently honoured");
    assert!(
        format!("{err}").contains("comes too late"),
        "must say why: {err}"
    );
    assert!(
        !engine.kb().vocabulary_is_closed(),
        "the refusal is atomic — the vocabulary must NOT have closed"
    );
}

/// A RETRACTION replay must not re-open the vocabulary. `rebuild_inner` clears the
/// fact store and replays; `admitted` is deliberately absent from its clear list,
/// for the same reason `derived_only` is.
#[test]
fn retraction_replay_does_not_reopen_the_vocabulary() {
    let engine = engine_with_facts(&["admits(\"person\").", "person(Adam).", "person(Bela)."]);
    let ids = engine.assert_text("person(Cira).").unwrap();
    engine.retract_fact(ids[0]).expect("retract");
    assert!(
        engine.kb().vocabulary_is_closed(),
        "a retraction must not re-open a closed vocabulary"
    );
    assert!(
        engine.assert_text("rich(Adam).").is_err(),
        "and the closure must still refuse after replay"
    );
}

/// `reset()` wipes the KB, so it wipes the declaration too — it is KB CONTENT,
/// not session configuration like `strict`/`existential_import`.
#[test]
fn reset_reopens_the_vocabulary() {
    let engine = engine_with_facts(&["admits(\"person\").", "person(Adam)."]);
    assert!(engine.kb().vocabulary_is_closed());
    engine.reset().unwrap();
    assert!(!engine.kb().vocabulary_is_closed());
    assert!(engine.assert_text("rich(Adam).").is_ok());
}

// ─── Proof envelope: verdict + trace + profile + version, BOUND ──────────

/// The live certification matrix: every constructible verdict class binds into
/// a coherent envelope (independent validator green), JSON round-trips to the
/// identity, and the profile/version stamps are real.
#[test]
fn certify_binds_verdict_trace_profile_and_version_across_the_matrix() {
    use nibli_engine::{
        EngineProofEnvelope, EngineResourceKind, PROOF_ENVELOPE_SCHEMA, validate_envelope,
    };

    fn check(env: &EngineProofEnvelope, expect: &EngineQueryResult) {
        assert_eq!(env.schema, PROOF_ENVELOPE_SCHEMA);
        assert_eq!(
            env.engine_version,
            env!("CARGO_PKG_VERSION"),
            "the envelope must stamp the lockstep workspace version"
        );
        assert_eq!(
            &env.result, expect,
            "bound verdict must match ({})",
            env.query
        );
        validate_envelope(env)
            .unwrap_or_else(|errs| panic!("{}: validator rejected: {errs:?}", env.query));
        let json = nibli_protocol::envelope_to_json(env);
        assert_eq!(
            nibli_protocol::envelope_from_json(&json).as_ref(),
            Some(env),
            "JSON round trip must be the identity"
        );
    }

    let mut engine = fresh_engine();
    engine.assert_text("animal(every dog).").unwrap();
    engine.assert_text("dog(Rex).").unwrap();
    engine.assert_text("dog(Rex).").unwrap(); // duplicate assertion, separately citable
    engine.assert_text("Kim = Rex.").unwrap();

    // TRUE via rule derivation + equality substitution over duplicates.
    let env = engine.certify_text("animal(Kim).").unwrap();
    check(&env, &EngineQueryResult::True);
    assert!(!env.profile.existential_import);
    assert!(env.profile.materialization);

    // NAF TRUE: the naf_dependent flag rides the envelope and the validator
    // re-derives it.
    let env = engine.certify_text("~cat(Rex).").unwrap();
    check(&env, &EngineQueryResult::True);
    assert!(env.trace.naf_dependent, "NAF truth must be flagged");

    // Ordinary closed-world FALSE.
    let env = engine.certify_text("cat(Rex).").unwrap();
    check(&env, &EngineQueryResult::False);
    assert!(env.trace.cwa_false, "missing-fact FALSE is closed-world");

    // Arithmetic FALSE: a computed DECISION (cwa_false stays off) whose
    // proof-local compute evidence is in the trace.
    let env = engine.certify_text("num_equal(5, 3).").unwrap();
    check(&env, &EngineQueryResult::False);
    assert!(!env.trace.cwa_false, "computed FALSE is not closed-world");
    assert!(
        env.trace.steps.iter().any(|s| matches!(
            &s.rule,
            nibli_types::logic::ProofRule::ComputeCheck { .. }
        ) && !s.holds),
        "the failing compute check must ride the certificate"
    );

    // UNKNOWN (backend-unavailable): registered external compute, no backend.
    engine
        .register_compute_predicate("exponential".to_string())
        .unwrap();
    let env = engine.certify_text("exponential(2, 3, 8).").unwrap();
    check(
        &env,
        &EngineQueryResult::Unknown(EngineUnknownReason::BackendUnavailable),
    );

    // RESOURCE_EXCEEDED (depth): a chain past the bound, with materialisation
    // off so its completeness gain does not decide it first.
    let deep = fresh_engine();
    deep.set_materialization(false);
    for rule in [
        "cat(every dog).",
        "animal(every cat).",
        "alive(every animal).",
        "beautiful(every alive).",
        "awake(every beautiful).",
        "dark(every awake).",
        "sleep(every dark).",
        "person(every sleep).",
        "eats(every person).",
        "runs(every eats).",
        "walks(every runs).",
        "talks(every walks).",
    ] {
        deep.assert_text(rule).unwrap();
    }
    deep.assert_text("dog(Rex).").unwrap();
    let env = deep.certify_text("talks(Rex).").unwrap();
    check(
        &env,
        &EngineQueryResult::ResourceExceeded(EngineResourceKind::Depth),
    );

    // The profile stamp is live, not a constant: flip strict + import.
    let flipped = fresh_engine();
    flipped.set_strict(true);
    flipped.set_existential_import(true).unwrap();
    flipped.assert_text("dog(Rex).").unwrap();
    let env = flipped.certify_text("dog(Rex).").unwrap();
    check(&env, &EngineQueryResult::True);
    assert!(env.profile.strict && env.profile.existential_import);
}
