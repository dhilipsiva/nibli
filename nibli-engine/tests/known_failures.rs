//! Known-failure backlog — surface-reachable defects from the 2026-06-10 deep
//! code-review panel (see `todo.md` → "Deep code-review panel findings" and
//! `code-review-panel-2026-06-10.json`).
//!
//! Each test below encodes the DESIRED (post-fix) behavior, so it FAILS today
//! (the bug reproduces) and will PASS once the corresponding `todo.md` item is
//! fixed. Every test is `#[ignore]`d so the normal suite stays green; this file
//! is the red backlog you opt into.
//!
//! Run the backlog (expect failures — that's the point):
//!   cargo test -p nibli-engine --test known_failures -- --ignored --test-threads=1
//!
//! Workflow: when you fix an item, delete its `#[ignore]` line so the test joins
//! the normal regression suite. A test here going GREEN while still `#[ignore]`d
//! means either the bug was fixed elsewhere (promote it) or the pin is mis-encoded
//! (fix the pin) — never leave a green ignored test.
//!
//! Scope: these are reproducible through the engine's public surface
//! (`assert_text`/`query_holds`/`check_contradictions`) and are NON-FATAL (they
//! return a wrong answer or silently drop input; none crash the process).
//! Process-aborting bugs (du-equivalence stack overflow) and raw-FOL-only bugs
//! (the `best_result` ResourceExceeded wipe) live in separate files so a crash
//! cannot take the rest of the backlog down with it.

use nibli_engine::{EngineLogicalTerm, NibliEngine};

// ─── Fail-open rule compilation (todo.md: HIGH) ─────────────────────────────
// `build_rule_template_fact`'s `_ => None` catch-all silently drops antecedent
// atoms it cannot represent (tense wrappers, disjunctions, ...), and the rule is
// registered anyway — possibly with zero conditions, so it fires unconditionally.

#[test] // FIXED (fail-closed rule compilation): promoted from the backlog to a live guard.
fn ganai_tensed_antecedent_must_not_fire_unconditionally() {
    let engine = NibliEngine::new();
    // "if Adam ran (past), then Adam is an animal" — on an empty KB, Adam never ran.
    // Fail-closed (reject the unrepresentable rule) and fail-open-fixed (represent the
    // tensed condition and don't fire) are both acceptable; the invariant is that
    // danlu(adam) is NOT derivable from an empty KB.
    if engine
        .assert_text("ganai la .adam. pu bajra gi la .adam. danlu")
        .is_ok()
    {
        let r = engine.query_holds("la .adam. cu danlu").unwrap();
        assert!(
            !r.is_true(),
            "tensed antecedent was dropped → rule fired with no supporting fact: {r:?}"
        );
    }
}

#[test] // FIXED (fail-closed rule compilation): promoted from the backlog to a live guard.
fn ganai_disjunctive_antecedent_must_not_fire_unconditionally() {
    let engine = NibliEngine::new();
    // "if (Adam is a dog OR Adam is a cat) then Adam is an animal" — neither disjunct holds.
    // Reject-or-represent (see the tensed-antecedent test); the invariant is that
    // danlu(adam) is NOT derivable from an empty KB.
    if engine
        .assert_text("ganai ga la .adam. gerku gi la .adam. mlatu gi la .adam. danlu")
        .is_ok()
    {
        let r = engine.query_holds("la .adam. cu danlu").unwrap();
        assert!(
            !r.is_true(),
            "disjunctive antecedent was dropped → rule fired with no supporting fact: {r:?}"
        );
    }
}

// ─── Zero-ingest assertions (todo.md: HIGH) ─────────────────────────────────
// Some shapes compile and are accepted but ingest zero facts and zero rules,
// while `assert_text` still returns Ok(id). Invariant under test: a successful
// assert must be observable — either the engine rejects what it cannot represent,
// or the asserted statement queries back true.

#[test] // FIXED (zero-ingest guard): bare disjunction is now rejected. Live guard.
fn disjunction_assert_must_be_observable() {
    let engine = NibliEngine::new();
    let s = "la .adam. cu gerku .i ja la .adam. cu mlatu";
    if engine.assert_text(s).is_ok() {
        let r = engine.query_holds(s).unwrap();
        assert!(
            r.is_true(),
            "disjunction asserted Ok but queries back non-true (nothing was ingested): {r:?}"
        );
    }
    // (A fail-closed fix that makes assert_text return Err is also acceptable: the
    //  `if` is then skipped and the test passes.)
}

#[test] // FIXED (zero-ingest guard): xor (flattened to And(Or, Not(And))) is now rejected. Live guard.
fn xor_assert_must_be_observable() {
    let engine = NibliEngine::new();
    let s = "la .adam. cu gerku .i ju la .adam. cu mlatu";
    if engine.assert_text(s).is_ok() {
        let r = engine.query_holds(s).unwrap();
        assert!(
            r.is_true(),
            "xor asserted Ok but queries back non-true (nothing was ingested): {r:?}"
        );
    }
}

#[test] // FIXED (negative-fact registry + event-normalized contradiction detection): promoted.
fn negated_ground_fact_then_contrary_positive_is_a_contradiction() {
    let engine = NibliEngine::new();
    // "Adam is NOT a dog."
    let neg = engine.assert_text("la .adam. na gerku");
    // Rejecting the negation outright is an acceptable fail-closed fix; otherwise
    // it must be recorded and contradict a later "Adam is a dog".
    if neg.is_ok() {
        engine.assert_text("la .adam. cu gerku").unwrap();
        assert!(
            !engine.check_contradictions().is_empty(),
            "negative fact was a silent no-op; the contradiction was not detected"
        );
    }
}

// ─── smuni silently discards meaning (todo.md: HIGH) ────────────────────────

#[test] // FIXED (rel clause on name conjoined into matrix): promoted to a live guard.
fn rel_clause_on_name_must_not_be_dropped() {
    let engine = NibliEngine::new();
    engine.assert_text("la .adam. cu klama").unwrap(); // only known fact: Adam goes
    // "Adam, who is a dog, goes." We do NOT know Adam is a dog, so this must not hold.
    let r = engine.query_holds("la .adam. poi gerku cu klama").unwrap();
    assert!(
        !r.is_true(),
        "the `poi gerku` clause was dropped → unsound TRUE for an unproven restriction: {r:?}"
    );
}

#[test] // Positive companion to the guard above: when BOTH conjuncts are known, the
// restricted query holds, and asserting the restricted sentence asserts both conjuncts.
fn rel_clause_on_name_positive_direction() {
    let engine = NibliEngine::new();
    engine.assert_text("la .adam. cu gerku").unwrap();
    engine.assert_text("la .adam. cu klama").unwrap();
    let r = engine.query_holds("la .adam. poi gerku cu klama").unwrap();
    assert!(
        r.is_true(),
        "both conjuncts known → restricted query must hold: {r:?}"
    );

    // Asserting the restricted sentence must assert BOTH conjuncts.
    let engine2 = NibliEngine::new();
    engine2.assert_text("la .adam. poi gerku cu klama").unwrap();
    let g = engine2.query_holds("la .adam. cu gerku").unwrap();
    let k = engine2.query_holds("la .adam. cu klama").unwrap();
    assert!(
        g.is_true() && k.is_true(),
        "asserting the restricted sentence must assert both conjuncts: gerku={g:?}, klama={k:?}"
    );
}

#[test] // FIXED (FA-overflow fails closed with a semantic error): promoted to a live guard.
fn fa_tag_beyond_arity_must_error_not_silently_drop() {
    let engine = NibliEngine::new();
    // `fu` tags place x5; `gerku` is 2-place, so the x5 term `do` cannot be placed.
    let r = engine.assert_text("fu do gerku");
    assert!(
        r.is_err(),
        "over-arity FA tag silently dropped the bound term instead of reporting an error"
    );
}

#[test] // FIXED (tanru decomposition emits Unspecified roles; firewall counts per shared event): promoted.
fn tanru_in_poi_must_not_be_falsely_rejected() {
    let engine = NibliEngine::new();
    // "a dog that runs fast goes" — valid Lojban; `sutra bajra` is a tanru inside the poi clause.
    assert!(
        engine
            .assert_text("lo gerku poi sutra bajra cu klama")
            .is_ok(),
        "a valid tanru-in-poi relative clause was rejected by the ambiguity firewall"
    );
}

// ─── gerna lexer truncation (todo.md: HIGH) ─────────────────────────────────

#[test] // FIXED (lexer error channel: unlexable runs surface as positioned parse errors): promoted.
fn lexer_must_not_silently_truncate_input() {
    let engine = NibliEngine::new();
    // The bare `7` is unlexable mid-sentence; the trailing sentence must not vanish silently.
    let s = "mi klama 7 do prami .i lo gerku cu danlu";
    if engine.assert_text(s).is_ok() {
        // If accepted at all, the trailing assertion must have reached the KB.
        let r = engine.query_holds("lo gerku cu danlu").unwrap();
        assert!(
            r.is_true(),
            "input was silently truncated at `7`; the trailing sentence never reached the KB: {r:?}"
        );
    }
    // (A parse error from assert_text is the preferred fix and passes this test.)
}

// ─── Quantifier-closure scoping (todo.md: HIGH) ─────────────────────────────

#[test] // FIXED (da/de/di existentials close INSIDE universal closure — ∀x.∃y scope): promoted.
fn da_after_universal_description_must_not_lose_the_rule() {
    let engine = NibliEngine::new();
    engine.assert_text("ro lo gerku cu citka da").unwrap(); // every dog eats something
    engine.assert_text("la .alis. cu gerku").unwrap(); // Alice is a dog
    // Therefore Alice eats something.
    let r = engine.query_holds("la .alis. cu citka da").unwrap();
    assert!(
        r.is_true(),
        "the `ro lo ... da` rule was silently dropped (∃ closed outside ∀): {r:?}"
    );
}

// ─── gerna flattener wrong body indices (todo.md: HIGH) ─────────────────────
// The Abstraction (lib.rs:244) and Restricted (lib.rs:320) arms snapshot
// `sentences.len()` BEFORE recursing and discard push_sentence's return value
// (the Connected arm at lib.rs:146-147 does it right). When the body itself
// pushes a nested sentence, body_idx points at the WRONG (nested) sentence — and
// it is always in-range, so smuni miscompiles silently. We pin via compile_debug:
// the abstraction's body predicate must actually appear in the compiled FOL.

#[test] // FIXED (flattener uses push_sentence's return value for body indices): promoted.
fn abstraction_body_over_connected_must_reference_real_body() {
    let engine = NibliEngine::new();
    // The `lo nu ...` abstraction body is `ganai la .adam. gerku gi la .adam. klama`.
    // Its compiled form must contain BOTH the antecedent (gerku) and the
    // consequent (klama). Today the flattener binds the abstraction to the
    // antecedent bridi alone, so `klama` is dropped entirely.
    let debug = engine
        .compile_debug("mi djica lo nu ganai la .adam. gerku gi la .adam. klama kei")
        .expect("should compile");
    assert!(
        debug.contains("klama"),
        "the abstraction body's consequent `klama` was dropped — flattener bound \
         the wrong (antecedent) sentence index. FOL:\n{debug}"
    );
}

#[test] // FIXED (flattener uses push_sentence's return value for body indices): promoted.
fn abstraction_body_over_rel_clause_must_reference_real_body() {
    let engine = NibliEngine::new();
    // Abstraction body is `lo gerku poi ke'a barda cu klama`; the head predicate
    // is `klama`. The flattener instead binds the abstraction to the `barda`
    // rel-clause bridi, so `klama` is dropped from the compiled FOL.
    let debug = engine
        .compile_debug("mi djica lo nu lo gerku poi ke'a barda cu klama kei")
        .expect("should compile");
    assert!(
        debug.contains("klama"),
        "the abstraction body head `klama` was dropped — flattener bound the \
         rel-clause (`barda`) sentence index instead. FOL:\n{debug}"
    );
}

// ─── Retraction conflates duplicate ground facts (todo.md: HIGH) ────────────
// The HashSet fact store tracks no multiplicity, and incremental retraction does
// not consult other live records, so retracting one of two records asserting the
// SAME ground fact removes the fact entirely — even though a second active record
// still asserts it. Reachable via the direct fact-injection API (`:assert` /
// assert-fact). The fact must still hold after retracting one of its two records.

#[test] // FIXED (multiplicity-aware incremental retraction): promoted to a live guard.
// PIN RE-ENCODED during promotion: the original pin queried via TEXT
// (`query_holds("la .adam. cu gerku")`), but text queries are event-decomposed
// (∃e. gerku(e) ∧ gerku_x1(e, adam) …) and structurally NEVER match a flat
// direct-injected fact — the pin failed even with both records live, masking the
// actual retraction bug behind a query-shape mismatch. We therefore verify
// through the raw FOL contract (`engine.kb().query_entailment` with a flat
// query buffer), which is exactly the shape `assert_fact_direct` stores. The
// flat-injection-vs-text-query mismatch is filed separately in todo.md.
fn duplicate_ground_fact_survives_retracting_one_copy() {
    let flat_gerku_adam = || nibli_types::logic::LogicBuffer {
        nodes: vec![nibli_types::logic::LogicNode::Predicate((
            "gerku".to_string(),
            vec![nibli_types::logic::LogicalTerm::Constant(
                "adam".to_string(),
            )],
        ))],
        roots: vec![0],
    };

    let engine = NibliEngine::new();
    let id1 = engine
        .assert_fact_direct(
            "gerku".to_string(),
            vec![EngineLogicalTerm::Constant("adam".to_string())],
        )
        .unwrap();
    let _id2 = engine
        .assert_fact_direct(
            "gerku".to_string(),
            vec![EngineLogicalTerm::Constant("adam".to_string())],
        )
        .unwrap();
    // Sanity: the flat fact is queryable through the FOL contract while both live.
    let before = engine.kb().query_entailment(flat_gerku_adam()).unwrap();
    assert!(
        before.is_true(),
        "sanity: flat direct-injected fact must be queryable via the FOL contract: {before:?}"
    );
    // Retract only the FIRST record; the second still asserts gerku(adam).
    engine.retract_fact(id1).unwrap();
    let r = engine.kb().query_entailment(flat_gerku_adam()).unwrap();
    assert!(
        r.is_true(),
        "a live record still asserts gerku(adam), but retracting the duplicate \
         removed the fact entirely (HashSet store has no multiplicity): {r:?}"
    );
}
