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

use nibli_engine::{EngineLogicBuffer, EngineLogicNode, NibliEngine};

/// A fresh KR-mode engine (backlog machine-ported from Lojban at THE DROP).
fn fresh_engine() -> NibliEngine {
    NibliEngine::new()
}

/// True if the compiled `LogicBuffer` contains the `base` predicate or any of its
/// Neo-Davidsonian role predicates (`base_xN`). `compile_debug` returns the typed
/// IR, so we walk nodes instead of substring-matching an S-expr string.
fn has_predicate_base(buf: &EngineLogicBuffer, base: &str) -> bool {
    let role_prefix = format!("{base}_x");
    buf.nodes.iter().any(|n| match n {
        EngineLogicNode::Predicate((rel, _)) => rel == base || rel.starts_with(&role_prefix),
        _ => false,
    })
}

// ─── Fail-open rule compilation (todo.md: HIGH) ─────────────────────────────
// `build_rule_template_fact`'s `_ => None` catch-all silently drops antecedent
// atoms it cannot represent (tense wrappers, disjunctions, ...), and the rule is
// registered anyway — possibly with zero conditions, so it fires unconditionally.

#[test] // FIXED (fail-closed rule compilation): promoted from the backlog to a live guard.
fn implication_tensed_antecedent_must_not_fire_unconditionally() {
    let engine = fresh_engine();
    // "if Adam ran (past), then Adam is an animal" — on an empty KB, Adam never ran.
    // Fail-closed (reject the unrepresentable rule) and fail-open-fixed (represent the
    // tensed condition and don't fire) are both acceptable; the invariant is that
    // danlu(adam) is NOT derivable from an empty KB.
    if engine
        .assert_text("past runs(Adam) -> animal(Adam).")
        .is_ok()
    {
        let r = engine.query_holds("animal(Adam).").unwrap();
        assert!(
            !r.is_true(),
            "tensed antecedent was dropped → rule fired with no supporting fact: {r:?}"
        );
    }
}

#[test] // FIXED (fail-closed rule compilation): promoted from the backlog to a live guard.
fn implication_disjunctive_antecedent_must_not_fire_unconditionally() {
    let engine = fresh_engine();
    // "if (Adam is a dog OR Adam is a cat) then Adam is an animal" — neither disjunct holds.
    // Reject-or-represent (see the tensed-antecedent test); the invariant is that
    // danlu(adam) is NOT derivable from an empty KB.
    if engine
        .assert_text("dog(Adam) | cat(Adam) -> animal(Adam).")
        .is_ok()
    {
        let r = engine.query_holds("animal(Adam).").unwrap();
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
    let engine = fresh_engine();
    let s = "dog(Adam) | cat(Adam).";
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
    let engine = fresh_engine();
    let s = "dog(Adam) ^ cat(Adam).";
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
    let engine = fresh_engine();
    // "Adam is NOT a dog."
    let neg = engine.assert_text("~dog(Adam).");
    // Rejecting the negation outright is an acceptable fail-closed fix; otherwise
    // it must be recorded and contradict a later "Adam is a dog".
    if neg.is_ok() {
        engine.assert_text("dog(Adam).").unwrap();
        assert!(
            !engine.check_contradictions().is_empty(),
            "negative fact was a silent no-op; the contradiction was not detected"
        );
    }
}

// ─── nibli-semantics silently discards meaning (todo.md: HIGH) ────────────────────────

#[test] // FIXED (rel clause on name conjoined into matrix): promoted to a live guard.
fn rel_clause_on_name_must_not_be_dropped() {
    let engine = fresh_engine();
    engine.assert_text("goes(Adam).").unwrap(); // only known fact: Adam goes
    // "Adam, who is a dog, goes." We do NOT know Adam is a dog, so this must not hold.
    let r = engine.query_holds("goes(Adam where dog).").unwrap();
    assert!(
        !r.is_true(),
        "the `poi gerku` clause was dropped → unsound TRUE for an unproven restriction: {r:?}"
    );
}

#[test] // Positive companion to the guard above: when BOTH conjuncts are known, the
// restricted query holds, and asserting the restricted sentence asserts both conjuncts.
fn rel_clause_on_name_positive_direction() {
    let engine = fresh_engine();
    engine.assert_text("dog(Adam).").unwrap();
    engine.assert_text("goes(Adam).").unwrap();
    let r = engine.query_holds("goes(Adam where dog).").unwrap();
    assert!(
        r.is_true(),
        "both conjuncts known → restricted query must hold: {r:?}"
    );

    // Asserting the restricted sentence must assert BOTH conjuncts.
    let engine2 = fresh_engine();
    engine2.assert_text("goes(Adam where dog).").unwrap();
    let g = engine2.query_holds("dog(Adam).").unwrap();
    let k = engine2.query_holds("goes(Adam).").unwrap();
    assert!(
        g.is_true() && k.is_true(),
        "asserting the restricted sentence must assert both conjuncts: gerku={g:?}, klama={k:?}"
    );
}

#[test] // FIXED (FA-overflow fails closed with a semantic error): promoted to a live guard.
fn fa_tag_beyond_arity_must_error_not_silently_drop() {
    let engine = fresh_engine();
    // `fu` tags place x5; `gerku` is 2-place, so the x5 term `do` cannot be placed.
    let r = engine.assert_text("fu do gerku");
    assert!(
        r.is_err(),
        "over-arity FA tag silently dropped the bound term instead of reporting an error"
    );
}

#[test] // FIXED (pair decomposition emits Unspecified roles; firewall counts per shared event): promoted.
fn pair_in_where_clause_must_not_be_falsely_rejected() {
    let engine = fresh_engine();
    // "a dog that runs fast goes" — valid Lojban; `sutra bajra` is a pair inside the poi clause.
    assert!(
        engine
            .assert_text("goes(some dog where fast runs).")
            .is_ok(),
        "a valid tanru-in-poi relative clause was rejected by the ambiguity firewall"
    );
}

// ─── front-end truncation (todo.md: HIGH; fixture ported to KR at THE DROP) ─

#[test] // FIXED (lexer error channel: unlexable runs surface as positioned parse errors): promoted.
fn lexer_must_not_silently_truncate_input() {
    let engine = fresh_engine();
    // The bare `7` is unparseable mid-claim; the trailing statement must not vanish silently.
    let s = "goes(me) 7 loves(you). animal(some dog).";
    if engine.assert_text(s).is_ok() {
        // If accepted at all, the trailing assertion must have reached the KB.
        let r = engine.query_holds("animal(some dog).").unwrap();
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
    let engine = fresh_engine();
    engine.assert_text("eats(every dog, $da).").unwrap(); // every dog eats something
    engine.assert_text("dog(Alis).").unwrap(); // Alice is a dog
    // Therefore Alice eats something.
    let r = engine.query_holds("eats(Alis, $da).").unwrap();
    assert!(
        r.is_true(),
        "the `ro lo ... da` rule was silently dropped (∃ closed outside ∀): {r:?}"
    );
}

// ─── front-end flattener wrong body indices (todo.md: HIGH) ─────────────────────
// The Abstraction (lib.rs:244) and Restricted (lib.rs:320) arms snapshot
// `sentences.len()` BEFORE recursing and discard push_sentence's return value
// (the Connected arm at lib.rs:146-147 does it right). When the body itself
// pushes a nested sentence, body_idx points at the WRONG (nested) sentence — and
// it is always in-range, so nibli-semantics miscompiles silently. We pin via compile_debug:
// the abstraction's body predicate must actually appear in the compiled FOL.

#[test] // FIXED (flattener uses push_sentence's return value for body indices): promoted.
fn abstraction_body_over_connected_must_reference_real_body() {
    let engine = fresh_engine();
    // The `lo nu ...` abstraction body is `ganai la .adam. gerku gi la .adam. klama`.
    // Its compiled form must contain BOTH the antecedent (gerku) and the
    // consequent (klama). Today the flattener binds the abstraction to the
    // antecedent proposition alone, so `klama` is dropped entirely.
    let buf = engine
        .compile_debug("desires(me, event { dog(Adam) -> goes(Adam) }).")
        .expect("should compile");
    assert!(
        has_predicate_base(&buf, "goes"),
        "the abstraction body's consequent `klama` was dropped — flattener bound \
         the wrong (antecedent) sentence index. FOL:\n{buf:?}"
    );
}

#[test] // FIXED (flattener uses push_sentence's return value for body indices): promoted.
fn abstraction_body_over_rel_clause_must_reference_real_body() {
    let engine = fresh_engine();
    // Abstraction body is `lo gerku poi ke'a barda cu klama`; the head predicate
    // is `klama`. The flattener instead binds the abstraction to the `barda`
    // rel-clause proposition, so `klama` is dropped from the compiled FOL.
    let buf = engine
        .compile_debug("desires(me, event { goes(some dog where big) }).")
        .expect("should compile");
    assert!(
        has_predicate_base(&buf, "goes"),
        "the abstraction body head `klama` was dropped — flattener bound the \
         rel-clause (`barda`) sentence index instead. FOL:\n{buf:?}"
    );
}

// ─── Retraction conflates duplicate ground facts (todo.md: HIGH) ────────────
// The HashSet fact store tracks no multiplicity, and incremental retraction does
// not consult other live records, so retracting one of two records asserting the
// SAME ground fact removes the fact entirely — even though a second active record
// still asserts it. Reachable via the direct fact-injection API (`:assert` /
// assert-fact). The fact must still hold after retracting one of its two records.

#[test] // FIXED (multiplicity-aware incremental retraction): promoted to a live guard.
// PIN RE-ENCODED (2026-06-17, flat-injection fix): the public injection API
// (`assert_fact_direct` / `:assert`) now EVENT-DECOMPOSES, minting a fresh event
// Skolem per call, so two `:assert gerku adam` calls are DISTINCT facts — no
// longer the "same ground fact twice" this guard requires. To still exercise
// HashSet multiplicity + incremental retraction at the FOL level, inject the
// IDENTICAL flat `gerku(adam)` buffer twice via the low-level `kb().assert_fact`
// (which stores flat buffers verbatim) and retract one record by id. The fact
// must still hold while a second live record asserts it.
fn duplicate_ground_fact_survives_retracting_one_copy() {
    let flat_dog_adam = || nibli_types::logic::LogicBuffer {
        nodes: vec![nibli_types::logic::LogicNode::Predicate((
            "gerku".to_string(),
            vec![nibli_types::logic::LogicalTerm::Constant(
                "adam".to_string(),
            )],
        ))],
        roots: vec![0],
    };

    let engine = fresh_engine();
    let id1 = engine
        .kb()
        .assert_fact(flat_dog_adam(), ":assert gerku".to_string())
        .unwrap();
    let _id2 = engine
        .kb()
        .assert_fact(flat_dog_adam(), ":assert gerku".to_string())
        .unwrap();
    // Sanity: both records assert the flat fact (FOL contract) while live.
    let before = engine.kb().query_entailment(flat_dog_adam()).unwrap();
    assert!(
        before.is_true(),
        "sanity: two live records assert gerku(adam): {before:?}"
    );
    // Retract only the FIRST record; the second still asserts gerku(adam).
    engine.kb().retract_fact(id1).unwrap();
    let r = engine.kb().query_entailment(flat_dog_adam()).unwrap();
    assert!(
        r.is_true(),
        "a live record still asserts gerku(adam), but retracting the duplicate \
         removed the fact entirely (HashSet store has no multiplicity): {r:?}"
    );
}

// ─── ∃-heavy nested-abstraction query blowup (Ch 12 consent case study) ─────
// A universal rule whose restrictor and conclusion both nest a full proposition
// inside `lo nu` (11 ∀-dependent Skolems), queried with an indefinite `lo`
// subject: the entailment search generate-and-tested every query existential
// over the full domain × SkolemFn-registry cartesian (members^k). The 3-fact
// KB below took ~40s in a native debug build and exhausted nibli-host's default
// 10B WASM fuel — which is how the trap bricked the REPL session and
// corrupted the Ch 12 captured transcripts. The query runs on a watchdog
// thread so a complexity regression fails cleanly on timeout instead of
// hanging the suite.

#[test] // FIXED (entailment ∃ candidate narrowing — collect_entailment_candidates): promoted.
fn ch12_consent_case_study_traced_query_completes() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let engine = fresh_engine();
        engine.assert_text("owns(some person, some data).").unwrap();
        engine
            .assert_text("permits(some person, event { uses(tool: some data) }).")
            .unwrap();
        engine
            .assert_text(
                "obligated(every person where permits(it, event { uses(tool: some data) }), event { uses(tool: some data) }).",
            )
            .unwrap();
        let (verdict, _trace, _json) = engine
            .query_text_with_proof("obligated(some person, event { uses(tool: some data) }).")
            .unwrap();
        tx.send(verdict).ok();
    });
    let verdict = rx.recv_timeout(std::time::Duration::from_secs(10)).expect(
        "Ch 12 consent query exceeded the 10s debug budget for a 3-fact \
             KB — the ∃-heavy nested-abstraction candidate search has blown up",
    );
    assert!(
        verdict.is_true(),
        "consent → processing obligation must be derivable: {verdict:?}"
    );
}
