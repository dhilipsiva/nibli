//! Verdict-regression corpus — the safety net for the Stage 2c formula-evaluator
//! merge (one `check_formula_holds_core<S: TraceSink>` replacing the separate
//! four-valued untraced evaluator + boolean traced evaluator).
//!
//! Every rep asserts the SAME verdict on BOTH query paths and that they AGREE:
//!   1. `query_holds`            — the BARE path (`query_entailment_inner`).
//!   2. `query_text_with_proof`  — the PROOF path (`query_entailment_with_proof`).
//!   3. `assert_eq!(bare, proof)` — the DIVERGENCE CATCHER.
//!
//! 2c changes BOTH paths (the bare path gains four-valued And/Or short-circuit;
//! the proof path drops the Stage-1 re-walks), so a single-path corpus would miss
//! a regression on the other. The cross-path equality is the standing guard that
//! the two never diverge. Landed GREEN against pre-2c code as the baseline.

use nibli_engine::{EngineQueryResult, NibliEngine};

/// A fresh KR-mode engine (corpus machine-ported from Lojban at THE DROP).
fn fresh_engine() -> NibliEngine {
    NibliEngine::new()
}

fn engine_with_facts(lines: &[&str]) -> NibliEngine {
    let engine = fresh_engine();
    for line in lines {
        engine
            .assert_text(line)
            .unwrap_or_else(|e| panic!("failed to assert '{line}': {e}"));
    }
    engine
}

/// Run one corpus rep through both query paths and assert they agree with the
/// expected four-valued verdict (and with each other).
fn check_rep(kb: &[&str], query: &str, expected: &EngineQueryResult) {
    let engine = engine_with_facts(kb);
    let bare = engine
        .query_holds(query)
        .unwrap_or_else(|e| panic!("bare query '{query}' errored: {e}"));
    let (proof, _trace, _json) = engine
        .query_text_with_proof(query)
        .unwrap_or_else(|e| panic!("proof query '{query}' errored: {e}"));
    assert_eq!(
        &bare, expected,
        "BARE-path verdict mismatch for query `{query}` (kb={kb:?})"
    );
    assert_eq!(
        &proof, expected,
        "PROOF-path verdict mismatch for query `{query}` (kb={kb:?})"
    );
    assert_eq!(
        bare, proof,
        "BARE/PROOF path DIVERGENCE for query `{query}` (kb={kb:?})"
    );
}

#[test]
fn verdict_corpus_true_false_breadth() {
    use EngineQueryResult::{False, True};
    // (kb_lines, query, expected) — breadth across the reasoning features the
    // merged evaluator must preserve: direct facts, universal rules, prenex
    // multi-var joins, surface numeric groups, du equivalence, temporal.
    let reps: Vec<(&[&str], &str, EngineQueryResult)> = vec![
        // direct assertion / miss
        (&["dog(Rex)."], "dog(Rex).", True),
        (&["dog(Rex)."], "cat(Rex).", False),
        (&["big(some dog)."], "big(some dog).", True),
        // universal rule chain + negative control
        (&["animal(every dog).", "dog(Rex)."], "animal(Rex).", True),
        (&["animal(every dog)."], "animal(Rex).", False),
        // prenex CYP cross-entity join + negative control
        (
            &[
                "all $da, $de, $di: prevents($da, $di) & metabolized_by($de, $di) -> increases($de).",
                "prevents(Flukonazol, Siptucin).",
                "metabolized_by(Uarfarin, Siptucin).",
            ],
            "increases(Uarfarin).",
            True,
        ),
        (
            &[
                "all $da, $de, $di: prevents($da, $di) & metabolized_by($de, $di) -> increases($de).",
                "prevents(Flukonazol, Siptucin).",
                "metabolized_by(Apiksaban, Sipibeman).",
            ],
            "increases(Apiksaban).",
            False,
        ),
        // prenex symmetric (both vars bound by the conclusion)
        (
            &[
                "all $da, $de: friend($da, $de) -> friend($de, $da).",
                "friend(Rex, Felix).",
            ],
            "friend(Felix, Rex).",
            True,
        ),
        // surface numeric group (decomposed comparison): 5 > 3, 3 > 5
        (&[], "greater(5, 3).", True),
        (&[], "greater(3, 5).", False),
        // du (identity) equivalence transfer
        (&["Djan = Jan.", "dog(Djan)."], "dog(Jan).", True),
        // temporal: tensed assertion + tense discrimination
        (&["past dog(Rex)."], "past dog(Rex).", True),
        (&["past dog(Rex)."], "future dog(Rex).", False),
    ];
    for (kb, query, expected) in &reps {
        check_rep(kb, query, expected);
    }
}

#[test]
fn compute_conjunct_ingestion_drop_is_verdict_neutral() {
    // Claim-3 hazard probe (Stage 2c). The merged evaluator short-circuits an
    // And on a definitively-False left conjunct, so it no longer evaluates (and
    // thus no longer AUTO-INGESTS) a compute-right conjunct on the BARE path
    // (`query_holds`). This must not flip any later verdict: a compute predicate
    // is RE-DISPATCHED (recomputed) on every direct query, so it is never
    // reachable ONLY via the dropped store ingestion. The single theoretical
    // flip vector — a universal rule keyed on the compute relation, whose
    // condition check reads the store WITHOUT recomputing — is not expressible
    // through the surface compiler (compute relations are not rule-compilable
    // conditions), which is itself the neutrality evidence.
    //
    // Demonstrated on BOTH paths: (A) `False ∧ compute` is False (the
    // conjunction), and (B) a subsequent DIRECT compute query is still True
    // (recompute) — regardless of whether (A) ingested the fact. `mlatu(rex)` is
    // unasserted, so the left conjunct is definitively False.
    let engine = engine_with_facts(&[]);
    let conj = "cat(Rex) & product(6, 2, 3).";
    let a_bare = engine.query_holds(conj).unwrap();
    let (a_proof, _t, _j) = engine.query_text_with_proof(conj).unwrap();
    assert!(
        a_bare.is_false(),
        "False ∧ compute should be False (bare), got {a_bare:?}"
    );
    assert!(
        a_proof.is_false(),
        "False ∧ compute should be False (proof), got {a_proof:?}"
    );
    let b_bare = engine.query_holds("product(6, 2, 3).").unwrap();
    let (b_proof, _t2, _j2) = engine.query_text_with_proof("product(6, 2, 3).").unwrap();
    assert!(
        b_bare.is_true(),
        "compute recomputes True after the dropped ingestion (bare), got {b_bare:?}"
    );
    assert!(
        b_proof.is_true(),
        "compute recomputes True after the dropped ingestion (proof), got {b_proof:?}"
    );
}

#[test]
fn verdict_corpus_compute_requery_stable() {
    // A surface arithmetic query that succeeds auto-ingests its compute fact; a
    // re-query must return the SAME verdict on both paths whether or not the fact
    // was ingested (recompute is free). Guards that the merged evaluator's compute
    // handling stays verdict-stable across repeated queries.
    let engine = engine_with_facts(&[]);
    for _ in 0..3 {
        let bare = engine.query_holds("product(6, 2, 3).").unwrap();
        let (proof, _t, _j) = engine.query_text_with_proof("product(6, 2, 3).").unwrap();
        assert!(bare.is_true(), "6 = 2*3 should hold (bare), got {bare:?}");
        assert!(
            proof.is_true(),
            "6 = 2*3 should hold (proof), got {proof:?}"
        );
        assert_eq!(bare, proof, "compute query bare/proof divergence");
    }
}
