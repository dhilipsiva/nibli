//! FIXED former process-aborting regression — now a normal, safe-to-run test.
//!
//! Bug (panel finding, todo.md: HIGH, FIXED 2026-06-10): "du-equivalence fallback
//! recurses unboundedly — stack overflow (SIGABRT)" — `nibli-reason/src/reasoning.rs`.
//! `check_predicate_in_kb_typed`'s du-equivalence variant fallback recursed with
//! NO cycle guard and NO depth increment: `try_backward_chain_typed` removes its
//! own `visited` entry before returning, and the variant loop passed the same
//! `depth` with a cleaned `visited`, so for a symmetric equivalence class
//! {alis, bob} an unprovable predicate `P(bob)` expanded to the variant `P(alis)`,
//! which expanded back to `P(bob)`, … unbounded recursion → stack overflow. The
//! traced twin (`trace_predicate_provenance_typed`) had the same defect (it
//! recursed on the variant with the same `depth` and a fresh `HashSet`).
//!
//! Fix: the variant fallback now (a) re-inserts `fact` into the shared `visited`
//! set for the duration of the variant search and skips already-visited variants,
//! and (b) advances `depth + 1` on the recursive call so the iterative-deepening
//! bound (`depth + 1 < max_chain_depth`) also terminates the search. The traced
//! twin advances `depth + 1` through both the probe and the recursive trace.
//!
//! Reachability: `du` is NOT parseable from surface Lojban, so the fact is
//! injected via the engine's direct fact-injection API
//! `NibliEngine::assert_fact_direct("equals", [Constant("alis"), Constant("bob")])`
//! (this routes through `process_assertion` → `collect_ground_facts` → the
//! `union_terms` interception that populates the equivalence classes — exactly
//! what the documented `:assert du` REPL command / `assert-fact` WIT method do).
//! In the native nibli-server embedding (no WASM fuel) this had been a
//! process-crash DoS.
//!
//! Post-fix behaviour (asserted below): the query returns gracefully with a
//! non-True result instead of aborting. The `#[ignore]` has been removed, so this
//! is now a normal regression test, safe to run alongside the rest of the suite.

use nibli_engine::{EngineLogicalTerm, NibliEngine};

/// A fresh KR-mode engine (the direct fact injection is language-free; the
/// query text was ported to KR at THE DROP).
fn fresh_engine() -> NibliEngine {
    NibliEngine::new()
}

#[test]
fn du_equivalence_unprovable_query_must_not_abort() {
    let engine = fresh_engine();

    // Inject `du(alis, bob)` directly (du is not surface-parseable). This unions
    // {alis, bob} into one equivalence class in logji's union-find.
    engine
        .assert_fact_direct(
            "equals".to_string(),
            vec![
                EngineLogicalTerm::Constant("alis".to_string()),
                EngineLogicalTerm::Constant("bob".to_string()),
            ],
        )
        .expect("direct du fact injection should succeed");

    // Query an UNPROVABLE predicate about bob. The du-equivalence fallback tries
    // the variant `mlatu(alis)`, which is also unprovable and re-enters the
    // fallback for `mlatu(bob)` … → unbounded recursion → SIGABRT today.
    //
    // Post-fix this returns a definitive False (mlatu holds for neither member).
    let r = engine
        .query_holds("cat(Bob).")
        .expect("query must return, not abort the process");
    assert!(
        !r.is_true(),
        "mlatu(bob) is not provable for either equivalence-class member; \
         a graceful non-True result is required (today the process aborts): {r:?}"
    );
}
