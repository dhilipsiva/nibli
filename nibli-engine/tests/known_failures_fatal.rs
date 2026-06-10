//! PROCESS-ABORTING known-failure backlog — QUARANTINED.
//!
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │  WARNING: the test in this file ABORTS THE PROCESS (stack overflow →     │
//! │  SIGABRT). A stack overflow is UNCATCHABLE — it cannot be turned into a   │
//! │  Rust panic and `#[should_panic]` will NOT contain it. One abort kills    │
//! │  every sibling test running in the same process.                          │
//! │                                                                           │
//! │  RUN ONLY IN ISOLATION, never as part of the normal suite:                │
//! │    cargo test -p nibli-engine --test known_failures_fatal \               │
//! │      -- --ignored --exact du_equivalence_unprovable_query_must_not_abort \ │
//! │      --test-threads=1                                                     │
//! │                                                                           │
//! │  EXPECTED RED STATE (today): the command aborts with a stack-overflow     │
//! │  message and a NONZERO exit code. That abort IS the reproduction — report │
//! │  it as "reproduced", not as a harness failure.                            │
//! │                                                                           │
//! │  This is why the test is `#[ignore]`d: it must never run alongside the    │
//! │  rest of the backlog (`known_failures.rs`, `integration.rs`).             │
//! └─────────────────────────────────────────────────────────────────────────┘
//!
//! Bug (panel finding, todo.md: HIGH): "du-equivalence fallback recurses
//! unboundedly — stack overflow (SIGABRT)" — `logji/src/reasoning.rs:594-621`.
//! `check_predicate_in_kb_typed`'s du-equivalence variant fallback recurses with
//! NO cycle guard and NO depth increment: `try_backward_chain_typed` removes its
//! own `visited` entry before returning, and the variant loop passes the same
//! `depth` with a cleaned `visited`, so for a symmetric equivalence class
//! {alis, bob} an unprovable predicate `P(bob)` expands to the variant `P(alis)`,
//! which expands back to `P(bob)`, … unbounded recursion → stack overflow.
//!
//! Reachability: `du` is NOT parseable from surface Lojban, so the fact is
//! injected via the engine's direct fact-injection API
//! `NibliEngine::assert_fact_direct("du", [Constant("alis"), Constant("bob")])`
//! (this routes through `process_assertion` → `collect_ground_facts` → the
//! `union_terms` interception that populates the equivalence classes — exactly
//! what the documented `:assert du` REPL command / `assert-fact` WIT method do).
//! In the native nibli-server embedding (no WASM fuel) this is a process-crash
//! DoS.
//!
//! DESIRED post-fix behaviour: the query returns gracefully (False / Unknown /
//! Err) instead of aborting. When the fix lands (thread depth + a visited guard
//! through the variant fallback), delete the `#[ignore]` so this becomes a normal
//! regression test — it will then be safe to run with the rest of the suite.

use nibli_engine::{EngineLogicalTerm, NibliEngine};

#[test]
#[ignore = "KNOWN BUG (todo.md: du-equivalence fallback recurses unboundedly): PROCESS-ABORTING stack overflow — run ONLY in isolation"]
fn du_equivalence_unprovable_query_must_not_abort() {
    let engine = NibliEngine::new();

    // Inject `du(alis, bob)` directly (du is not surface-parseable). This unions
    // {alis, bob} into one equivalence class in logji's union-find.
    engine
        .assert_fact_direct(
            "du".to_string(),
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
        .query_holds("la .bob. cu mlatu")
        .expect("query must return, not abort the process");
    assert!(
        !r.is_true(),
        "mlatu(bob) is not provable for either equivalence-class member; \
         a graceful non-True result is required (today the process aborts): {r:?}"
    );
}
