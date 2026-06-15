//! Integration tests for the nibli-engine: full pipeline (parse → compile → reason).
//!
//! Each test creates a fresh NibliEngine, asserts Lojban text, and queries with proof.
//! No WASM, no HTTP — exercises gerna+smuni+logji directly via Rust crate calls.

use nibli_engine::{EngineAggregateOp, EngineQueryResult, NibliEngine};
use nibli_store::NibliStore;
use std::fs;
use std::path::{Path, PathBuf};

/// Helper: create a fresh engine, assert multiple lines, return the engine.
fn engine_with_facts(lines: &[&str]) -> NibliEngine {
    let engine = NibliEngine::new();
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

fn cleanup(path: &Path) {
    let _ = fs::remove_file(path);
}

// ─── Basic assertion and query ──────────────────────────────────────

#[test]
fn simple_assertion_and_query() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, trace, json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_true(&holds, "Query for asserted fact should hold");
    assert!(!trace.is_empty(), "Proof trace should be non-empty");
    assert!(!json.is_empty(), "Proof JSON should be non-empty");
}

#[test]
fn simple_negation_query_false() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu barda").unwrap();
    assert_false(&holds, "Query for unasserted fact should not hold");
}

// ─── Cooperative cancellation ───────────────────────────────────────

#[test]
fn engine_cancel_flag_aborts_query() {
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;
    // With the cancel flag pre-set, every query path returns Err instead of
    // running to completion. This is the hook the native server's watchdog
    // uses to free a blocking thread when the request timeout elapses.
    let engine = engine_with_facts(&["la .adam. cu gerku", "ro lo gerku cu danlu"]);
    let flag = Arc::new(AtomicBool::new(true));
    engine.set_cancel_flag(flag.clone());

    let proof = engine.query_text_with_proof("la .adam. cu danlu");
    assert!(
        proof.is_err(),
        "cancelled proof query must Err, got {proof:?}"
    );
    assert!(proof.unwrap_err().to_lowercase().contains("cancel"));

    let holds = engine.query_holds("la .adam. cu danlu");
    assert!(
        holds.is_err(),
        "cancelled holds query must Err, got {holds:?}"
    );

    // Clearing the flag restores normal evaluation.
    engine.clear_cancel_flag();
    let (result, _, _) = engine
        .query_text_with_proof("la .adam. cu danlu")
        .expect("query should succeed after clearing cancel flag");
    assert_true(
        &result,
        "syllogism should hold once cancellation is cleared",
    );
}

// ─── Universal rule chain (syllogism) ───────────────────────────────

#[test]
fn universal_rule_chain_syllogism() {
    let engine = engine_with_facts(&[
        "ro lo gerku cu danlu",
        "ro lo danlu cu citka",
        "la .adam. cu gerku",
    ]);

    // Direct fact
    let (holds, _trace, _json) = engine.query_text_with_proof("la .adam. cu gerku").unwrap();
    assert_true(&holds, "Direct fact should hold");

    // One-hop derivation: gerku → danlu
    let (holds, trace, _json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert_true(&holds, "One-hop derived fact should hold");
    assert!(trace.contains("Rule"), "Proof trace should show derivation");

    // Two-hop derivation: gerku → danlu → citka
    let (holds, trace, _json) = engine.query_text_with_proof("la .adam. cu citka").unwrap();
    assert_true(&holds, "Two-hop derived fact should hold");
    assert!(
        trace.contains("Rule"),
        "Proof trace should show derivation chain"
    );
}

// ─── Temporal reasoning ─────────────────────────────────────────────

#[test]
fn temporal_past_assertion_and_query() {
    let engine = engine_with_facts(&["pu lo gerku cu barda"]);

    // Tensed query should hold
    let (holds, _trace, _json) = engine
        .query_text_with_proof("pu lo gerku cu barda")
        .unwrap();
    assert_true(&holds, "Past-tensed query should hold");

    // Bare (untensed) query should NOT hold
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_false(&holds, "Bare query should not match past-tensed fact");
}

#[test]
fn temporal_tense_discrimination() {
    let engine = engine_with_facts(&["pu lo gerku cu barda"]);

    // Future tense should NOT match past tense
    let (holds, _trace, _json) = engine
        .query_text_with_proof("ba lo gerku cu barda")
        .unwrap();
    assert_false(&holds, "Future query should not match past-tensed fact");
}

// ─── Description opacity (le vs lo) ────────────────────────────────

#[test]
fn description_opacity_le_vs_lo() {
    let engine = engine_with_facts(&["le gerku cu barda"]);

    // le query should hold (opaque description)
    let (holds, _trace, _json) = engine.query_text_with_proof("le gerku cu barda").unwrap();
    assert_true(&holds, "le (opaque) query should hold");
}

#[test]
fn la_name_assertion() {
    let engine = engine_with_facts(&["la .adam. cu gerku"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("la .adam. cu gerku").unwrap();
    assert_true(&holds, "la name assertion should hold");
}

// ─── Parse error handling ───────────────────────────────────────────

#[test]
fn parse_error_returns_syntax_error() {
    let engine = NibliEngine::new();
    let result = engine.assert_text("not valid lojban at all !!!");
    assert!(result.is_err(), "Invalid Lojban should produce an error");
    let err = result.unwrap_err();
    assert!(
        err.contains("[Syntax Error]"),
        "Error should be a syntax error, got: {}",
        err
    );
}

#[test]
fn query_parse_error() {
    let engine = NibliEngine::new();
    let result = engine.query_text_with_proof("blorp bleep !!!");
    assert!(result.is_err(), "Invalid query should produce an error");
}

// ─── Proof trace structure ──────────────────────────────────────────

#[test]
fn proof_trace_contains_asserted_for_ground_fact() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, trace, json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
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
    let engine = engine_with_facts(&["ro lo gerku cu danlu", "la .adam. cu gerku"]);
    let (_holds, _trace, json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("Proof JSON should parse");
    let steps = parsed["steps"].as_array().expect("steps should be array");
    assert!(steps.len() > 1, "Derived proof should have multiple steps");
}

// ─── Engine reset ───────────────────────────────────────────────────

#[test]
fn reset_clears_knowledge_base() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_true(&holds, "Fact should hold before reset");

    engine.reset();

    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_false(&holds, "Fact should not hold after reset");
}

// ─── Multiple facts ─────────────────────────────────────────────────

#[test]
fn multiple_independent_facts() {
    let engine = engine_with_facts(&["lo gerku cu barda", "lo mlatu cu cmalu"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_true(&holds, "First fact should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu cmalu").unwrap();
    assert_true(&holds, "Second fact should hold");
}

// ─── Multi-sentence assertion ───────────────────────────────────────

#[test]
fn multi_sentence_assertion() {
    let engine = NibliEngine::new();
    // Assert multiple sentences in one text block (separated by .i)
    engine
        .assert_text("lo gerku cu barda .i lo mlatu cu cmalu")
        .unwrap();
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert_true(&holds, "First sentence should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu cmalu").unwrap();
    assert_true(&holds, "Second sentence should hold");
}

// ─── Sentence connectives ───────────────────────────────────────────

#[test]
fn universal_rule_with_named_entity() {
    // Universal rules + named entity — the primary use case
    let engine = engine_with_facts(&["ro lo gerku cu danlu", "la .adam. cu gerku"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert_true(&holds, "Named entity should derive through universal rule");
}

#[test]
fn forethought_implication_ganai_reasons() {
    // ganai A gi B  ==  A -> B. Assert the conditional + A (gerku), derive B (danlu).
    let engine = engine_with_facts(&[
        "ganai la .adam. cu gerku gi la .adam. cu danlu",
        "la .adam. cu gerku",
    ]);
    let (holds, _t, _j) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert_true(
        &holds,
        "ganai: danlu should derive from gerku (modus ponens)",
    );

    // Negative control: without the antecedent, the consequent is not derivable.
    let only_rule = engine_with_facts(&["ganai la .adam. cu gerku gi la .adam. cu danlu"]);
    let (holds, _t, _j) = only_rule
        .query_text_with_proof("la .adam. cu danlu")
        .unwrap();
    assert_false(&holds, "ganai: danlu must NOT hold without gerku");
}

#[test]
fn forethought_biconditional_go_gi_reasons_both_directions() {
    // go A gi B  ==  A <-> B. Reasons from either side (no CycleCut).
    let fwd = engine_with_facts(&[
        "go la .adam. cu gerku gi la .adam. cu danlu",
        "la .adam. cu gerku",
    ]);
    let (holds, _t, _j) = fwd.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert_true(
        &holds,
        "go biconditional: gerku should derive danlu (forward)",
    );

    let rev = engine_with_facts(&[
        "go la .adam. cu gerku gi la .adam. cu danlu",
        "la .adam. cu danlu",
    ]);
    let (holds, _t, _j) = rev.query_text_with_proof("la .adam. cu gerku").unwrap();
    assert_true(
        &holds,
        "go biconditional: danlu should derive gerku (reverse)",
    );
}

#[test]
fn afterthought_biconditional_jo_reasons_both_directions() {
    // S1 .i jo S2  ==  S1 <-> S2.
    let fwd = engine_with_facts(&[
        "la .adam. cu gerku .i jo la .adam. cu danlu",
        "la .adam. cu gerku",
    ]);
    let (holds, _t, _j) = fwd.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert_true(
        &holds,
        ".i jo biconditional: gerku should derive danlu (forward)",
    );

    let rev = engine_with_facts(&[
        "la .adam. cu gerku .i jo la .adam. cu danlu",
        "la .adam. cu danlu",
    ]);
    let (holds, _t, _j) = rev.query_text_with_proof("la .adam. cu gerku").unwrap();
    assert_true(
        &holds,
        ".i jo biconditional: danlu should derive gerku (reverse)",
    );
}

// ─── Conversion (se) ────────────────────────────────────────────────

#[test]
fn se_conversion_assertion_and_query() {
    let engine = engine_with_facts(&["la .adam. cu se ponse lo gerku"]);
    let (holds, _trace, _json) = engine
        .query_text_with_proof("la .adam. cu se ponse lo gerku")
        .unwrap();
    assert_true(&holds, "se-converted assertion should be queryable");
}

#[test]
fn query_holds_matches_proof_query_boolean() {
    let engine = engine_with_facts(&["ro lo gerku cu danlu", "la .adam. cu gerku"]);

    let via_bool = engine
        .query_holds("la .adam. cu danlu")
        .expect("Boolean query should succeed");
    let (via_proof, _trace, _json) = engine
        .query_text_with_proof("la .adam. cu danlu")
        .expect("Proof query should succeed");

    assert_eq!(
        via_bool, via_proof,
        "Boolean query API and proof query API must agree on whether a fact holds"
    );
}

#[test]
fn reset_then_reassert_replaces_previous_kb_contents() {
    let engine = engine_with_facts(&["la .adam. cu gerku"]);
    assert!(
        engine
            .query_holds("la .adam. cu gerku")
            .expect("Initial fact should be queryable")
            .is_true()
    );

    engine.reset();
    engine
        .assert_text("la .elis. cu mlatu")
        .expect("New fact should assert after reset");

    assert!(
        engine
            .query_holds("la .adam. cu gerku")
            .expect("Old fact query should still run")
            .is_false(),
        "Reset should remove prior KB contents before new facts are asserted"
    );
    assert!(
        engine
            .query_holds("la .elis. cu mlatu")
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
        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        engine
            .assert_text("ro lo gerku cu danlu")
            .expect("Rule should persist");
        engine
            .assert_text("la .adam. cu gerku")
            .expect("Fact should persist");
        assert!(
            engine
                .query_holds("la .adam. cu danlu")
                .expect("Derived query should run before reopen")
                .is_true()
        );
    }

    {
        let reopened = NibliEngine::open(&path).expect("Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("la .adam. cu danlu")
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
        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        engine
            .assert_text("la .adam. cu gerku")
            .expect("Fact should persist")
    };

    {
        let mut store = NibliStore::open(&path, "local".into()).expect("Store should open");
        store
            .retract_fact(fact_id)
            .expect("Retracting persisted fact should succeed");
    }

    {
        let reopened = NibliEngine::open(&path).expect("Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("la .adam. cu gerku")
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
        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        let id = engine
            .assert_text("la .adam. cu gerku")
            .expect("Fact should persist");
        assert!(
            engine
                .query_holds("la .adam. cu gerku")
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
                .query_holds("la .adam. cu gerku")
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
        let reopened = NibliEngine::open(&path).expect("Persistent engine should reopen");
        assert!(
            reopened
                .query_holds("la .adam. cu gerku")
                .expect("Query should run after reopen")
                .is_false(),
            "Facts retracted via the engine API must stay retracted after reopen"
        );
    }

    cleanup(&path);
}

#[test]
fn persistent_engine_queries_merged_remote_facts_after_reopen() {
    let local_path = temp_db_path("merge_local");
    let remote_path = temp_db_path("merge_remote");
    cleanup(&local_path);
    cleanup(&remote_path);

    {
        let local_engine = NibliEngine::open(&local_path).expect("Local engine should open");
        local_engine
            .assert_text("ro lo gerku cu danlu")
            .expect("Local rule should persist");
    }

    {
        let remote_engine = NibliEngine::open(&remote_path).expect("Remote engine should open");
        remote_engine
            .assert_text("la .skip. cu mlatu")
            .expect("Remote dummy fact should persist");
        remote_engine
            .assert_text("la .adam. cu gerku")
            .expect("Remote fact should persist");
    }

    {
        let mut local_store =
            NibliStore::open(&local_path, "local".into()).expect("Local store should open");
        local_store
            .merge_from_file(&remote_path)
            .expect("Store merge should succeed");
    }

    {
        let reopened = NibliEngine::open(&local_path).expect("Merged engine should reopen");
        assert!(
            reopened
                .query_holds("la .adam. cu danlu")
                .expect("Merged query should run after reopen")
                .is_true(),
            "Merged remote facts should replay into the reopened engine"
        );
    }

    cleanup(&local_path);
    cleanup(&remote_path);
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
    let corpus = include_str!("../../gdpr.lojban");
    let engine = NibliEngine::new();
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

/// THE HEADLINE: consent-withdrawal belief revision.
/// With consent, processing has a lawful basis (Art 6) and there is no erasure
/// right. Retract consent and BOTH flip: no lawful basis remains, so the right
/// to erasure (Art 17(1)(b)) arises. The erasure verdict is derived by
/// negation-as-failure and the proof carries the NAF dependency flag.
#[test]
fn gdpr_belief_revision_consent_withdrawal() {
    let engine = NibliEngine::new();
    engine.assert_text("la .adam. cu prenu").unwrap();
    engine
        .assert_text("ro lo prenu poi zanru cu se curmi")
        .unwrap(); // Art 6(1)(a)
    let consent_id = engine.assert_text("la .adam. cu zanru").unwrap();

    // ── Consent present ──
    assert_true(
        &engine.query_holds("la .adam. cu se curmi").unwrap(),
        "With consent, Adam's processing has a lawful basis",
    );
    assert_false(
        &engine.query_holds("la .adam. na se curmi").unwrap(),
        "With consent, there is no right to erasure",
    );

    // ── Withdraw consent ──
    engine.retract_fact(consent_id).unwrap();

    assert_false(
        &engine.query_holds("la .adam. cu se curmi").unwrap(),
        "After withdrawal, no lawful basis remains",
    );
    let (erasure, trace, json) = engine
        .query_text_with_proof("la .adam. na se curmi")
        .unwrap();
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
        "ro lo prenu poi nupre cu se curmi",
        "la .adam. cu prenu",
        "la .adam. cu nupre",
        "la .bet. cu prenu", // a person with no lawful basis
    ]);
    assert_true(
        &engine.query_holds("la .adam. cu se curmi").unwrap(),
        "Contract is a lawful basis (Art 6(1)(b))",
    );
    assert_false(
        &engine.query_holds("la .bet. cu se curmi").unwrap(),
        "A subject with no lawful basis has no lawful processing",
    );
}

/// Art 9: special-category (health) data requires a stricter, specific basis;
/// ordinary personal data does not (negative control / DPIA triage).
#[test]
fn gdpr_special_category_requires_stricter_basis() {
    let engine = engine_with_facts(&[
        "ro lo kanro datni cu se bilga lo nu satci",
        "la .kanrek. cu kanro datni",
        "la .ordrek. cu datni",
    ]);
    assert_true(
        &engine
            .query_holds("la .kanrek. cu se bilga lo nu satci")
            .unwrap(),
        "Health data requires a stricter basis (Art 9)",
    );
    assert_false(
        &engine
            .query_holds("la .ordrek. cu se bilga lo nu satci")
            .unwrap(),
        "Ordinary data does not require the special-category basis",
    );
}

/// Art 5: principles (here, accuracy) apply to ALL personal data, reached through
/// a category -> data -> obligation chain (multi-hop inference over special data).
#[test]
fn gdpr_art5_accuracy_applies_to_health_data() {
    let engine = engine_with_facts(&[
        "ro lo kanro datni cu datni",
        "ro lo datni cu se bilga lo nu drani",
        "la .kanrek. cu kanro datni",
    ]);
    let (holds, trace, _json) = engine
        .query_text_with_proof("la .kanrek. cu se bilga lo nu drani")
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
        "ro lo prenu cu se curmi lo nu datni facki",
        "la .adam. cu prenu",
        "la .akmes. cu datni turni", // a controller, not a data subject
    ]);
    assert_true(
        &engine
            .query_holds("la .adam. cu se curmi lo nu datni facki")
            .unwrap(),
        "A data subject has the right of access (Art 15)",
    );
    assert_false(
        &engine
            .query_holds("la .akmes. cu se curmi lo nu datni facki")
            .unwrap(),
        "A controller (non-subject) does not acquire the access right",
    );
}

/// Art 33: a controller that suffers a breach must notify; a controller with no
/// breach has no such obligation (negative control / audit evidence).
#[test]
fn gdpr_breach_notification() {
    let engine = engine_with_facts(&[
        "ro lo datni turni poi cfila cu se bilga lo nu notci",
        "la .akmes. cu datni turni",
        "la .gugli. cu datni turni",
        "la .akmes. cu cfila", // only AkmeCorp breached
    ]);
    assert_true(
        &engine
            .query_holds("la .akmes. cu se bilga lo nu notci")
            .unwrap(),
        "A breached controller must notify (Art 33)",
    );
    assert_false(
        &engine
            .query_holds("la .gugli. cu se bilga lo nu notci")
            .unwrap(),
        "A controller with no breach has no notification obligation",
    );
}

/// PERF REGRESSION PIN (Ch 20 reproducibility): the chapter tells readers to
/// load the FULL shipped gdpr.lojban and run `la .adam. cu se curmi`. Before
/// the 2026-06 backward-chaining fixes in logji (lazy candidate build,
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
    let corpus = include_str!("../../gdpr.lojban");
    let engine = NibliEngine::new();
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
        if trimmed == "la .adam. cu zanru" {
            consent_id = Some(id);
        }
    }

    // Ch 20's first lawful-basis query, against the FULL loaded corpus.
    assert_true(
        &engine.query_holds("la .adam. cu se curmi").unwrap(),
        "Against the full corpus, Adam's processing has a lawful basis (Art 6)",
    );

    // The consent-withdrawal belief-revision flip, also against the full corpus.
    engine
        .retract_fact(consent_id.expect("consent line present in gdpr.lojban"))
        .unwrap();
    assert_false(
        &engine.query_holds("la .adam. cu se curmi").unwrap(),
        "After withdrawal, no lawful basis remains (full-corpus exhaustive search)",
    );
    assert_true(
        &engine.query_holds("la .adam. na se curmi").unwrap(),
        "After withdrawal, the right to erasure (Art 17) is triggered",
    );

    let elapsed = start.elapsed();
    assert!(
        elapsed < std::time::Duration::from_secs(120),
        "full-corpus Ch 20 sequence took {elapsed:?} (budget 120s) — the \
         backward-chaining candidate search has regressed"
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
fn stacked_poi_conjoins_both_clauses() {
    let engine = engine_with_facts(&[
        "ro lo xukmi poi zenba poi cinla cu ckape",
        "la .alfan. cu xukmi",
        "la .alfan. cu zenba",
        "la .alfan. cu cinla", // both conditions hold
        "la .betan. cu xukmi",
        "la .betan. cu zenba", // zenba only
        "la .gaman. cu xukmi",
        "la .gaman. cu cinla", // cinla only
    ]);
    assert_true(
        &engine.query_holds("la .alfan. cu ckape").unwrap(),
        "both zenba and cinla -> ckape",
    );
    assert_false(
        &engine.query_holds("la .betan. cu ckape").unwrap(),
        "zenba only (cinla missing) -> NOT ckape",
    );
    assert_false(
        &engine.query_holds("la .gaman. cu ckape").unwrap(),
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
    let corpus = include_str!("../../drug-interactions.lojban");
    let engine = NibliEngine::new();
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
        &engine.query_holds("la .varfarin. cu zenba").unwrap(),
        "Warfarin concentration rises (fluconazole inhibits CYP2C9, warfarin is a substrate)",
    );
    // Step 2: toxicity risk (general rule: increased concentration + narrow index).
    assert_true(
        &engine.query_holds("la .varfarin. cu ckape").unwrap(),
        "Warfarin is at toxicity risk (increased concentration + narrow therapeutic index)",
    );
    // Step 3: safety alert (general rule: toxicity risk -> alert), with proof.
    let (alert, trace, _json) = engine
        .query_text_with_proof("la .varfarin. cu kajde")
        .unwrap();
    assert_true(&alert, "Warfarin co-prescription warrants a safety alert");
    assert!(
        trace.contains("Rule"),
        "Alert proof should show a derivation chain, got:\n{trace}"
    );

    // Negative control: apixaban (CYP3A4) — fluconazole does not inhibit CYP3A4.
    assert_false(
        &engine.query_holds("la .apiksaban. cu zenba").unwrap(),
        "Apixaban concentration does not rise (CYP3A4 not inhibited by fluconazole)",
    );
    assert_false(
        &engine.query_holds("la .apiksaban. cu kajde").unwrap(),
        "Apixaban co-administration produces NO alert (deduced False, not unknown)",
    );
}

/// The downstream clinical rules are GENERAL: phenytoin, a different narrow-index
/// CYP2C9 substrate, reaches a safety alert through the SAME toxicity/alert rules
/// (no per-drug alert rule is written).
#[test]
fn ddi_general_rules_fire_for_second_drug() {
    let engine = engine_with_ddi_corpus();
    assert_true(
        &engine.query_holds("la .fenituin. cu kajde").unwrap(),
        "Phenytoin alerts via the same general toxicity/alert rules as warfarin",
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
        "la .raxitidin. cu xukmi",
        "la .raxitidin. cu zenba", // concentration rises
        "ro lo xukmi poi zenba poi cinla cu ckape",
        "ro lo xukmi poi ckape cu kajde",
    ]);
    assert_false(
        &wide.query_holds("la .raxitidin. cu ckape").unwrap(),
        "A wide-margin drug with raised concentration is not at toxicity risk",
    );
    assert_false(
        &wide.query_holds("la .raxitidin. cu kajde").unwrap(),
        "A wide-margin drug with raised concentration warrants no alert",
    );

    // (b) narrow-index, but NO interaction (no concentration rise) -> no risk.
    // This is the discriminating control: it fails if the toxicity step ignores
    // the concentration-increase premise.
    let narrow = engine_with_facts(&[
        "la .narotil. cu xukmi",
        "la .narotil. cu cinla", // narrow index, but no interaction
        "ro lo xukmi poi zenba poi cinla cu ckape",
        "ro lo xukmi poi ckape cu kajde",
    ]);
    assert_false(
        &narrow.query_holds("la .narotil. cu ckape").unwrap(),
        "A narrow-index drug with no interaction is not at toxicity risk",
    );
    assert_false(
        &narrow.query_holds("la .narotil. cu kajde").unwrap(),
        "A narrow-index drug with no interaction warrants no alert",
    );
}

/// Belief revision (non-monotonic): an alert is not "baked in" — it is re-derived
/// from current facts. The clinically canonical move: the interacting drug is
/// discontinued. Retracting "fluconazole inhibits CYP2C9" removes the mechanism's
/// entry premise, so the concentration rise, the toxicity risk, and the alert all
/// dissolve in one step. Phenytoin shares the same inhibitor premise, so its alert
/// dissolves too — exactly the intended clinical consequence of stopping the
/// inhibitor.
#[test]
fn ddi_belief_revision_discontinue_inhibitor() {
    let engine = NibliEngine::new();
    for line in [
        "la .varfarin. cu xukmi",
        "la .fenituin. cu xukmi",
        "la .flukonazol. cu xukmi",
        "la .varfarin. cu se katna la .siptucin.",
        "la .fenituin. cu se katna la .siptucin.",
        "la .varfarin. cu cinla",
        "la .fenituin. cu cinla",
    ] {
        engine.assert_text(line).unwrap();
    }
    let inhibits_id = engine
        .assert_text("la .flukonazol. cu fanta la .siptucin.")
        .unwrap();
    for line in [
        "ganai ge la .flukonazol. cu fanta la .siptucin. gi la .varfarin. cu se katna la .siptucin. gi la .varfarin. cu zenba",
        "ganai ge la .flukonazol. cu fanta la .siptucin. gi la .fenituin. cu se katna la .siptucin. gi la .fenituin. cu zenba",
        "ro lo xukmi poi zenba poi cinla cu ckape",
        "ro lo xukmi poi ckape cu kajde",
    ] {
        engine.assert_text(line).unwrap();
    }

    // ── Before discontinuation: both drugs alert ──
    assert_true(
        &engine.query_holds("la .varfarin. cu kajde").unwrap(),
        "While fluconazole inhibits CYP2C9, warfarin alerts",
    );
    assert_true(
        &engine.query_holds("la .fenituin. cu kajde").unwrap(),
        "While fluconazole inhibits CYP2C9, phenytoin alerts",
    );

    // ── Discontinue fluconazole: retract the inhibition fact ──
    engine.retract_fact(inhibits_id).unwrap();

    assert_false(
        &engine.query_holds("la .varfarin. cu zenba").unwrap(),
        "After discontinuation, warfarin's concentration no longer rises",
    );
    assert_false(
        &engine.query_holds("la .varfarin. cu ckape").unwrap(),
        "After discontinuation, warfarin's toxicity basis is gone",
    );
    assert_false(
        &engine.query_holds("la .varfarin. cu kajde").unwrap(),
        "After discontinuation, the warfarin alert is automatically withdrawn",
    );
    assert_false(
        &engine.query_holds("la .fenituin. cu kajde").unwrap(),
        "Discontinuing the shared inhibitor also clears the phenytoin alert",
    );
}

/// Witness extraction: enumerate which drugs are CYP2C9 substrates. The query
/// finds the entities bound to the existential variable across the fact store.
#[test]
fn ddi_witness_cyp2c9_substrates() {
    let engine = engine_with_ddi_corpus();
    let witnesses = engine.query_find_text("da se katna la .siptucin.").unwrap();
    // Collect the entity bound to `da` in each witness set.
    let mut substrates: Vec<String> = witnesses
        .iter()
        .filter_map(|set| {
            set.iter()
                .find(|b| b.variable == "da")
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
        substrates.iter().any(|s| s.contains("fenituin")),
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
    let n = engine
        .count_witnesses_text("la .adam. cu pilno da")
        .unwrap();
    assert_eq!(
        n, 2,
        "Adam's regimen contains exactly two drugs (warfarin + fluconazole)"
    );
}

/// Aggregation API: sum a numeric property across witnesses. Exercises
/// NibliEngine::aggregate_text over event-decomposed numeric facts.
#[test]
fn ddi_dose_sum_aggregation() {
    // klani(drug, amount): "drug measures <amount>". Numbers via `li`.
    let engine = engine_with_facts(&[
        "la .varfarin. cu klani li mu", // 5
        "la .fenituin. cu klani li ze", // 7
    ]);
    let total = engine
        .aggregate_text("da klani de", "de", EngineAggregateOp::Sum)
        .unwrap();
    assert_eq!(total, Some(12.0), "Summed dose across drugs should be 12");
}

/// Temporal reasoning: a present-tense alert holds; a past-tense query for the
/// same alert does not (tense discrimination), matching the engine's temporal
/// contract used elsewhere in the book.
#[test]
fn ddi_temporal_alert_discrimination() {
    let engine = engine_with_facts(&["ca la .varfarin. cu kajde"]);
    assert_true(
        &engine.query_holds("ca la .varfarin. cu kajde").unwrap(),
        "A present-tense alert holds",
    );
    assert_false(
        &engine.query_holds("pu la .varfarin. cu kajde").unwrap(),
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
    // canonically at the logji query_find boundary.
    //
    // NOTE: the corpus is asserted in the SAME order in both engines because
    // event-existential Skolem names (sk_N) are assertion-order dependent by
    // design; cross-order canonicalization is pinned at the logji level on
    // Skolem-free ground facts. An in-process pin is weaker than two true
    // processes (different global seeds), but the sort makes the order
    // seed-independent by construction.
    let lines = [
        "la .zod. cu gerku",
        "la .alis. cu gerku",
        "la .mik. cu gerku",
        "la .bob. cu gerku",
    ];
    let e1 = engine_with_facts(&lines);
    let e2 = engine_with_facts(&lines);

    let render = |engine: &NibliEngine| -> Vec<String> {
        engine
            .query_find_text("ma gerku")
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

// ════════════════════════════════════════════════════════════════════
// Surface-numeric evaluation (todo.md: event decomposition shadowed the
// numeric evaluators — every surface arithmetic/comparison query was FALSE)
// ════════════════════════════════════════════════════════════════════

#[test]
fn surface_numeric_pilji_true_and_false() {
    let engine = NibliEngine::new();
    assert_true(
        &engine.query_holds("li pa no cu pilji li re li mu").unwrap(),
        "10 = 2 × 5 must be derivable through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li pa pa cu pilji li re li mu").unwrap(),
        "11 = 2 × 5 must be FALSE through surface Lojban",
    );
}

#[test]
fn surface_numeric_sumji_dilcu() {
    let engine = NibliEngine::new();
    assert_true(
        &engine.query_holds("li mu cu sumji li re li ci").unwrap(),
        "5 = 2 + 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li xa cu sumji li re li ci").unwrap(),
        "6 = 2 + 3 must be FALSE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("li ci cu dilcu li xa li re").unwrap(),
        "3 = 6 / 2 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li ci cu dilcu li xa li no").unwrap(),
        "division by zero must be FALSE, not an error",
    );
}

#[test]
fn surface_numeric_comparison_zmadu_mleca_dunli() {
    let engine = NibliEngine::new();
    assert_true(
        &engine.query_holds("li mu cu zmadu li ci").unwrap(),
        "5 > 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li ci cu zmadu li mu").unwrap(),
        "3 > 5 must be FALSE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("li re cu mleca li ci").unwrap(),
        "2 < 3 must be TRUE through surface Lojban",
    );
    assert_true(
        &engine.query_holds("li ci cu dunli li ci").unwrap(),
        "3 == 3 must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li ci cu dunli li re").unwrap(),
        "3 == 2 must be FALSE through surface Lojban",
    );
}

#[test]
fn surface_numeric_negation() {
    let engine = NibliEngine::new();
    assert_true(
        &engine.query_holds("li ci na zmadu li mu").unwrap(),
        "NOT(3 > 5) must be TRUE through surface Lojban",
    );
    assert_false(
        &engine.query_holds("li mu na zmadu li ci").unwrap(),
        "NOT(5 > 3) must be FALSE through surface Lojban",
    );
}

#[test]
fn surface_numeric_traced_verdicts_agree() {
    // The traced path must agree with the untraced verdict (both evaluators
    // carry the numeric-group hook) and record a compute-check step.
    let engine = NibliEngine::new();
    let (verdict, trace, _json) = engine
        .query_text_with_proof("li pa no cu pilji li re li mu")
        .unwrap();
    assert_true(&verdict, "traced 10 = 2 × 5 must be TRUE");
    assert!(
        trace.contains("pilji"),
        "trace should mention the computed relation: {trace}"
    );
}
