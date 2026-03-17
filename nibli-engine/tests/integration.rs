//! Integration tests for the nibli-engine: full pipeline (parse → compile → reason).
//!
//! Each test creates a fresh NibliEngine, asserts Lojban text, and queries with proof.
//! No WASM, no HTTP — exercises gerna+smuni+logji directly via Rust crate calls.

use nibli_engine::NibliEngine;

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

// ─── Basic assertion and query ──────────────────────────────────────

#[test]
fn simple_assertion_and_query() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, trace, json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(holds, "Query for asserted fact should hold");
    assert!(!trace.is_empty(), "Proof trace should be non-empty");
    assert!(!json.is_empty(), "Proof JSON should be non-empty");
}

#[test]
fn simple_negation_query_false() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu barda").unwrap();
    assert!(!holds, "Query for unasserted fact should not hold");
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
    assert!(holds, "Direct fact should hold");

    // One-hop derivation: gerku → danlu
    let (holds, trace, _json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "One-hop derived fact should hold");
    assert!(
        trace.contains("Derived"),
        "Proof trace should show derivation"
    );

    // Two-hop derivation: gerku → danlu → citka
    let (holds, trace, _json) = engine.query_text_with_proof("la .adam. cu citka").unwrap();
    assert!(holds, "Two-hop derived fact should hold");
    assert!(
        trace.contains("Derived"),
        "Proof trace should show derivation chain"
    );
}

// ─── Temporal reasoning ─────────────────────────────────────────────

#[test]
fn temporal_past_assertion_and_query() {
    let engine = engine_with_facts(&["pu lo gerku cu barda"]);

    // Tensed query should hold
    let (holds, _trace, _json) = engine.query_text_with_proof("pu lo gerku cu barda").unwrap();
    assert!(holds, "Past-tensed query should hold");

    // Bare (untensed) query should NOT hold
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(!holds, "Bare query should not match past-tensed fact");
}

#[test]
fn temporal_tense_discrimination() {
    let engine = engine_with_facts(&["pu lo gerku cu barda"]);

    // Future tense should NOT match past tense
    let (holds, _trace, _json) = engine.query_text_with_proof("ba lo gerku cu barda").unwrap();
    assert!(!holds, "Future query should not match past-tensed fact");
}

// ─── Description opacity (le vs lo) ────────────────────────────────

#[test]
fn description_opacity_le_vs_lo() {
    let engine = engine_with_facts(&["le gerku cu barda"]);

    // le query should hold (opaque description)
    let (holds, _trace, _json) = engine.query_text_with_proof("le gerku cu barda").unwrap();
    assert!(holds, "le (opaque) query should hold");
}

#[test]
fn la_name_assertion() {
    let engine = engine_with_facts(&["la .adam. cu gerku"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("la .adam. cu gerku").unwrap();
    assert!(holds, "la name assertion should hold");
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
    assert!(
        result.is_err(),
        "Invalid query should produce an error"
    );
}

// ─── Proof trace structure ──────────────────────────────────────────

#[test]
fn proof_trace_contains_asserted_for_ground_fact() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, trace, json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(holds);
    assert!(
        trace.contains("Asserted"),
        "Ground fact proof should contain 'Asserted'"
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
    let engine = engine_with_facts(&[
        "ro lo gerku cu danlu",
        "la .adam. cu gerku",
    ]);
    let (_holds, _trace, json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("Proof JSON should parse");
    let steps = parsed["steps"].as_array().expect("steps should be array");
    assert!(
        steps.len() > 1,
        "Derived proof should have multiple steps"
    );
}

// ─── Engine reset ───────────────────────────────────────────────────

#[test]
fn reset_clears_knowledge_base() {
    let engine = engine_with_facts(&["lo gerku cu barda"]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(holds, "Fact should hold before reset");

    engine.reset();

    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(!holds, "Fact should not hold after reset");
}

// ─── Multiple facts ─────────────────────────────────────────────────

#[test]
fn multiple_independent_facts() {
    let engine = engine_with_facts(&[
        "lo gerku cu barda",
        "lo mlatu cu cmalu",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("lo gerku cu barda").unwrap();
    assert!(holds, "First fact should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu cmalu").unwrap();
    assert!(holds, "Second fact should hold");
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
    assert!(holds, "First sentence should hold");
    let (holds, _trace, _json) = engine.query_text_with_proof("lo mlatu cu cmalu").unwrap();
    assert!(holds, "Second sentence should hold");
}

// ─── Sentence connectives ───────────────────────────────────────────

#[test]
fn universal_rule_with_named_entity() {
    // Universal rules + named entity — the primary use case
    let engine = engine_with_facts(&[
        "ro lo gerku cu danlu",
        "la .adam. cu gerku",
    ]);
    let (holds, _trace, _json) = engine.query_text_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "Named entity should derive through universal rule");
}

// ─── Conversion (se) ────────────────────────────────────────────────

#[test]
fn se_conversion_assertion_and_query() {
    let engine = engine_with_facts(&["la .adam. cu se ponse lo gerku"]);
    let (holds, _trace, _json) = engine
        .query_text_with_proof("la .adam. cu se ponse lo gerku")
        .unwrap();
    assert!(holds, "se-converted assertion should be queryable");
}
