//! Two-node gossip smoke test.
//!
//! This is the foundational test: two nibli nodes, gossip propagation,
//! independent verification. The grammar is the gatekeeper.

use tavla::GossipNode;

/// Two-node gossip: assert on A, ingest on B, query B.
///
/// 1. Node A asserts "ro lo gerku cu danlu" (all dogs are animals)
/// 2. Node A asserts "la .adam. cu gerku" (Adam is a dog)
/// 3. Node A creates envelopes for both
/// 4. Node B ingests both envelopes
/// 5. Node B queries "la .adam. cu danlu" → TRUE (derived via backward chaining)
/// 6. Node B queries "la .adam. cu mlatu" → FALSE (no evidence)
/// 7. Proof trace from step 5 contains "Derived"
#[test]
fn two_node_gossip_propagation() {
    // ── Create two nodes ──
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // ── Node A asserts facts ──
    let env1 = node_a
        .assert_local("ro lo gerku cu danlu")
        .expect("Node A should assert universal rule");

    let env2 = node_a
        .assert_local("la .adam. cu gerku")
        .expect("Node A should assert ground fact");

    // Verify Node A has 2 envelopes in its log.
    assert_eq!(node_a.log_size(), 2, "Node A should have 2 envelopes");

    // ── Node B ingests both envelopes ──
    let result1 = node_b
        .ingest(env1)
        .expect("Node B should ingest envelope 1");
    assert!(
        result1.fact_id.is_some(),
        "Ingesting Lojban assertion should produce a fact ID"
    );

    let result2 = node_b
        .ingest(env2)
        .expect("Node B should ingest envelope 2");
    assert!(
        result2.fact_id.is_some(),
        "Ingesting Lojban assertion should produce a fact ID"
    );

    // Verify Node B has 2 envelopes in its log.
    assert_eq!(node_b.log_size(), 2, "Node B should have 2 envelopes");

    // ── Node B queries "la .adam. cu danlu" → should be TRUE ──
    let (holds, proof_text, _proof_json) = node_b
        .query_with_proof("la .adam. cu danlu")
        .expect("Node B should be able to query");
    assert!(
        holds,
        "Node B should derive 'adam is an animal' via backward chaining"
    );

    // ── Proof trace should contain "Derived" ──
    assert!(
        proof_text.contains("Derived"),
        "Proof trace should show derived reasoning, got:\n{}",
        proof_text
    );
    println!("Proof trace for 'la .adam. cu danlu':\n{}", proof_text);

    // ── Node B queries "la .adam. cu mlatu" → should be FALSE ──
    let (holds, _proof_text, _proof_json) = node_b
        .query_with_proof("la .adam. cu mlatu")
        .expect("Node B should be able to query");
    assert!(
        !holds,
        "Node B should NOT derive 'adam is a cat' — no evidence"
    );
}

/// Dedup test: ingesting the same envelope twice should be idempotent.
#[test]
fn dedup_prevents_double_ingest() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let env = node_a
        .assert_local("la .adam. cu gerku")
        .expect("Should assert");

    // Ingest once.
    let r1 = node_b.ingest(env.clone()).expect("First ingest");
    assert!(r1.fact_id.is_some());

    // Ingest same envelope again — should be deduped.
    let r2 = node_b.ingest(env).expect("Second ingest (dedup)");
    assert!(
        r2.fact_id.is_none(),
        "Duplicate envelope should be skipped (no new fact)"
    );

    assert_eq!(node_b.log_size(), 1, "Log should have 1 envelope, not 2");
}

/// Vector clock merge: after ingestion, B's clock should reflect A's state.
#[test]
fn vector_clock_merge_on_ingest() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts two facts — its clock should be alis:2.
    let _env1 = node_a.assert_local("la .adam. cu gerku").unwrap();
    let env2 = node_a.assert_local("la .adam. cu danlu").unwrap();

    // B's clock is empty before ingest.
    assert!(
        node_b.get_clock().entries.is_empty(),
        "B's clock should be empty"
    );

    // B ingests A's second envelope (clock carries alis:2).
    node_b.ingest(env2).unwrap();

    // B's clock should now have alis >= 2.
    let b_alis = node_b.get_clock().entries.get("alis").copied().unwrap_or(0);
    assert!(
        b_alis >= 2,
        "After ingest, B's clock for alis should be >= 2, got {}",
        b_alis
    );
}

/// Invalid Lojban should be rejected by gerna on ingest.
#[test]
fn invalid_lojban_rejected_on_ingest() {
    let _node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // Create an envelope manually with invalid Lojban.
    // We can't use assert_local because it would fail on node_a too.
    // Instead, craft a raw envelope.
    let bad_envelope = tavla::Envelope {
        id: "bad123".to_string(),
        author: "alis".to_string(),
        clock: tavla::VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("this is not valid lojban at all xyz".to_string()),
        stance: tavla::EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2026-03-20T00:00:00Z".to_string(),
        sig: vec![],
    };

    let result = node_b.ingest(bad_envelope);
    assert!(
        result.is_err(),
        "Invalid Lojban should be rejected by gerna: {:?}",
        result
    );
}
