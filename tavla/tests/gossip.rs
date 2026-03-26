//! Gossip integration tests.
//!
//! Tests CRDT log, vector clocks, anti-entropy sync,
//! retraction tombstones, KB rebuild, epidemic propagation,
//! trust-as-knowledge, contradiction detection, and envelope expiration.

use tavla::{EpistemicStance, GossipNode, TrustPolicy, VectorClock};
use chrono;

// ─── Basic gossip (from Prompt 1) ────────────────────────────────

/// Two-node gossip: assert on A, ingest on B, query B.
#[test]
fn two_node_gossip_propagation() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let env1 = node_a
        .assert_local("ro lo gerku cu danlu")
        .expect("Node A should assert universal rule");

    let env2 = node_a
        .assert_local("la .adam. cu gerku")
        .expect("Node A should assert ground fact");

    assert_eq!(node_a.log_size(), 2, "Node A should have 2 envelopes");

    let result1 = node_b
        .ingest(env1)
        .expect("Node B should ingest envelope 1");
    assert!(result1.fact_id.is_some());

    let result2 = node_b
        .ingest(env2)
        .expect("Node B should ingest envelope 2");
    assert!(result2.fact_id.is_some());

    assert_eq!(node_b.log_size(), 2, "Node B should have 2 envelopes");

    let (holds, proof_text, _) = node_b
        .query_with_proof("la .adam. cu danlu")
        .expect("Node B should be able to query");
    assert!(holds, "Node B should derive 'adam is an animal'");
    println!("Proof trace for 'la .adam. cu danlu':\n{}", proof_text);
    assert!(proof_text.contains("Rule ("), "expected backward-chaining rule derivation in proof text:\n{}", proof_text);

    let (holds, _, _) = node_b
        .query_with_proof("la .adam. cu mlatu")
        .expect("Node B should be able to query");
    assert!(!holds, "Node B should NOT derive 'adam is a cat'");
}

/// Dedup test: ingesting the same envelope twice should be idempotent.
#[test]
fn dedup_prevents_double_ingest() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let env = node_a
        .assert_local("la .adam. cu gerku")
        .expect("Should assert");

    let r1 = node_b.ingest(env.clone()).expect("First ingest");
    assert!(r1.fact_id.is_some());

    let r2 = node_b.ingest(env).expect("Second ingest (dedup)");
    assert!(r2.fact_id.is_none(), "Duplicate should be skipped");

    assert_eq!(node_b.log_size(), 1, "Log should have 1 envelope, not 2");
    assert_eq!(
        node_b.active_count(),
        1,
        "Duplicate ingest must not create extra active facts"
    );

    let (holds, _, _) = node_b
        .query_with_proof("la .adam. cu gerku")
        .expect("Deduplicated fact should remain queryable");
    assert!(
        holds,
        "Duplicate ingest should leave one queryable fact, not zero or many"
    );
}

/// Vector clock merge: after ingestion, B's clock should reflect A's state.
#[test]
fn vector_clock_merge_on_ingest() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let _env1 = node_a.assert_local("la .adam. cu gerku").unwrap();
    let env2 = node_a.assert_local("la .adam. cu danlu").unwrap();

    assert!(node_b.get_clock().entries.is_empty());

    node_b.ingest(env2).unwrap();

    let b_alis = node_b.get_clock().entries.get("alis").copied().unwrap_or(0);
    assert!(
        b_alis >= 2,
        "B's clock for alis should be >= 2, got {b_alis}"
    );
}

/// Invalid Lojban should be rejected by gerna on ingest.
#[test]
fn invalid_lojban_rejected_on_ingest() {
    let _node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let bad_envelope = tavla::Envelope {
        id: "bad123".to_string(),
        author: "alis".to_string(),
        clock: tavla::VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("this is not valid lojban at all xyz".to_string()),
        stance: tavla::EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2026-03-20T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };

    let result = node_b.ingest(bad_envelope);
    assert!(
        result.is_err(),
        "Invalid Lojban should be rejected: {:?}",
        result
    );
}

// ─── CRDT log tests ──────────────────────────────────────────────

/// OR-Set CRDT: retraction creates tombstone, active_assertions excludes it.
#[test]
fn crdt_retraction_tombstones() {
    let mut node = GossipNode::new("alis");

    let env1 = node.assert_local("la .adam. cu gerku").unwrap();
    let _env2 = node.assert_local("la .adam. cu danlu").unwrap();

    assert_eq!(node.active_count(), 2);

    // Retract the first assertion.
    let tombstone = node.retract_local(&env1.id).unwrap();
    assert!(matches!(tombstone.op, tavla::GossipOp::Retract(_)));

    // CRDT log has 3 envelopes (2 assertions + 1 retraction).
    assert_eq!(node.log_size(), 3);
    // But only 1 active assertion remains.
    assert_eq!(node.active_count(), 1);

    // The retracted fact should no longer be in the KB.
    // After rebuild, only "la .adam. cu danlu" survives.
    let (holds, _, _) = node.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "Non-retracted fact should still hold");
}

/// Retraction propagates via ingest.
#[test]
fn retraction_propagates_to_peer() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts and B ingests.
    let env1 = node_a.assert_local("la .adam. cu gerku").unwrap();
    node_b.ingest(env1.clone()).unwrap();

    assert_eq!(node_b.active_count(), 1);

    // A retracts and B ingests the tombstone.
    let tombstone = node_a.retract_local(&env1.id).unwrap();
    let result = node_b.ingest(tombstone).unwrap();
    assert!(result.was_retraction);

    // B should have 0 active assertions after retraction.
    assert_eq!(node_b.active_count(), 0);

    let (holds, _, _) = node_b
        .query_with_proof("la .adam. cu gerku")
        .expect("Peer should still be queryable after retraction");
    assert!(
        !holds,
        "Retracted remote fact should no longer hold in the peer KB"
    );
}

/// KB rebuild from CRDT log restores consistent state.
#[test]
fn kb_rebuild_from_crdt_log() {
    let mut node = GossipNode::new("alis");

    node.assert_local("ro lo gerku cu danlu").unwrap();
    node.assert_local("la .adam. cu gerku").unwrap();

    // Verify derivation works.
    let (holds, _, _) = node.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds);

    // Reset KB (simulating corruption or restart).
    node.reset();
    let (holds, _, _) = node.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(!holds, "KB should be empty after reset");

    // Rebuild from CRDT log.
    node.rebuild_kb();
    let (holds, _, _) = node.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "KB should be restored after rebuild");
}

#[test]
fn synced_retraction_survives_reset_and_rebuild() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let env1 = node_a.assert_local("la .adam. cu gerku").unwrap();
    let env2 = node_a.assert_local("la .adam. cu danlu").unwrap();
    node_b.ingest(env1.clone()).unwrap();
    node_b.ingest(env2).unwrap();

    let tombstone = node_a.retract_local(&env1.id).unwrap();
    node_b.ingest(tombstone).unwrap();

    let (holds, _, _) = node_b.query_with_proof("la .adam. cu gerku").unwrap();
    assert!(
        !holds,
        "Synced tombstone should retract the fact before rebuild"
    );
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(
        holds,
        "Independent surviving facts should still hold before rebuild"
    );

    node_b.reset();
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(!holds, "Reset should empty the KB before replay");

    node_b.rebuild_kb();
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu gerku").unwrap();
    assert!(
        !holds,
        "Rebuild must not replay tombstoned facts from the synced CRDT log"
    );
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "Rebuild should replay surviving synced assertions");
}

// ─── Vector clock dominance ──────────────────────────────────────

/// VectorClock::dominates — correct causal ordering.
#[test]
fn vector_clock_dominates() {
    let mut a = VectorClock::new();
    let mut b = VectorClock::new();

    // Empty clocks dominate each other.
    assert!(a.dominates(&b));
    assert!(b.dominates(&a));

    a.tick("alis");
    // a={alis:1} dominates b={} — we've seen everything b has.
    assert!(a.dominates(&b));
    // b={} does NOT dominate a={alis:1} — b hasn't seen alis's event.
    assert!(!b.dominates(&a));

    b.tick("bob");
    // a={alis:1} vs b={bob:1} — neither dominates (concurrent).
    assert!(!a.dominates(&b));
    assert!(!b.dominates(&a));

    a.merge(&b);
    // a={alis:1, bob:1} dominates b={bob:1}.
    assert!(a.dominates(&b));
}

// ─── Sync diff ───────────────────────────────────────────────────

/// sync_diff returns envelopes the peer hasn't seen.
#[test]
fn sync_diff_returns_missing_envelopes() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts 3 facts.
    node_a.assert_local("la .adam. cu gerku").unwrap();
    node_a.assert_local("la .adam. cu danlu").unwrap();
    node_a.assert_local("la .adam. cu mlatu").unwrap();

    // B has seen nothing — empty clock.
    let diff = node_a.sync_diff(node_b.get_clock());
    assert_eq!(diff.len(), 3, "B should need all 3 envelopes");

    // B ingests the first two via sync.
    node_b.ingest(diff[0].clone()).unwrap();
    node_b.ingest(diff[1].clone()).unwrap();

    // Now B has a partial clock. Ask A for the remaining diff.
    let diff2 = node_a.sync_diff(node_b.get_clock());
    assert_eq!(diff2.len(), 1, "B should need only 1 more envelope");
}

/// Sync diff respects causal order (lower clock sum first).
#[test]
fn sync_diff_causal_order() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts facts in order.
    let _e1 = node_a.assert_local("la .adam. cu gerku").unwrap();
    let _e2 = node_a.assert_local("la .adam. cu danlu").unwrap();

    // B asserts something independently.
    let _e3 = node_b.assert_local("la .adam. cu mlatu").unwrap();

    // Merge A's log into B's CRDT.
    let peer_clock = VectorClock::new(); // pretend peer has nothing
    let diff = node_a.sync_diff(&peer_clock);

    // Should be in causal order: e1 (clock sum 1) before e2 (clock sum 2).
    assert!(diff[0].clock.sum() <= diff[1].clock.sum());
}

// ─── 3-node epidemic gossip ──────────────────────────────────────

/// Three-node epidemic gossip: A↔B↔C (A does NOT peer with C).
///
/// Phase 1: A asserts facts → propagate A→B→C
/// Phase 2: "Kill" B (simulate by not using it), A and C assert independently
/// Phase 3: "Restart" B, sync from both A and C → B gets everything
#[test]
fn three_node_epidemic_gossip() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");
    let mut node_c = GossipNode::new("carol");

    // ── Phase 1: A asserts, propagates A→B→C ──

    let rule = node_a.assert_local("ro lo gerku cu danlu").unwrap();
    let fact_a = node_a.assert_local("la .adam. cu gerku").unwrap();

    // B ingests from A (A↔B link).
    node_b.ingest(rule.clone()).unwrap();
    node_b.ingest(fact_a.clone()).unwrap();

    // B verifies derivation.
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(
        holds,
        "B should derive 'adam is danlu' after syncing from A"
    );

    // C ingests from B (B↔C link) — epidemic: A→B→C.
    // B sends its sync_diff to C.
    let diff_b_to_c = node_b.sync_diff(node_c.get_clock());
    assert_eq!(diff_b_to_c.len(), 2, "B should send 2 envelopes to C");
    for env in diff_b_to_c {
        node_c.ingest(env).unwrap();
    }

    // C verifies derivation — facts propagated A→B→C.
    let (holds, _, _) = node_c.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "C should derive 'adam is danlu' via epidemic A→B→C");

    // ── Phase 2: "Kill" B. A and C assert independently. ──

    // A asserts more.
    let _fact_a2 = node_a.assert_local("la .adam. cu mlatu").unwrap();

    // C asserts independently.
    let _fact_c = node_c.assert_local("la .adam. cu finpe").unwrap();

    // B is "dead" — doesn't see any of these.
    assert_eq!(node_b.log_size(), 2, "B hasn't seen new facts");

    // ── Phase 3: "Restart" B. Sync from both A and C. ──

    // B syncs from A.
    let diff_a_to_b = node_a.sync_diff(node_b.get_clock());
    assert!(
        !diff_a_to_b.is_empty(),
        "A should have at least 1 new envelope for B"
    );
    for env in diff_a_to_b {
        node_b.ingest(env).unwrap();
    }

    // B syncs from C.
    let diff_c_to_b = node_c.sync_diff(node_b.get_clock());
    assert!(
        !diff_c_to_b.is_empty(),
        "C should have at least 1 new envelope for B"
    );
    for env in diff_c_to_b {
        node_b.ingest(env).unwrap();
    }

    // B should now have ALL facts from A, B's own, and C.
    // A: rule, fact_a, fact_a2 (3 envelopes)
    // C: fact_c (1 envelope)
    // B originally had: rule, fact_a (2 envelopes)
    // After sync: rule, fact_a, fact_a2, fact_c (4 envelopes)
    assert_eq!(
        node_b.log_size(),
        4,
        "B should have 4 envelopes after syncing from both A and C"
    );

    // B can query all the facts.
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu mlatu").unwrap();
    assert!(holds, "B should have A's new fact 'adam is mlatu'");

    let (holds, _, _) = node_b.query_with_proof("la .adam. cu finpe").unwrap();
    assert!(holds, "B should have C's fact 'adam is finpe'");

    // The original derivation should still work.
    let (holds, _, _) = node_b.query_with_proof("la .adam. cu danlu").unwrap();
    assert!(holds, "B should still derive 'adam is danlu'");

    println!("3-node epidemic gossip: A→B→C propagation + partition recovery verified");
}

/// Retraction across 3 nodes: A retracts, B and C see tombstone.
#[test]
fn three_node_retraction_propagation() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");
    let mut node_c = GossipNode::new("carol");

    // A asserts, B and C ingest.
    let env = node_a.assert_local("la .adam. cu gerku").unwrap();
    let env_id = env.id.clone();
    node_b.ingest(env.clone()).unwrap();
    node_c.ingest(env).unwrap();

    assert_eq!(node_b.active_count(), 1);
    assert_eq!(node_c.active_count(), 1);

    // A retracts.
    let tombstone = node_a.retract_local(&env_id).unwrap();

    // B ingests tombstone directly (A↔B link).
    node_b.ingest(tombstone.clone()).unwrap();
    assert_eq!(
        node_b.active_count(),
        0,
        "B should have 0 active after retraction"
    );

    // C gets tombstone from B (B↔C link, epidemic).
    let diff = node_b.sync_diff(node_c.get_clock());
    for e in diff {
        node_c.ingest(e).unwrap();
    }
    assert_eq!(
        node_c.active_count(),
        0,
        "C should have 0 active after retraction"
    );
}

/// CRDT log merge is idempotent — merging the same log twice changes nothing.
#[test]
fn crdt_merge_idempotent() {
    let mut log_a = tavla::CrdtLog::new();
    let mut log_b = tavla::CrdtLog::new();

    let env = tavla::Envelope {
        id: "test123".to_string(),
        author: "alis".to_string(),
        clock: VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu gerku".to_string()),
        stance: tavla::EpistemicStance::Deduced,
        topics: vec!["gerku".to_string()],
        timestamp: "2026-03-20T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };

    log_a.insert(env.clone());
    log_b.insert(env);

    // Merge B into A — should add nothing (already present).
    let new = log_a.merge(&log_b);
    assert!(new.is_empty(), "Merging duplicate log should add nothing");
    assert_eq!(log_a.len(), 1);
}

// ─── Trust as knowledge ─────────────────────────────────────────

/// TrustRequired: rejects untrusted, accepts after :trust, rejects after :distrust.
#[test]
fn trust_required_lifecycle() {
    let mut node_a = GossipNode::with_policy("alis", TrustPolicy::TrustRequired);
    let mut node_b = GossipNode::new("bob");

    // B asserts a fact.
    let env = node_b.assert_local("la .adam. cu gerku").unwrap();

    // A rejects — B is untrusted.
    let result = node_a.ingest(env.clone()).unwrap();
    assert!(
        result.was_rejected,
        "A should reject B's envelope (untrusted)"
    );
    assert!(result.fact_id.is_none());
    assert_eq!(node_a.active_count(), 0);

    // A trusts B.
    node_a.trust("bob").unwrap();

    // Now A should accept B's envelope.
    let result2 = node_a.ingest(env.clone()).unwrap();
    assert!(
        !result2.was_rejected,
        "A should accept B's envelope after trust"
    );
    assert!(result2.fact_id.is_some());
    assert_eq!(node_a.active_count(), 2); // trust assertion + bob's fact

    // A distrusts B.
    node_a.distrust("bob").unwrap();

    // Verify the trust assertion is gone.
    let trusts = node_a.trust_list();
    assert!(trusts.is_empty(), "No trust assertions after distrust");

    // New facts from B should be rejected again.
    let env2 = node_b.assert_local("la .adam. cu danlu").unwrap();
    let result3 = node_a.ingest(env2).unwrap();
    assert!(
        result3.was_rejected,
        "A should reject B again after distrust"
    );
}

/// QuarantineUntrusted: accepts but quarantines untrusted envelopes.
#[test]
fn quarantine_untrusted_policy() {
    let mut node_a = GossipNode::with_policy("alis", TrustPolicy::QuarantineUntrusted);
    let mut node_b = GossipNode::new("bob");

    let env = node_b.assert_local("la .adam. cu gerku").unwrap();

    // A quarantines — B is untrusted.
    let result = node_a.ingest(env).unwrap();
    assert!(result.was_quarantined, "Should be quarantined");
    assert!(!result.was_rejected, "Should NOT be rejected");
    assert!(result.fact_id.is_none(), "Quarantined facts not in KB");

    // Verify quarantine counts.
    assert_eq!(node_a.quarantined_count(), 1);
    assert_eq!(node_a.active_count(), 0);

    let (holds, _, _) = node_a
        .query_with_proof("la .adam. cu gerku")
        .expect("Quarantined KB should still be queryable");
    assert!(
        !holds,
        "Quarantined envelopes must stay out of the KB until trust promotes them"
    );

    // CRDT log has the envelope.
    assert_eq!(node_a.log_size(), 1);

    // A trusts B — quarantined envelopes should be promoted.
    node_a.trust("bob").unwrap();
    node_a.reevaluate_quarantine();

    // Now the quarantined fact should be active.
    assert_eq!(node_a.quarantined_count(), 0);
    assert_eq!(node_a.active_count(), 2); // trust + bob's fact

    // The fact should now be in the KB.
    let (holds, _, _) = node_a.query_with_proof("la .adam. cu gerku").unwrap();
    assert!(holds, "Promoted fact should be queryable");
}

/// AcceptAll: accepts everything regardless of trust.
#[test]
fn accept_all_policy() {
    let mut node_a = GossipNode::with_policy("alis", TrustPolicy::AcceptAll);
    let mut node_b = GossipNode::new("bob");

    let env = node_b.assert_local("la .adam. cu gerku").unwrap();

    let result = node_a.ingest(env).unwrap();
    assert!(!result.was_rejected);
    assert!(!result.was_quarantined);
    assert!(result.fact_id.is_some());
}

/// Self-authored envelopes always trusted regardless of policy.
#[test]
fn self_trust_always() {
    let mut node = GossipNode::with_policy("alis", TrustPolicy::TrustRequired);

    // Self-asserted should work.
    let result = node.assert_local("la .adam. cu gerku");
    assert!(result.is_ok(), "Self-asserted should always work");
    assert_eq!(node.active_count(), 1);
}

/// Trust list shows lacri assertions.
#[test]
fn trust_list_shows_lacri() {
    let mut node = GossipNode::new("alis");

    node.trust("bob").unwrap();
    node.trust_topic("carol", "gerku").unwrap();

    let trusts = node.trust_list();
    assert_eq!(trusts.len(), 2);
    assert!(trusts.iter().any(|t| t.contains("bob")));
    assert!(trusts.iter().any(|t| t.contains("carol")));
}

// ─── Contradiction detection ─────────────────────────────────

/// Contradiction detected when asserting a fact whose negation is already in KB.
#[test]
fn contradiction_detected_on_negation() {
    let mut node = GossipNode::new("alis");

    // Assert a positive fact.
    node.assert_local("lo gerku cu barda").unwrap();

    // Assert the negation — should detect contradiction but still assert (paraconsistent).
    node.assert_local("lo gerku cu na barda").unwrap();

    // Both assertions should be in the KB.
    assert_eq!(node.active_count(), 2);

    // A contradiction should have been detected.
    assert_eq!(
        node.unresolved_contradiction_count(),
        1,
        "Should detect 1 contradiction"
    );

    let contras = node.contradictions();
    assert_eq!(contras.len(), 1);
    assert_eq!(contras[0].assertion, "lo gerku cu na barda");
    assert!(!contras[0].resolved);
}

/// Two nodes assert contradictory facts, both detect contradiction on ingest.
#[test]
fn two_node_contradiction_on_ingest() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts positive.
    let env_a = node_a.assert_local("lo gerku cu barda").unwrap();
    // B asserts negative.
    let env_b = node_b.assert_local("lo gerku cu na barda").unwrap();

    // A ingests B's negation — should detect contradiction.
    let result_a = node_a.ingest(env_b).unwrap();
    assert!(
        result_a.contradiction.is_some(),
        "A should detect contradiction from B's assertion"
    );
    assert_eq!(node_a.unresolved_contradiction_count(), 1);

    // B ingests A's positive — should detect contradiction.
    let result_b = node_b.ingest(env_a).unwrap();
    assert!(
        result_b.contradiction.is_some(),
        "B should detect contradiction from A's assertion"
    );
    assert_eq!(node_b.unresolved_contradiction_count(), 1);
}

/// Resolve a contradiction by ID.
#[test]
fn resolve_contradiction() {
    let mut node = GossipNode::new("alis");

    node.assert_local("lo gerku cu barda").unwrap();
    node.assert_local("lo gerku cu na barda").unwrap();

    assert_eq!(node.unresolved_contradiction_count(), 1);

    // Resolve.
    node.resolve_contradiction(1).unwrap();
    assert_eq!(node.unresolved_contradiction_count(), 0);

    // All contradictions still tracked (but resolved).
    assert_eq!(node.contradictions().len(), 1);
    assert!(node.contradictions()[0].resolved);

    // Double resolve should error.
    assert!(node.resolve_contradiction(1).is_err());
}

/// No contradiction when asserting non-contradictory facts.
#[test]
fn no_contradiction_on_compatible_facts() {
    let mut node = GossipNode::new("alis");

    node.assert_local("lo gerku cu barda").unwrap();
    node.assert_local("lo mlatu cu cmalu").unwrap();

    assert_eq!(
        node.unresolved_contradiction_count(),
        0,
        "Compatible facts should not trigger contradictions"
    );
}

// ─── Epistemic stances ───────────────────────────────────────

/// Local assertion defaults to Deduced (ja'o).
#[test]
fn local_assertion_defaults_to_deduced() {
    let mut node = GossipNode::new("alis");
    let env = node.assert_local("la .adam. cu gerku").unwrap();
    assert_eq!(env.stance, EpistemicStance::Deduced);
    assert_eq!(env.stance.cmavo(), "ja'o");
}

/// Assert with explicit stance (Expected / ba'a).
#[test]
fn assert_with_expected_stance() {
    let mut node = GossipNode::new("alis");
    let env = node
        .assert_local_with_stance("lo trena cu clira", EpistemicStance::Expected)
        .unwrap();
    assert_eq!(env.stance, EpistemicStance::Expected);
    assert_eq!(env.stance.cmavo(), "ba'a");
}

/// Assert with Opinion stance (pe'i).
#[test]
fn assert_with_opinion_stance() {
    let mut node = GossipNode::new("alis");
    let env = node
        .assert_local_with_stance("lo gerku cu melbi", EpistemicStance::Opinion)
        .unwrap();
    assert_eq!(env.stance, EpistemicStance::Opinion);
    assert_eq!(env.stance.cmavo(), "pe'i");
}

/// Confidence ordering: Deduced > Expected > Opinion > Hearsay.
#[test]
fn stance_confidence_ordering() {
    assert!(EpistemicStance::Deduced.confidence() > EpistemicStance::Expected.confidence());
    assert!(EpistemicStance::Expected.confidence() > EpistemicStance::Opinion.confidence());
    assert!(EpistemicStance::Opinion.confidence() > EpistemicStance::Hearsay.confidence());
}

/// Epistemic sources track author and stance from CRDT log.
#[test]
fn epistemic_sources_from_crdt_log() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts as Deduced.
    let env_a = node_a.assert_local("la .adam. cu gerku").unwrap();

    // B asserts the same fact as Expected.
    let env_b = node_b
        .assert_local_with_stance("la .adam. cu gerku", EpistemicStance::Expected)
        .unwrap();

    // Create a node C that ingests both.
    let mut node_c = GossipNode::new("carol");
    node_c.ingest_from(env_a, Some("alis")).unwrap();
    node_c.ingest_from(env_b, Some("bob")).unwrap();

    let sources = node_c.epistemic_sources("la .adam. cu gerku");
    assert_eq!(sources.len(), 2, "Should have 2 sources");

    // Find A's source — should be Deduced, via alis.
    let src_a = sources.iter().find(|s| s.author == "alis").unwrap();
    assert_eq!(src_a.stance, EpistemicStance::Deduced);
    assert_eq!(src_a.via.as_deref(), Some("alis"));

    // Find B's source — should be Expected, via bob.
    let src_b = sources.iter().find(|s| s.author == "bob").unwrap();
    assert_eq!(src_b.stance, EpistemicStance::Expected);
    assert_eq!(src_b.via.as_deref(), Some("bob"));

    // Strongest source should be A (Deduced > Expected).
    let strongest = GossipNode::strongest_source(&sources).unwrap();
    assert_eq!(strongest.author, "alis");
    assert_eq!(strongest.stance, EpistemicStance::Deduced);
}

/// Self-authored assertions have no relay (via = None).
#[test]
fn self_authored_has_no_relay() {
    let mut node = GossipNode::new("alis");
    node.assert_local("la .adam. cu gerku").unwrap();

    let sources = node.epistemic_sources("la .adam. cu gerku");
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].author, "alis");
    assert!(
        sources[0].via.is_none(),
        "Self-authored should have no relay"
    );
}

/// Ingested envelope tracks relay provenance.
#[test]
fn ingest_tracks_relay_via() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    let env = node_a.assert_local("la .adam. cu gerku").unwrap();

    // B ingests from A (relayed via "alis" peer connection).
    node_b.ingest_from(env, Some("alis")).unwrap();

    let sources = node_b.epistemic_sources("la .adam. cu gerku");
    assert_eq!(sources.len(), 1);
    assert_eq!(sources[0].author, "alis");
    assert_eq!(sources[0].via.as_deref(), Some("alis"));
}

/// Distrust removes trust and triggers re-evaluation.
#[test]
fn distrust_revokes_and_reevaluates() {
    let mut node_a = GossipNode::with_policy("alis", TrustPolicy::QuarantineUntrusted);
    let mut node_b = GossipNode::new("bob");

    // Trust bob first.
    node_a.trust("bob").unwrap();

    // Bob's fact accepted (trusted).
    let env = node_b.assert_local("la .adam. cu gerku").unwrap();
    let result = node_a.ingest(env).unwrap();
    assert!(!result.was_quarantined);
    assert!(result.fact_id.is_some());

    // Now distrust bob — his facts should be quarantined on rebuild.
    node_a.distrust("bob").unwrap();

    // After distrust + rebuild, bob's fact is quarantined.
    // The distrust method already calls rebuild_kb.
    // Bob's fact is now from an untrusted source.
    // We need to reevaluate.
    node_a.reevaluate_quarantine();

    assert_eq!(
        node_a.quarantined_count(),
        1,
        "Bob's fact should be quarantined after distrust"
    );
}

// ─── Signature verification ─────────────────────────────────────

/// Signed envelopes from known peers are accepted.
#[test]
fn signed_envelope_accepted_from_known_peer() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // Register each other's public keys.
    node_b.register_peer_key("alis", node_a.public_key());

    // Alis asserts (auto-signed).
    let env = node_a.assert_local("la .adam. cu gerku").unwrap();

    // Bob ingests — should succeed (valid signature, known key).
    let result = node_b.ingest(env).unwrap();
    assert!(result.fact_id.is_some(), "signed envelope should be accepted");
    assert!(!result.was_rejected);
}

/// Forged envelopes (wrong signature) are rejected when policy is RequireSigned.
#[test]
fn forged_envelope_rejected() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");
    node_b.sig_policy = tavla::SignaturePolicy::RequireSigned;

    // Register alis's real public key.
    node_b.register_peer_key("alis", node_a.public_key());

    // Alis asserts (auto-signed with her key).
    let mut env = node_a.assert_local("la .adam. cu gerku").unwrap();

    // Tamper with the envelope content (change the text in the op).
    env.op = tavla::GossipOp::AssertLojban("la .adam. cu mlatu".to_string());
    // The sig is now invalid because canonical_bytes() changed.

    let result = node_b.ingest(env).unwrap();
    assert!(result.was_rejected, "forged envelope should be rejected");
    assert!(result.fact_id.is_none());
}

/// Unsigned envelopes accepted under AcceptUnsigned policy (default).
#[test]
fn unsigned_envelope_accepted_under_accept_unsigned_policy() {
    let mut node_b = GossipNode::new("bob");

    let unsigned_env = tavla::Envelope {
        id: "unsigned123".to_string(),
        author: "alis".to_string(),
        clock: tavla::VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu gerku".to_string()),
        stance: tavla::EpistemicStance::Deduced,
        topics: vec!["gerku".to_string()],
        timestamp: "2026-03-25T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };

    let result = node_b.ingest(unsigned_env).unwrap();
    assert!(result.fact_id.is_some(), "unsigned should be accepted under AcceptUnsigned");
}

/// Unsigned envelopes rejected under RequireSigned policy.
#[test]
fn unsigned_envelope_rejected_under_require_signed_policy() {
    let mut node_b = GossipNode::new("bob");
    node_b.sig_policy = tavla::SignaturePolicy::RequireSigned;

    let unsigned_env = tavla::Envelope {
        id: "unsigned456".to_string(),
        author: "alis".to_string(),
        clock: tavla::VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu gerku".to_string()),
        stance: tavla::EpistemicStance::Deduced,
        topics: vec!["gerku".to_string()],
        timestamp: "2026-03-25T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };

    let result = node_b.ingest(unsigned_env).unwrap();
    assert!(result.was_rejected, "unsigned should be rejected under RequireSigned");
}

// ─── Tombstone conflict handling ──────────────────────────────────

/// Direct CrdtLog::merge() preserves tombstones from the peer.
#[test]
fn merge_preserves_tombstones_from_peer() {
    let mut log_a = tavla::CrdtLog::new();
    let mut log_b = tavla::CrdtLog::new();

    // Both logs have the same assertion envelope.
    let env = tavla::Envelope {
        id: "fact1".to_string(),
        author: "alis".to_string(),
        clock: VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu gerku".to_string()),
        stance: EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2026-03-26T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };
    log_a.insert(env.clone());
    log_b.insert(env);

    // A retracts the fact (creates retraction envelope + tombstone).
    let retract_env = tavla::Envelope {
        id: "retract1".to_string(),
        author: "alis".to_string(),
        clock: VectorClock::new(),
        op: tavla::GossipOp::Retract("fact1".to_string()),
        stance: EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2026-03-26T00:01:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };
    log_a.insert(retract_env);
    assert!(log_a.tombstones.contains("fact1"));

    // B has no tombstone yet.
    assert!(!log_b.tombstones.contains("fact1"));

    // Merge A into B — tombstone should propagate.
    log_b.merge(&log_a);
    assert!(
        log_b.tombstones.contains("fact1"),
        "Tombstone should propagate via merge"
    );

    // Active assertions on B should exclude the tombstoned fact.
    let active = log_b.active_assertions();
    assert!(active.is_empty(), "Tombstoned fact should not be active after merge");
}

/// Concurrent retraction: two nodes independently retract the same fact, then merge.
#[test]
fn concurrent_retraction_same_envelope() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // A asserts, B ingests.
    let env = node_a.assert_local("la .adam. cu gerku").unwrap();
    node_b.ingest(env.clone()).unwrap();
    assert_eq!(node_a.active_count(), 1);
    assert_eq!(node_b.active_count(), 1);

    // Both independently retract the same fact.
    let retract_a = node_a.retract_local(&env.id).unwrap();
    let retract_b = node_b.retract_local(&env.id).unwrap();

    // Both should have 0 active assertions locally.
    assert_eq!(node_a.active_count(), 0);
    assert_eq!(node_b.active_count(), 0);

    // Cross-ingest the retractions (each gets the other's retraction envelope).
    node_b.ingest(retract_a).unwrap();
    node_a.ingest(retract_b).unwrap();

    // Fact should remain retracted on both after cross-merge.
    assert_eq!(node_a.active_count(), 0, "A should have 0 active after cross-merge");
    assert_eq!(node_b.active_count(), 0, "B should have 0 active after cross-merge");
}

/// Partition recovery: A retracts during partition, B syncs after healing.
#[test]
fn partition_recovery_tombstone_via_sync() {
    let mut node_a = GossipNode::new("alis");
    let mut node_b = GossipNode::new("bob");

    // Pre-partition: A asserts, B ingests.
    let env = node_a.assert_local("la .adam. cu gerku").unwrap();
    node_b.ingest(env.clone()).unwrap();
    assert_eq!(node_b.active_count(), 1);

    // Partition: A retracts, B doesn't see it.
    let _retract = node_a.retract_local(&env.id).unwrap();
    assert_eq!(node_a.active_count(), 0);
    assert_eq!(node_b.active_count(), 1); // B still has the fact

    // Partition heals: B syncs from A via sync_diff.
    let diff = node_a.sync_diff(&node_b.get_clock());
    for envelope in diff {
        node_b.ingest(envelope).unwrap();
    }

    // B should now have the retraction.
    assert_eq!(
        node_b.active_count(),
        0,
        "B should have 0 active after partition recovery sync"
    );
}

// ─── Envelope expiration ──────────────────────────────────────────

/// CrdtLog::expire_before removes old envelopes and tombstones expired assertions.
#[test]
fn expire_before_removes_old_envelopes() {
    let mut log = tavla::CrdtLog::new();

    // Insert an old envelope and a recent one.
    let old_env = tavla::Envelope {
        id: "old1".to_string(),
        author: "alis".to_string(),
        clock: VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu gerku".to_string()),
        stance: EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2020-01-01T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };
    let recent_env = tavla::Envelope {
        id: "recent1".to_string(),
        author: "alis".to_string(),
        clock: VectorClock::new(),
        op: tavla::GossipOp::AssertLojban("la .adam. cu danlu".to_string()),
        stance: EpistemicStance::Deduced,
        topics: vec![],
        timestamp: "2099-01-01T00:00:00Z".to_string(),
        sig: vec![],
        pub_key: vec![],
        quarantined: false,
    };
    log.insert(old_env);
    log.insert(recent_env);
    assert_eq!(log.len(), 2);

    // Expire everything before 2025.
    let expired = log.expire_before("2025-01-01T00:00:00Z");
    assert_eq!(expired, 1, "should expire 1 old envelope");
    assert_eq!(log.len(), 1, "should have 1 envelope remaining");

    // The old assertion should be tombstoned.
    assert!(
        log.tombstones.contains("old1"),
        "expired assertion should be tombstoned"
    );

    // The recent envelope should still be active.
    let active = log.active_assertions();
    assert_eq!(active.len(), 1);
    assert_eq!(active[0].id, "recent1");
}

/// GossipNode::expire_old_envelopes removes old envelopes and rebuilds KB.
#[test]
fn gossip_node_expire_old_envelopes() {
    let mut node = GossipNode::new("alis");

    // Assert two facts.
    node.assert_local("la .adam. cu gerku").unwrap();
    node.assert_local("la .adam. cu danlu").unwrap();
    assert_eq!(node.active_count(), 2);

    // Expire with a TTL of 0 seconds — everything should expire.
    let expired = node.expire_old_envelopes(chrono::Duration::seconds(0));
    assert_eq!(expired, 2, "both envelopes should expire with 0s TTL");
    assert_eq!(node.active_count(), 0, "no active assertions after expiry");

    // KB should reflect the expiration.
    let (holds, _, _) = node.query_with_proof("la .adam. cu gerku").unwrap();
    assert!(!holds, "expired fact should not hold");
}
