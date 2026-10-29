//! Grounded role lookups must avoid a relation scan for every counted member.
//! The scan twin stays test-only and compares complete witnesses and certificates.

use super::*;
use crate::kb::{ANCHOR_FACT_VISITS, ANCHOR_POSITION_INDEX_ENABLED};
use nibli_types::logic::{EngineProfile, ProofEnvelope, validate_envelope};
use std::time::Instant;

const MEMBER: &str = "count_member";
const VARIABLE: &str = "$member";

fn with_index<T>(enabled: bool, f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            ANCHOR_POSITION_INDEX_ENABLED.set(self.0);
        }
    }
    let _restore = Restore(ANCHOR_POSITION_INDEX_ENABLED.replace(enabled));
    f()
}

fn member_query(count: Option<u32>) -> LogicBuffer {
    let mut nodes = Vec::new();
    let event = LogicalTerm::Variable("_ev0".into());
    let anchor = pred(&mut nodes, MEMBER, vec![event.clone()]);
    let role = pred(
        &mut nodes,
        &format!("{MEMBER}_x1"),
        vec![event, LogicalTerm::Variable(VARIABLE.into())],
    );
    let body = and(&mut nodes, anchor, role);
    let body = exists(&mut nodes, "_ev0", body);
    let root = nodes.len() as u32;
    nodes.push(match count {
        Some(count) => LogicNode::CountNode((VARIABLE.into(), count, body)),
        None => LogicNode::ExistsNode((VARIABLE.into(), body)),
    });
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

fn member_kb(size: usize) -> KnowledgeBase {
    let statements = (0..size)
        .map(|i| {
            let key = format!("member-{i:05}");
            (make_event_assertion(&key, MEMBER), key)
        })
        .collect();
    let (kb, _) = KnowledgeBase::from_compiled_batch(statements).unwrap();
    kb.set_strict(true);
    kb.set_max_chain_depth(32).unwrap();
    kb
}

fn certificate(kb: &KnowledgeBase, query: LogicBuffer) -> ProofEnvelope {
    let (result, trace) = kb.query_entailment_with_proof(query).unwrap();
    let profile = EngineProfile {
        strict: kb.is_strict(),
        existential_import: kb.is_existential_import(),
        materialization: kb.is_materialization(),
        max_chain_depth: kb.max_chain_depth(),
    };
    let envelope = ProofEnvelope::bind("indexed count regression", result, trace, profile);
    validate_envelope(&envelope).unwrap();
    envelope
}

fn assert_scan_parity(kb: &KnowledgeBase, find: LogicBuffer, exact: LogicBuffer) {
    let ask = || {
        (
            kb.query_find(find.clone()).map_err(|e| e.to_string()),
            kb.count_witnesses(find.clone()).map_err(|e| e.to_string()),
            certificate(kb, exact.clone()),
        )
    };
    let indexed = with_index(true, ask);
    let scanned = with_index(false, ask);
    assert_eq!(indexed, scanned);
    assert_eq!(indexed, with_index(true, ask));
}

#[test]
fn indexed_counts_preserve_witnesses_and_certificates() {
    for size in [0, 1, 9, 100] {
        let kb = member_kb(size);
        assert_scan_parity(&kb, member_query(None), member_query(Some(size as u32)));
        assert_scan_parity(&kb, member_query(None), member_query(Some(size as u32 + 1)));
    }
    let kb = member_kb(9);
    // Separate assertions of the same member retain their own evidence, but
    // neither the row count nor certificate may depend on the lookup route.
    kb.assert_fact(make_event_assertion("member-00000", MEMBER), "again".into())
        .unwrap();
    assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), 9);
    assert_scan_parity(&kb, member_query(None), member_query(Some(9)));
}

#[test]
fn indexed_counts_preserve_surface_rules_flavors_equality_and_incompleteness() {
    for (statements, find, count) in [
        (
            vec!["dog(Adam).", "dog(Bel).", "animal(every dog)."],
            "animal($x).",
            2,
        ),
        (
            vec!["dog(Adam).", "cat(Adam).", "cat(Bel)."],
            "dog($x) | cat($x).",
            2,
        ),
        (
            vec!["past dog(Adam).", "dog(Bel).", "future dog(Cam)."],
            "past dog($x).",
            1,
        ),
        (
            vec!["dog(Adam).", "dog(Bel).", "Adam = Bel."],
            "dog($x).",
            1,
        ),
        (
            vec!["dog(Adam).", "animal(every dog).", "dog(every animal)."],
            "dog($x).",
            1,
        ),
    ] {
        let (kb, _) = KnowledgeBase::from_compiled_batch(
            statements
                .iter()
                .map(|line| (compile_surface(line), (*line).into()))
                .collect(),
        )
        .unwrap();
        kb.set_materialization(false);
        kb.set_max_chain_depth(2).unwrap();
        let find = compile_surface(find);
        let mut exact = find.clone();
        let mut replaced = 0;
        for node in &mut exact.nodes {
            if let LogicNode::ExistsNode((variable, body)) = node
                && variable == "$x"
            {
                *node = LogicNode::CountNode((variable.clone(), count, *body));
                replaced += 1;
            }
        }
        assert_eq!(replaced, 1, "surface find must bind one individual");
        assert_scan_parity(&kb, find, exact);
    }
}

#[test]
fn indexed_counts_follow_assert_retract_reset_and_hypothetical_lifecycles() {
    let kb = member_kb(3);
    assert_scan_parity(&kb, member_query(None), member_query(Some(3)));
    let id = kb
        .assert_fact(make_event_assertion("new", MEMBER), "new".into())
        .unwrap();
    assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), 4);
    assert_scan_parity(&kb, member_query(None), member_query(Some(4)));
    kb.retract_fact(id).unwrap();
    assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), 3);
    assert_scan_parity(&kb, member_query(None), member_query(Some(3)));
    kb.rebuild().unwrap();
    assert_scan_parity(&kb, member_query(None), member_query(Some(3)));
    kb.with_assumptions(&[make_event_assertion("temporary", MEMBER)], |temporary| {
        assert_eq!(temporary.count_witnesses(member_query(None)).unwrap(), 4);
        assert_scan_parity(temporary, member_query(None), member_query(Some(4)));
    })
    .unwrap();
    assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), 3);
    kb.reset().unwrap();
    assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), 0);
    assert_scan_parity(&kb, member_query(None), member_query(Some(0)));
}

#[test]
fn indexed_counts_keep_incomplete_collections_and_proofs_non_definitive() {
    let (kb, _) = KnowledgeBase::from_compiled_batch(vec![
        (
            make_event_assertion("outsider", "unrelated"),
            "domain".into(),
        ),
        (
            make_event_universal(MEMBER, "other_member"),
            "forward".into(),
        ),
        (
            make_event_universal("other_member", MEMBER),
            "backward".into(),
        ),
    ])
    .unwrap();
    kb.set_materialization(false);
    kb.set_max_chain_depth(2).unwrap();
    for indexed in [false, true] {
        with_index(indexed, || {
            assert_incomplete_enumeration(kb.query_find(member_query(None)));
            assert_incomplete_enumeration(kb.count_witnesses(member_query(None)));
            assert!(
                !certificate(&kb, member_query(Some(0)))
                    .result
                    .is_definitive()
            );
        });
    }
    assert_scan_parity(&kb, member_query(None), member_query(Some(0)));
}

#[test]
fn indexed_counts_visit_linear_fact_buckets() {
    let mut previous = None;
    for size in [1_000, 10_000] {
        let kb = member_kb(size);
        ANCHOR_FACT_VISITS.set(0);
        assert_eq!(kb.count_witnesses(member_query(None)).unwrap(), size);
        let find_visits = ANCHOR_FACT_VISITS.replace(0);
        assert_eq!(
            certificate(&kb, member_query(Some(size as u32))).result,
            QueryResult::True
        );
        let proof_visits = ANCHOR_FACT_VISITS.get();
        // Each query may read a constant number of candidate buckets per member.
        // This counts actual fact visits, so a restored per-member full scan
        // fails independently of the machine's clock or build optimization.
        assert!(find_visits <= 8 * size, "find: {size}: {find_visits}");
        assert!(proof_visits <= 16 * size, "proof: {size}: {proof_visits}");
        if let Some((old_find, old_proof)) = previous {
            assert!(find_visits <= 11 * old_find);
            assert!(proof_visits <= 11 * old_proof);
        }
        previous = Some((find_visits, proof_visits));
    }
    // Positive control: the same counter must see the original quadratic scan.
    let kb = member_kb(100);
    ANCHOR_FACT_VISITS.set(0);
    with_index(false, || kb.count_witnesses(member_query(None))).unwrap();
    assert!(ANCHOR_FACT_VISITS.get() >= 100 * 100);
}

#[test]
#[ignore = "explicit debug/release benchmark; includes the quadratic scan reference"]
fn benchmark_event_decomposed_counts() {
    for size in [100, 1_000, 2_000, 5_000, 10_000] {
        let kb = member_kb(size);
        let mut envelopes = Vec::new();
        for indexed in [false, true] {
            with_index(indexed, || {
                ANCHOR_FACT_VISITS.set(0);
                let start = Instant::now();
                let count = kb.count_witnesses(member_query(None)).unwrap();
                let find_elapsed = start.elapsed();
                let find_visits = ANCHOR_FACT_VISITS.replace(0);
                let start = Instant::now();
                let envelope = certificate(&kb, member_query(Some(size as u32)));
                let proof_elapsed = start.elapsed();
                assert_eq!(count, size);
                assert_eq!(envelope.result, QueryResult::True);
                println!(
                    "count-benchmark size={size} indexed={indexed} find_ms={:.3} proof_ms={:.3} find_visits={find_visits} proof_visits={}",
                    find_elapsed.as_secs_f64() * 1_000.0,
                    proof_elapsed.as_secs_f64() * 1_000.0,
                    ANCHOR_FACT_VISITS.get(),
                );
                envelopes.push(envelope);
            });
        }
        assert_eq!(envelopes[0], envelopes[1], "certificate at {size}");
    }
}
