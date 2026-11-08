use super::*;
use nibli_types::execution::{
    ExecutionEventKind as Kind, ExecutionPhase as Phase, RecordingStatus,
};

const POLICY: &str = "derived_only(\"ready\"). all $build: approves(TestRunner, $build) & approves(Reviewer, $build) -> ready($build, Release). approves(TestRunner, BuildA).";
const CLAIM: &str = "ready(BuildA, Release).";

fn release_session() -> CoreSession {
    let session = CoreSession::new();
    session.assert_text(POLICY).unwrap();
    session
}

#[test]
fn recording_preserves_verdicts_proofs_errors_and_profile() {
    for strict in [false, true] {
        let session = release_session();
        session.set_strict(strict);
        for claim in [
            CLAIM,
            "approves(TestRunner, BuildA).",
            "sum(Adam, 2, 3).",
            "invalid_uncommitted(Adam).",
        ] {
            let plain = session.query_text_with_proof(claim);
            for options in [
                RecordingOptions::disabled(),
                RecordingOptions::standard(),
                RecordingOptions::full(),
            ] {
                let recorded = session.query_text_recorded(claim, options);
                assert_eq!(
                    format!("{:?}", recorded.outcome),
                    format!("{plain:?}"),
                    "claim: {claim}"
                );
                assert_eq!(recorded.record.profile.strict, strict);
                if options.mode == RecordingMode::Disabled {
                    assert_eq!(recorded.record.status, RecordingStatus::Disabled);
                    assert!(recorded.record.events.is_empty());
                    assert!(recorded.record.artifacts.is_empty());
                }
            }
        }
    }
}

#[test]
fn execution_records_real_failed_candidates_and_distinct_search_passes() {
    let session = release_session();
    session.assert_text("approves(Reviewer, BuildB).").unwrap();
    let recorded = session.query_text_recorded(CLAIM, RecordingOptions::full());
    assert!(recorded.outcome.unwrap().0.is_false());
    let events = &recorded.record.events;
    for kind in [
        Kind::Parse,
        Kind::Validate,
        Kind::Lower,
        Kind::SearchPass,
        Kind::GoalEnter,
        Kind::Unification,
        Kind::RuleCondition,
        Kind::Outcome,
    ] {
        assert!(events.iter().any(|e| e.kind == kind), "missing {kind:?}");
    }
    assert!(events.iter().any(|e| e.phase == Phase::Probe));
    assert!(events.iter().any(|e| e.phase == Phase::Proof));
    assert!(events.iter().any(
        |e| e.kind == Kind::Unification && e.result.as_ref().is_some_and(QueryResult::is_false)
    ));
    for (index, event) in events.iter().enumerate() {
        assert_eq!(event.sequence, index.to_string());
        if let Some(parent) = &event.parent_frame_id {
            assert!(parent.parse::<usize>().unwrap() < index);
        }
    }
    let artifact = &recorded.record.artifacts[0];
    assert_eq!(artifact.source, CLAIM);
    assert_eq!(
        artifact.logic.as_ref().unwrap(),
        &session.compile_query_text(CLAIM).unwrap()
    );
}

#[test]
fn recording_limits_truncate_history_without_changing_reasoning() {
    let session = release_session();
    let expected = session.query_text(CLAIM).unwrap();
    for (events, bytes) in [(1, 8 * 1024 * 1024), (10_000, 16)] {
        let options = RecordingOptions {
            max_events: events,
            max_bytes: bytes,
            ..RecordingOptions::standard()
        };
        let run = session.query_text_recorded(CLAIM, options);
        assert_eq!(run.outcome.unwrap().0, expected);
        assert_eq!(run.record.status, RecordingStatus::Truncated);
        assert!(run.record.truncation_reason.is_some());
        assert!(run.record.events.len() <= events);
        assert!(run.record.recorded_bytes <= bytes);
    }
    let next = session.query_text_recorded(CLAIM, RecordingOptions::standard());
    assert_eq!(next.record.status, RecordingStatus::Complete);
    assert_eq!(next.record.events[0].sequence, "0");
}

#[test]
fn mixed_mutation_failure_rolls_back_sources_frontier_and_guard() {
    let session = release_session();
    let before = serde_json::to_value(session.snapshot().unwrap()).unwrap();
    let changed = session.apply_changes_recorded(
        &[
            SessionChange::Assert {
                text: "approves(Reviewer, BuildA).".into(),
            },
            SessionChange::Assert { text: CLAIM.into() },
        ],
        RecordingOptions::full(),
    );
    assert!(changed.outcome.is_err());
    assert_eq!(changed.record.status, RecordingStatus::Aborted);
    assert!(
        changed
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Rollback)
    );
    assert!(
        !changed
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Commit && e.phase == Phase::Complete)
    );
    assert!(
        changed
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Rollback && e.phase == Phase::Complete)
    );
    assert_eq!(
        serde_json::to_value(session.snapshot().unwrap()).unwrap(),
        before
    );
    assert!(session.query_text(CLAIM).unwrap().is_false());
    let next = session.query_text_recorded(CLAIM, RecordingOptions::standard());
    assert_eq!(next.record.status, RecordingStatus::Complete);
}

#[test]
fn snapshots_preserve_independent_support_tombstones_and_large_ids() {
    let session = release_session();
    let changed = session
        .apply_changes_recorded(
            &[
                SessionChange::Assert {
                    text: "approves(Reviewer, BuildA).".into(),
                },
                SessionChange::Assert {
                    text: "approves(Reviewer, BuildA).".into(),
                },
            ],
            RecordingOptions::standard(),
        )
        .outcome
        .unwrap();
    let first = &changed.operation_ids[0][0];
    let second = &changed.operation_ids[1][0];
    session
        .apply_changes_recorded(
            &[SessionChange::Withdraw { id: first.clone() }],
            RecordingOptions::standard(),
        )
        .outcome
        .unwrap();
    let snapshot = session.snapshot().unwrap();
    assert!(
        snapshot
            .assertions
            .iter()
            .find(|a| &a.id == first)
            .unwrap()
            .buffer
            .is_none()
    );
    let restored = CoreSession::from_snapshot(&snapshot).unwrap();
    assert_eq!(
        serde_json::to_value(restored.snapshot().unwrap()).unwrap(),
        serde_json::to_value(&snapshot).unwrap()
    );
    assert!(restored.query_text(CLAIM).unwrap().is_true());
    restored
        .apply_changes_recorded(
            &[SessionChange::Withdraw { id: second.clone() }],
            RecordingOptions::standard(),
        )
        .outcome
        .unwrap();
    assert!(restored.query_text(CLAIM).unwrap().is_false());
    assert!(restored.assert_text(CLAIM).is_err());

    let simple = CoreSession::new();
    simple.assert_text("dog(Adam).").unwrap();
    let mut large = simple.snapshot().unwrap();
    large.assertions[0].id = "9007199254740993".into();
    large.next_fact_id = "9007199254740994".into();
    let rebuilt = CoreSession::from_snapshot(&large).unwrap();
    assert_eq!(
        rebuilt.snapshot().unwrap().assertions[0].id,
        "9007199254740993"
    );
    let mutation = rebuilt.apply_changes_recorded(
        &[SessionChange::Assert {
            text: "dog(Bela).".into(),
        }],
        RecordingOptions::standard(),
    );
    assert_eq!(
        mutation.outcome.unwrap().operation_ids[0][0],
        "9007199254740994"
    );
}

#[test]
fn snapshot_replay_rejects_tampering_and_invalid_identity_frontiers() {
    let session = release_session();
    let snapshot = session.snapshot().unwrap();
    let mut cases = Vec::new();
    let mut bad = snapshot.clone();
    bad.schema_version += 1;
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.engine_version = "unrelated".into();
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.next_fact_id = "0".into();
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.assertions[0].id = "00".into();
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.assertions[1].id = bad.assertions[0].id.clone();
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.assertions[0].label = "dog(Adam).".into();
    cases.push(bad);
    let mut bad = snapshot.clone();
    bad.derived_only = vec!["ready".into(), "ready".into()];
    cases.push(bad);
    for bad in cases {
        assert!(
            CoreSession::from_snapshot(&bad).is_err(),
            "accepted invalid snapshot: {bad:?}"
        );
    }
    assert_eq!(
        serde_json::to_value(session.snapshot().unwrap()).unwrap(),
        serde_json::to_value(snapshot).unwrap()
    );
}
