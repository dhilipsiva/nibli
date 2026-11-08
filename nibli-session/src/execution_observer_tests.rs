use super::*;
use nibli_types::execution::{ExecutionEventKind as Kind, ExecutionPhase as Phase, MemoKind};
use nibli_types::logic::{ResourceKind, UnknownReason};

fn chain() -> CoreSession {
    let session = CoreSession::new();
    session.set_materialization(false);
    for source in ["dog(Adam).", "animal(every dog).", "alive(every animal)."] {
        session.assert_text(source).unwrap();
    }
    session
}

#[test]
fn recorder_exposes_real_depth_passes_and_memo_scopes() {
    let session = chain();
    let plain = session.query_text_with_proof("alive(Adam).").unwrap();
    let run = session.query_text_recorded("alive(Adam).", RecordingOptions::full());
    assert_eq!(
        format!("{:?}", run.outcome.as_ref().unwrap()),
        format!("{plain:?}")
    );
    assert!(run.outcome.unwrap().0.is_true());
    let probes: Vec<_> = run
        .record
        .events
        .iter()
        .filter(|e| e.kind == Kind::SearchPass && e.phase == Phase::Probe)
        .collect();
    assert!(probes.len() > 1, "must exercise real iterative deepening");
    assert_eq!(probes[0].state.depth, Some(1));
    assert_eq!(
        run.record
            .events
            .iter()
            .filter(|e| e.kind == Kind::SearchPass && e.phase == Phase::Proof)
            .count(),
        1
    );
    assert!(run.record.events.iter().any(|e| e.kind == Kind::DepthBound));
    assert!(
        run.record
            .events
            .iter()
            .any(|e| e.kind == Kind::CacheStore && e.state.memo == Some(MemoKind::RemainingDepth))
    );
    assert!(
        run.record
            .events
            .iter()
            .any(|e| e.kind == Kind::CacheHit && e.state.memo == Some(MemoKind::PredicateResult))
    );
    assert!(run.record.events.iter().any(|e| e.kind == Kind::ProofLink));
    assert!(
        run.record
            .events
            .iter()
            .filter(|e| e.phase == Phase::Probe)
            .all(|e| e.proof_node.is_none())
    );
    assert_eq!(session.max_chain_depth(), 10);

    session.set_max_chain_depth(1).unwrap();
    let limited = session.query_text_recorded("alive(Adam).", RecordingOptions::full());
    assert_eq!(
        limited.outcome.unwrap().0,
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    );
    assert_eq!(limited.record.profile.max_chain_depth, 1);
    assert_eq!(session.max_chain_depth(), 1);
}

#[test]
fn recorder_captures_compute_memo_without_inventing_a_backend_answer() {
    let session = CoreSession::new();
    let run = session.query_text_recorded("sum(Adam, 2, 3).", RecordingOptions::full());
    assert_eq!(
        run.outcome.unwrap().0,
        QueryResult::Unknown(UnknownReason::BackendUnavailable)
    );
    for kind in [Kind::CacheMiss, Kind::CacheStore, Kind::CacheHit] {
        assert!(
            run.record
                .events
                .iter()
                .any(|e| e.kind == kind && e.state.memo == Some(MemoKind::Compute)),
            "missing {kind:?}"
        );
    }
    let next = session.query_text_recorded("sum(Adam, 2, 3).", RecordingOptions::full());
    let first_compute = next
        .record
        .events
        .iter()
        .find(|e| e.state.memo == Some(MemoKind::Compute))
        .unwrap();
    assert_eq!(
        first_compute.kind,
        Kind::CacheMiss,
        "compute memo must not survive a query"
    );
}

#[test]
fn recorder_tracks_witness_minting_withdrawal_and_replay() {
    let session = CoreSession::new();
    let admitted = session.apply_changes_recorded(
        &[
            SessionChange::Assert {
                text: "big(some dog).".into(),
            },
            SessionChange::Assert {
                text: "cat(Bela).".into(),
            },
        ],
        RecordingOptions::full(),
    );
    let ids = admitted.outcome.unwrap().operation_ids;
    assert!(
        admitted
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Witness && e.assertion_ids.contains(&ids[0][0]))
    );
    assert!(
        admitted
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::FactInsert)
    );
    let query = session.query_text_recorded("big(some dog).", RecordingOptions::full());
    assert!(query.outcome.unwrap().0.is_true());
    assert!(
        query
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Candidate && e.state.candidate.is_some())
    );
    let withdrawal = session.apply_changes_recorded(
        &[SessionChange::Withdraw {
            id: ids[0][0].clone(),
        }],
        RecordingOptions::full(),
    );
    withdrawal.outcome.unwrap();
    for kind in [
        Kind::Withdraw,
        Kind::Rebuild,
        Kind::Replay,
        Kind::CacheInvalidate,
    ] {
        assert!(
            withdrawal.record.events.iter().any(|e| e.kind == kind),
            "missing {kind:?}"
        );
    }
    assert!(
        withdrawal
            .record
            .events
            .iter()
            .any(|e| e.kind == Kind::Replay && e.assertion_ids.contains(&ids[1][0]))
    );
    assert!(session.query_text("big(some dog).").unwrap().is_false());
    assert!(session.query_text("cat(Bela).").unwrap().is_true());
}

#[test]
fn cancellation_is_aborted_without_reporting_the_unwind_sentinel_as_truth() {
    use std::sync::{Arc, atomic::AtomicBool};
    let session = chain();
    session
        .kb()
        .set_cancel_flag(Arc::new(AtomicBool::new(true)));
    let run = session.query_text_recorded("alive(Adam).", RecordingOptions::full());
    assert!(run.outcome.is_err());
    assert_eq!(run.record.status, RecordingStatus::Aborted);
    assert!(run.record.result.is_none());
    assert!(
        run.record
            .events
            .iter()
            .all(|e| e.kind != Kind::GoalExit || e.result.is_none())
    );
    session.kb().clear_cancel_flag();
    assert!(session.query_text("alive(Adam).").unwrap().is_true());
}

#[test]
fn snapshot_recovers_exhausted_identity_space_and_rejects_missing_guard_metadata() {
    let session = CoreSession::new();
    session.assert_text("dog(Adam).").unwrap();
    let mut exhausted = session.snapshot().unwrap();
    exhausted.assertions[0].id = (u64::MAX - 1).to_string();
    exhausted.next_fact_id = u64::MAX.to_string();
    let restored = CoreSession::from_snapshot(&exhausted).unwrap();
    assert_eq!(restored.snapshot().unwrap(), exhausted);
    assert!(restored.assert_text("dog(Bela).").is_err());
    assert!(restored.query_text("dog(Adam).").unwrap().is_true());

    let guarded = CoreSession::new();
    guarded.assert_text("derived_only(\"ready\").").unwrap();
    let mut inconsistent = guarded.snapshot().unwrap();
    inconsistent.derived_only.clear();
    assert!(CoreSession::from_snapshot(&inconsistent).is_err());
}

#[test]
fn live_phase_taps_are_per_call_and_survive_disabled_or_truncated_history() {
    use std::sync::{Arc, Mutex};
    #[derive(Default)]
    struct Tap(Mutex<Vec<Phase>>);
    impl ExecutionObserver for Tap {
        fn phase(&self, phase: Phase) {
            self.0.lock().unwrap().push(phase);
        }
        fn observe(&self, _: ExecutionEvent) {
            panic!("phase tap must not receive event payloads");
        }
        fn compilation(&self, _: CompilationArtifact) {
            panic!("phase tap must not receive compiler artifacts");
        }
    }
    let session = chain();
    let plain = session.query_text_with_proof("alive(Adam).").unwrap();
    for options in [
        RecordingOptions::disabled(),
        RecordingOptions {
            max_events: 0,
            ..RecordingOptions::standard()
        },
    ] {
        let tap = Arc::new(Tap::default());
        let run =
            session.query_text_recorded_with_phase_observer("alive(Adam).", options, tap.clone());
        assert_eq!(format!("{:?}", run.outcome.unwrap()), format!("{plain:?}"));
        let phases = tap.0.lock().unwrap().clone();
        assert_eq!(phases.first(), Some(&Phase::Compile));
        assert!(phases.contains(&Phase::Probe));
        assert!(phases.contains(&Phase::Proof));
        assert_eq!(phases.last(), Some(&Phase::Complete));
        assert!(phases.windows(2).all(|pair| pair[0] != pair[1]));
        session
            .query_text_recorded("alive(Adam).", RecordingOptions::standard())
            .outcome
            .unwrap();
        assert_eq!(
            *tap.0.lock().unwrap(),
            phases,
            "tap must not leak into a later call"
        );
    }
    let tap = Arc::new(Tap::default());
    session
        .apply_changes_recorded_with_phase_observer(
            &[SessionChange::Assert {
                text: "cat(Bela).".into(),
            }],
            RecordingOptions::standard(),
            tap.clone(),
        )
        .outcome
        .unwrap();
    let phases = tap.0.lock().unwrap().clone();
    assert_eq!(phases.first(), Some(&Phase::Mutation));
    assert!(phases.contains(&Phase::Compile));
    assert!(phases.contains(&Phase::Admission));
    assert_eq!(phases.last(), Some(&Phase::Complete));
}

#[test]
fn snapshot_preserves_literal_and_withdrawn_admission_declarations() {
    for source in [
        "derived_only(\"Ready\").",
        "derived_only(\"not an identifier\").",
        "derived_only(\"\").",
        "admits(\"Ready\").",
    ] {
        let session = CoreSession::new();
        let ids = session.assert_text(source).unwrap();
        for withdrawn in [false, true] {
            if withdrawn {
                session.retract_fact(ids[0].0).unwrap();
            }
            let snapshot = session.snapshot().unwrap();
            let restored = CoreSession::from_snapshot(&snapshot).unwrap();
            assert_eq!(
                restored.snapshot().unwrap(),
                snapshot,
                "{source}, withdrawn={withdrawn}"
            );
        }
    }
}

#[test]
fn snapshot_replays_history_before_applying_saved_strict_profile() {
    let session = CoreSession::new();
    session.assert_text("~dog(Adam).").unwrap();
    session.assert_text("dog(Adam).").unwrap();
    session.set_strict(true);
    let snapshot = session.snapshot().unwrap();
    let restored = CoreSession::from_snapshot(&snapshot).unwrap();
    assert_eq!(restored.snapshot().unwrap(), snapshot);
    assert!(restored.kb().is_strict());
    assert!(restored.query_text("dog(Adam).").unwrap().is_true());
    assert_eq!(
        format!("{:?}", restored.assert_text("dog(Adam).")),
        format!("{:?}", session.assert_text("dog(Adam).")),
        "future admission behavior must match the saved session"
    );
}

#[test]
fn snapshot_preserves_rebuilt_import_and_materialization_profiles() {
    for import in [false, true] {
        for materialization in [false, true] {
            let session = CoreSession::new();
            session.assert_text("animal(every dog).").unwrap();
            session.set_existential_import(!import).unwrap();
            session.set_existential_import(import).unwrap();
            session.set_materialization(materialization);
            let expected = session.query_text("dog(some animal).").unwrap();
            let snapshot = session.snapshot().unwrap();
            let restored = CoreSession::from_snapshot(&snapshot).unwrap();
            assert_eq!(restored.snapshot().unwrap(), snapshot);
            assert_eq!(restored.query_text("dog(some animal).").unwrap(), expected);
        }
    }
}

#[test]
fn unsupported_native_configuration_rejects_snapshot_but_recording_stays_truthful() {
    let setters: &[fn(&CoreSession)] = &[
        |session| {
            session
                .kb()
                .set_predicate_sorts("dog", vec!["animal".into()])
        },
        |session| session.kb().declare_entity_sort("Adam", "animal"),
        |session| session.kb().declare_subsort("dog", "animal"),
        |session| session.kb().set_rule_forward("animal", true),
        |session| session.kb().set_rule_priority("animal", 3),
        |session| {
            session
                .kb()
                .register_constraint("native".into(), vec![])
                .unwrap()
        },
    ];
    for configure in setters {
        let session = chain();
        configure(&session);
        assert!(session.snapshot().is_err());
        let plain = session.query_text_with_proof("dog(Adam).").unwrap();
        let recorded = session.query_text_recorded("dog(Adam).", RecordingOptions::standard());
        assert_eq!(
            format!("{:?}", recorded.outcome.unwrap()),
            format!("{plain:?}")
        );
        assert_eq!(recorded.record.status, RecordingStatus::Complete);
        assert!(recorded.record.initial_snapshot.is_none());
        assert!(recorded.record.snapshot_unavailable_reason.is_some());
        assert!(
            !recorded
                .record
                .capabilities
                .iter()
                .any(|c| c == "recoverable_snapshot")
        );
        assert!(!recorded.record.events.is_empty());
    }
}

#[test]
fn external_compute_callbacks_follow_the_documented_host_rebind_contract() {
    fn evaluate(_: &str, _: &[nibli_types::logic::LogicalTerm]) -> Result<bool, String> {
        Ok(true)
    }
    fn batch(requests: &[nibli_reason::ComputeRequest]) -> Vec<Result<bool, String>> {
        requests.iter().map(|_| Ok(true)).collect()
    }
    let session = CoreSession::new();
    session.set_compute_dispatch(evaluate, batch);
    assert!(session.query_text("sum(Adam, 2, 3).").unwrap().is_true());
    let restored = CoreSession::from_snapshot(&session.snapshot().unwrap()).unwrap();
    assert_eq!(
        restored.query_text("sum(Adam, 2, 3).").unwrap(),
        QueryResult::Unknown(UnknownReason::BackendUnavailable)
    );
    restored.set_compute_dispatch(evaluate, batch);
    assert!(restored.query_text("sum(Adam, 2, 3).").unwrap().is_true());
}

#[test]
fn native_display_only_or_mismatched_labels_cannot_claim_recoverable_snapshots() {
    fn check(session: CoreSession) {
        assert!(session.snapshot().is_err());
        let plain = session.query_text_with_proof("dog(Adam).").unwrap();
        assert!(plain.0.is_true());
        let run = session.query_text_recorded("dog(Adam).", RecordingOptions::standard());
        assert_eq!(format!("{:?}", run.outcome.unwrap()), format!("{plain:?}"));
        assert_eq!(run.record.status, RecordingStatus::Complete);
        assert!(run.record.initial_snapshot.is_none());
        assert!(
            !run.record
                .capabilities
                .iter()
                .any(|c| c == "recoverable_snapshot")
        );
        let reason = run.record.snapshot_unavailable_reason.unwrap();
        assert!(reason.contains("assertion #0"), "{reason}");
        assert!(reason.len() < 160, "unbounded snapshot summary");
        assert!(!run.record.events.is_empty());
    }
    let direct = CoreSession::new();
    direct
        .assert_fact_direct(
            "dog",
            &[nibli_types::logic::LogicalTerm::Constant("adam".into())],
            None,
        )
        .unwrap();
    check(direct);
    for label in [
        "native display label".into(),
        "invalid_".repeat(1000),
        "cat(Adam).".into(),
    ] {
        let injected = CoreSession::new();
        let buffer = injected.compile_text("dog(Adam).").unwrap();
        injected.assert_buffer_with_id(buffer, label, 0).unwrap();
        check(injected);
    }
}

#[test]
fn repeated_kr_packets_and_withdrawn_native_labels_roundtrip() {
    let session = CoreSession::new();
    let packet = "dog(Adam). cat(Bela). animal(every dog).";
    let first = session.assert_text(packet).unwrap();
    session.assert_text(packet).unwrap();
    session.retract_fact(first[0].0).unwrap();
    session
        .restore_withdrawn_assertion(100, "this was never KR".into())
        .unwrap();
    let snapshot = session.snapshot().unwrap();
    let restored = CoreSession::from_snapshot(&snapshot).unwrap();
    assert_eq!(restored.snapshot().unwrap(), snapshot);
    assert!(restored.query_text("animal(Adam).").unwrap().is_true());
    let run = restored.query_text_recorded("animal(Adam).", RecordingOptions::standard());
    assert!(
        run.record
            .capabilities
            .iter()
            .any(|c| c == "recoverable_snapshot")
    );
    assert!(run.record.snapshot_unavailable_reason.is_none());
}
