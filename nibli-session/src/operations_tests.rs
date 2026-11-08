use super::*;
use nibli_types::execution::{
    ExecutionEventKind as Kind, ExecutionPhase as Phase, RecordingStatus,
};
use nibli_types::logic::{CollectionFailureKind, EngineProfile, WitnessOrigin};
use std::sync::{Arc, Mutex};

fn session(source: &str) -> CoreSession {
    let session = CoreSession::new();
    session.set_materialization(false);
    session.assert_text(source).unwrap();
    session
}

fn modes() -> [RecordingOptions; 3] {
    [
        RecordingOptions::disabled(),
        RecordingOptions::standard(),
        RecordingOptions::full(),
    ]
}

#[test]
fn compile_inspection_preserves_ir_and_separates_preflight_from_admission() {
    let session = session("derived_only(\"dog\").");
    let before = session.snapshot().unwrap();
    for options in modes() {
        let inspected = session.compile_text_recorded("dog(Adam).", true, options);
        let result = inspected.outcome.unwrap();
        assert_eq!(result.logic, session.compile_text("dog(Adam).").unwrap());
        assert_eq!(result.structural_preflight, StructuralPreflight::Passed);
        assert!(
            session.assert_text("dog(Adam).").is_err(),
            "structural preflight is not admission"
        );
        let query_only = session.compile_text_recorded("dog(exactly 1 dog).", true, options);
        assert!(matches!(
            query_only.outcome.unwrap().structural_preflight,
            StructuralPreflight::Refused { .. }
        ));
        let no_preflight = session.compile_text_recorded("dog(exactly 1 dog).", false, options);
        assert_eq!(
            no_preflight.outcome.unwrap().structural_preflight,
            StructuralPreflight::NotRequested
        );
        let error = session.compile_text_recorded("uncommitted_predicate(Adam).", true, options);
        assert_eq!(
            error.outcome.unwrap_err().to_string(),
            session
                .compile_text("uncommitted_predicate(Adam).")
                .unwrap_err()
                .to_string()
        );
        assert_eq!(session.snapshot().unwrap(), before);
    }
}

#[test]
fn collection_wrappers_preserve_complete_unavailable_and_error_results() {
    let session = session("dog(Adam). dog(Bob). Adam = Bob. quantity(Adam, 3). quantity(Cara, 7).");
    let before = session.snapshot().unwrap();
    for options in modes() {
        for query in [
            "dog($x).",
            "cat($x).",
            "sum(Adam, 2, 3).",
            "uncommitted($x).",
        ] {
            let find = session.query_find_text_recorded(query, options);
            assert_eq!(
                format!("{:?}", find.outcome),
                format!("{:?}", session.query_find_text_outcome(query))
            );
            let count = session.count_witnesses_text_recorded(query, options);
            assert_eq!(
                format!("{:?}", count.outcome),
                format!("{:?}", session.count_witnesses_text_outcome(query))
            );
            assert!(find.record.result.is_none());
            assert!(count.record.result.is_none());
        }
        for variable in ["$n", "$missing"] {
            let aggregate = session.aggregate_text_recorded(
                "quantity($x, $n).",
                variable,
                AggregateOp::Sum,
                options,
            );
            assert_eq!(
                format!("{:?}", aggregate.outcome),
                format!(
                    "{:?}",
                    session.aggregate_text_outcome("quantity($x, $n).", variable, AggregateOp::Sum)
                )
            );
            assert!(aggregate.record.result.is_none());
        }
        assert_eq!(session.snapshot().unwrap(), before);
    }
    assert_eq!(
        session.count_witnesses_text_outcome("dog($x).").unwrap(),
        CollectionOutcome::Complete(1)
    );
    let unavailable =
        session.query_find_text_recorded("sum(Adam, 2, 3).", RecordingOptions::full());
    let CollectionOutcome::Unavailable(failure) = unavailable.outcome.unwrap() else {
        panic!("incomplete enumeration must be unavailable")
    };
    assert_eq!(failure.kind, CollectionFailureKind::IncompleteEnumeration);
    assert_eq!(
        unavailable.record.status,
        RecordingStatus::Complete,
        "a completed unavailable result is not an aborted operation"
    );
    assert!(
        unavailable
            .record
            .events
            .iter()
            .any(|event| event.kind == Kind::EnumerationIncomplete)
    );
    assert!(
        unavailable
            .record
            .events
            .iter()
            .all(|event| event.kind != Kind::EnumerationBinding)
    );
}

#[test]
fn collection_recording_retains_source_and_limits_without_inventing_proof() {
    let session = session("dog(Adam). cat(Bob). person(Cara).");
    let expected = session
        .query_find_text_outcome("dog($x) | cat($x).")
        .unwrap();
    let full = session.query_find_text_recorded("dog($x) | cat($x).", RecordingOptions::full());
    assert_eq!(full.outcome.unwrap(), expected);
    assert!(
        full.record
            .events
            .iter()
            .any(|event| event.kind == Kind::EnumerationCandidate)
    );
    assert!(
        full.record
            .events
            .iter()
            .any(|event| event.kind == Kind::EnumerationBinding)
    );
    assert!(
        full.record
            .events
            .iter()
            .all(|event| event.proof_node.is_none())
    );
    assert_eq!(full.record.artifacts[0].source, "dog($x) | cat($x).");
    assert!(
        full.record
            .events
            .iter()
            .filter(|event| event.kind == Kind::EnumerationCandidate)
            .all(|event| event
                .source
                .as_ref()
                .is_some_and(|source| source.artifact_id == "0"))
    );
    let limited = session.query_find_text_recorded(
        "dog($x) | cat($x).",
        RecordingOptions {
            max_events: 1,
            max_bytes: 128,
            ..RecordingOptions::standard()
        },
    );
    assert_eq!(limited.outcome.unwrap(), expected);
    assert_eq!(limited.record.status, RecordingStatus::Truncated);
    assert!(limited.record.recorded_bytes <= 128);
}

#[test]
fn contradiction_observation_preserves_findings_and_unresolved_checks() {
    let session = session(
        "dog(Adam). ~dog(Adam). dog(Bob). animal(every dog). alive(every animal). ~alive(Bob).",
    );
    session.set_max_chain_depth(1).unwrap();
    let expected = session.kb().check_contradictions_report();
    assert!(!expected.violations.is_empty());
    assert!(!expected.unresolved.is_empty());
    let before = session.snapshot().unwrap();
    for options in modes() {
        let recorded = session.check_contradictions_recorded(options);
        assert_eq!(recorded.outcome.unwrap(), expected);
        assert!(recorded.record.result.is_none());
        if options.mode != RecordingMode::Disabled {
            for kind in [
                Kind::ConstraintCheck,
                Kind::ConstraintViolation,
                Kind::ConstraintGap,
            ] {
                assert!(
                    recorded
                        .record
                        .events
                        .iter()
                        .any(|event| event.kind == kind),
                    "missing {kind:?}"
                );
            }
        }
        assert_eq!(session.snapshot().unwrap(), before);
    }
    serde_json::to_value(&expected).unwrap();
}

#[test]
fn profiles_apply_atomically_and_recovery_preserves_comparison_semantics() {
    let session = session("animal(every dog).");
    let original = session.profile();
    assert!(!session.query_text("dog(some dog).").unwrap().is_true());
    let imported = EngineProfile {
        strict: true,
        existential_import: true,
        materialization: true,
        max_chain_depth: 17,
    };
    let changed = session.set_profile_recorded(&imported, RecordingOptions::full());
    assert_eq!(changed.outcome.unwrap(), imported);
    assert_eq!(session.profile(), imported);
    assert!(
        changed
            .record
            .events
            .iter()
            .any(|event| event.kind == Kind::ProfileChange)
    );
    assert!(changed.record.final_snapshot.is_some());
    let CollectionOutcome::Complete(rows) = session.query_find_text_outcome("dog($x).").unwrap()
    else {
        panic!("imported witness must be enumerable")
    };
    assert!(
        rows.iter()
            .flatten()
            .any(|binding| binding.origin == WitnessOrigin::ExistentialImport)
    );
    let restored = CoreSession::from_snapshot(&session.snapshot().unwrap()).unwrap();
    assert_eq!(restored.profile(), imported);
    assert_eq!(
        restored.query_find_text_outcome("dog($x).").unwrap(),
        CollectionOutcome::Complete(rows)
    );
    let before = session.snapshot().unwrap();
    let invalid = EngineProfile {
        max_chain_depth: 0,
        ..original.clone()
    };
    let rejected = session.set_profile_recorded(&invalid, RecordingOptions::full());
    assert!(rejected.outcome.is_err());
    assert_eq!(session.snapshot().unwrap(), before);
    assert!(
        rejected
            .record
            .events
            .iter()
            .any(|event| event.kind == Kind::Rollback && event.phase == Phase::Complete)
    );
    assert!(
        !rejected
            .record
            .events
            .iter()
            .any(|event| event.kind == Kind::ProfileChange)
    );
    session.set_profile(&original).unwrap();
    assert!(!session.query_text("dog(some dog).").unwrap().is_true());
}

#[test]
fn profile_replacement_keeps_historical_sources_under_strict_mode() {
    let session = session("~dog(Adam). dog(Adam). ~cat(Bob).");
    let history = session.snapshot().unwrap().assertions;
    let strict = EngineProfile {
        strict: true,
        ..session.profile()
    };
    for options in modes() {
        session
            .set_profile_recorded(&strict, options)
            .outcome
            .unwrap();
        assert!(session.query_text("dog(Adam).").unwrap().is_true());
        assert_eq!(session.snapshot().unwrap().assertions, history);
        let imported = EngineProfile {
            existential_import: true,
            strict: false,
            ..strict.clone()
        };
        session
            .set_profile_recorded(&imported, options)
            .outcome
            .unwrap();
        assert!(session.query_text("dog(Adam).").unwrap().is_true());
        let restored = CoreSession::from_snapshot(&session.snapshot().unwrap()).unwrap();
        assert_eq!(restored.profile(), imported);
    }
}

#[derive(Default)]
struct EventCounter(std::sync::atomic::AtomicUsize);
impl ExecutionObserver for EventCounter {
    fn observe(&self, _: ExecutionEvent) {
        self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
    fn compilation(&self, _: CompilationArtifact) {}
    fn phase(&self, _: Phase) {}
}

#[test]
fn shared_recording_lifecycle_restores_the_previous_observer_after_success_and_error() {
    let session = session("dog(Adam).");
    let previous = Arc::new(EventCounter::default());
    session
        .kb()
        .replace_execution_observer(Some(previous.clone()));
    for options in modes() {
        session
            .query_find_text_recorded("dog($x).", options)
            .outcome
            .unwrap();
        assert!(
            session
                .compile_text_recorded("uncommitted($x).", true, options)
                .outcome
                .is_err()
        );
        session
            .check_contradictions_recorded(options)
            .outcome
            .unwrap();
        assert_eq!(previous.0.load(std::sync::atomic::Ordering::Relaxed), 0);
    }
    session.query_text("dog(Adam).").unwrap();
    assert!(previous.0.load(std::sync::atomic::Ordering::Relaxed) > 0);
}

#[derive(Default)]
struct PhaseTap(Mutex<Vec<Phase>>);
impl ExecutionObserver for PhaseTap {
    fn observe(&self, _: ExecutionEvent) {
        panic!("host tap receives phases only")
    }
    fn compilation(&self, _: CompilationArtifact) {
        panic!("host tap receives phases only")
    }
    fn phase(&self, phase: Phase) {
        self.0.lock().unwrap().push(phase);
    }
}

#[test]
fn every_new_operation_taps_real_phases_even_when_recording_is_disabled() {
    let session = session("dog(Adam).");
    let tap = Arc::new(PhaseTap::default());
    let off = RecordingOptions::disabled();
    session
        .compile_text_recorded_with_phase_observer("dog(Adam).", true, off, tap.clone())
        .outcome
        .unwrap();
    session
        .query_find_text_recorded_with_phase_observer("dog($x).", off, tap.clone())
        .outcome
        .unwrap();
    session
        .count_witnesses_text_recorded_with_phase_observer("dog($x).", off, tap.clone())
        .outcome
        .unwrap();
    session
        .aggregate_text_recorded_with_phase_observer(
            "dog($x).",
            "$x",
            AggregateOp::Sum,
            off,
            tap.clone(),
        )
        .outcome
        .unwrap();
    session
        .check_contradictions_recorded_with_phase_observer(off, tap.clone())
        .outcome
        .unwrap();
    session
        .set_profile_recorded_with_phase_observer(&session.profile(), off, tap.clone())
        .outcome
        .unwrap();
    let phases = tap.0.lock().unwrap();
    for phase in [
        Phase::Compile,
        Phase::Admission,
        Phase::Enumeration,
        Phase::ConstraintScan,
        Phase::Configuration,
        Phase::Complete,
    ] {
        assert!(phases.contains(&phase), "missing {phase:?}");
    }
}

#[test]
fn native_unrecoverable_sessions_still_return_truthful_operation_results() {
    let session = session("dog(Adam).");
    session.kb().declare_entity_sort("Adam", "person");
    let before = session.query_find_text_outcome("dog($x).").unwrap();
    let recorded = session.query_find_text_recorded("dog($x).", RecordingOptions::full());
    assert_eq!(recorded.outcome.unwrap(), before);
    assert_eq!(recorded.record.status, RecordingStatus::Complete);
    assert!(recorded.record.initial_snapshot.is_none());
    assert!(recorded.record.snapshot_unavailable_reason.is_some());
    assert!(
        !recorded
            .record
            .capabilities
            .iter()
            .any(|capability| capability == "recoverable_snapshot")
    );
}
