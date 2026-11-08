//! Typed collection results preserve the compatibility API and expose real
//! enumeration attempts without presenting provisional bindings as final rows.
use super::*;
use nibli_types::execution::{CompilationArtifact, ExecutionObserver};
use nibli_types::logic::{AggregateOp, AggregateOutcome};
use std::sync::Mutex;

#[derive(Default)]
struct Observations {
    disabled: bool,
    events: Mutex<Vec<ExecutionEvent>>,
    phases: Mutex<Vec<ExecutionPhase>>,
}

impl ExecutionObserver for Observations {
    fn recording_enabled(&self) -> bool {
        !self.disabled
    }
    fn observe(&self, event: ExecutionEvent) {
        self.events.lock().unwrap().push(event);
    }
    fn phase(&self, phase: ExecutionPhase) {
        self.phases.lock().unwrap().push(phase);
    }
    fn compilation(&self, _: CompilationArtifact) {}
}

fn reasoning_message(error: NibliError) -> String {
    match error {
        NibliError::Reasoning(message) => message,
        other => panic!("expected reasoning error, got {other:?}"),
    }
}

fn unavailable<T: std::fmt::Debug>(outcome: CollectionOutcome<T>) -> CollectionFailure {
    match outcome {
        CollectionOutcome::Unavailable(failure) => failure,
        complete => panic!("expected unavailable collection, got {complete:?}"),
    }
}

#[test]
fn complete_answers_and_counts_preserve_empty_and_equality_deduplication() {
    let kb = new_kb();
    let query = compile_surface("dog($x).");
    assert_eq!(
        kb.query_find_outcome(query.clone()).unwrap(),
        CollectionOutcome::Complete(vec![])
    );
    assert_eq!(
        kb.count_witnesses_outcome(query.clone()).unwrap(),
        CollectionOutcome::Complete(0)
    );
    assert_buf(&kb, compile_surface("dog(Adam). dog(Bob). Adam = Bob."));
    let original = kb.query_find(query.clone()).unwrap();
    assert_eq!(original.len(), 1, "equal entities count once");
    assert_eq!(
        kb.query_find_outcome(query.clone()).unwrap(),
        CollectionOutcome::Complete(original)
    );
    assert_eq!(
        kb.count_witnesses_outcome(query.clone()).unwrap(),
        CollectionOutcome::Complete(1)
    );
    assert_eq!(kb.count_witnesses(query).unwrap(), 1);
}

#[test]
fn incomplete_find_count_and_aggregate_keep_exact_legacy_diagnostics() {
    let kb = new_kb();
    kb.set_materialization(false);
    let query = compile_surface("sum(Adam, 2, 3).");
    let failure = unavailable(kb.query_find_outcome(query.clone()).unwrap());
    assert_eq!(failure.kind, CollectionFailureKind::IncompleteEnumeration);
    assert_eq!(
        failure.message,
        reasoning_message(kb.query_find(query.clone()).unwrap_err())
    );
    let counted = unavailable(kb.count_witnesses_outcome(query.clone()).unwrap());
    assert_eq!(counted, failure);
    assert_eq!(
        counted.message,
        reasoning_message(kb.count_witnesses(query.clone()).unwrap_err())
    );
    let aggregate = unavailable(
        kb.aggregate_outcome(query.clone(), "$x", AggregateOp::Sum)
            .unwrap(),
    );
    assert_eq!(aggregate, failure);
    assert_eq!(
        aggregate.message,
        reasoning_message(kb.aggregate(query, "$x", AggregateOp::Sum).unwrap_err())
    );

    // A definitive false conjunct absorbs the unresolved branch. The typed
    // boundary must not turn this existing complete-empty result into failure.
    let absent = compile_surface("sum(Adam, 2, 3) & dog(Adam).");
    assert_eq!(
        kb.query_find_outcome(absent).unwrap(),
        CollectionOutcome::Complete(vec![])
    );
}

#[test]
fn enumeration_events_capture_rejected_candidates_and_only_final_distinct_rows() {
    let kb = new_kb();
    kb.set_materialization(false);
    assert_buf(&kb, compile_surface("dog(Adam). cat(Bob). person(Cara)."));
    let before = kb.list_assertion_records().unwrap();
    let observations = Arc::new(Observations::default());
    kb.replace_execution_observer(Some(observations.clone()));
    let query = compile_surface("dog($x) | cat($x).");
    let recorded = kb.query_find_outcome(query.clone()).unwrap();
    let CollectionOutcome::Complete(rows) = &recorded else {
        panic!("expected complete rows: {recorded:?}");
    };
    assert_eq!(rows.len(), 2);
    let events = observations.events.lock().unwrap();
    assert!(events.iter().any(|event| {
        event.kind == EK::EnumerationCandidate
            && event.state.candidate.as_deref() == Some("Constant(\"cara\")")
    }));
    let accepted: Vec<_> = events
        .iter()
        .filter(|event| event.kind == EK::EnumerationBinding)
        .collect();
    assert_eq!(accepted.len(), rows.len());
    assert!(accepted.iter().all(|event| {
        event
            .state
            .bindings
            .iter()
            .all(|binding| binding.value != "Constant(\"cara\")")
    }));
    assert!(events.iter().all(|event| event.proof_node.is_none()));
    drop(events);
    assert!(
        observations
            .phases
            .lock()
            .unwrap()
            .contains(&ExecutionPhase::Enumeration)
    );
    let disabled = Arc::new(Observations {
        disabled: true,
        ..Observations::default()
    });
    kb.replace_execution_observer(Some(disabled.clone()));
    assert_eq!(kb.query_find_outcome(query).unwrap(), recorded);
    assert!(disabled.events.lock().unwrap().is_empty());
    assert_eq!(kb.list_assertion_records().unwrap(), before);
}

#[test]
fn increasing_depth_can_repair_an_unavailable_collection() {
    let kb = new_kb();
    kb.set_materialization(false);
    assert_buf(
        &kb,
        compile_surface("dog(Adam). animal(every dog). alive(every animal)."),
    );
    kb.set_max_chain_depth(1).unwrap();
    let query = compile_surface("alive($x).");
    assert_eq!(
        unavailable(kb.query_find_outcome(query.clone()).unwrap()).kind,
        CollectionFailureKind::IncompleteEnumeration
    );
    kb.set_max_chain_depth(10).unwrap();
    assert_eq!(
        kb.count_witnesses_outcome(query).unwrap(),
        CollectionOutcome::Complete(1)
    );
}

#[test]
fn incomplete_enumeration_never_emits_final_binding_events() {
    let kb = new_kb();
    kb.set_materialization(false);
    assert_buf(&kb, compile_surface("dog(Adam)."));
    let observations = Arc::new(Observations::default());
    kb.replace_execution_observer(Some(observations.clone()));
    let outcome = kb
        .query_find_outcome(compile_surface("dog($x) | sum(Adam, 2, 3)."))
        .unwrap();
    assert_eq!(
        unavailable(outcome).kind,
        CollectionFailureKind::IncompleteEnumeration
    );
    let events = observations.events.lock().unwrap();
    assert!(
        events
            .iter()
            .any(|event| event.kind == EK::EnumerationCandidate)
    );
    assert!(
        events
            .iter()
            .any(|event| event.kind == EK::EnumerationIncomplete)
    );
    assert!(
        events
            .iter()
            .all(|event| event.kind != EK::EnumerationBinding)
    );
}

#[test]
fn aggregates_distinguish_empty_finite_and_invalid_selected_columns() {
    let kb = new_kb();
    let query = compile_surface("quantity($x, $n).");
    assert_eq!(
        kb.aggregate_outcome(query.clone(), "$n", AggregateOp::Sum)
            .unwrap(),
        CollectionOutcome::Complete(AggregateOutcome::Empty)
    );
    assert_buf(&kb, compile_surface("quantity(Adam, 3). quantity(Bob, 7)."));
    for (op, value) in [
        (AggregateOp::Sum, 10.0),
        (AggregateOp::Min, 3.0),
        (AggregateOp::Max, 7.0),
        (AggregateOp::Avg, 5.0),
    ] {
        assert_eq!(
            kb.aggregate_outcome(query.clone(), "$n", op.clone())
                .unwrap(),
            CollectionOutcome::Complete(AggregateOutcome::Value {
                value,
                witnesses: 2,
            })
        );
        assert_eq!(
            kb.aggregate(query.clone(), "$n", op).unwrap(),
            AggregateOutcome::Value {
                value,
                witnesses: 2,
            }
        );
    }
    let missing = unavailable(
        kb.aggregate_outcome(query.clone(), "$missing", AggregateOp::Sum)
            .unwrap(),
    );
    assert_eq!(missing.kind, CollectionFailureKind::UnboundVariable);
    assert_eq!(
        missing.message,
        reasoning_message(
            kb.aggregate(query.clone(), "$missing", AggregateOp::Sum)
                .unwrap_err()
        )
    );
    assert_buf(&kb, compile_surface("quantity(Cara, Blue)."));
    let nonnumeric = unavailable(
        kb.aggregate_outcome(query.clone(), "$n", AggregateOp::Sum)
            .unwrap(),
    );
    assert_eq!(nonnumeric.kind, CollectionFailureKind::NonNumericValue);
    assert_eq!(
        nonnumeric.message,
        reasoning_message(kb.aggregate(query, "$n", AggregateOp::Sum).unwrap_err())
    );
}

// Native flat IR is intentional: nonfinite operands cannot be spelled in KR.
fn native_numbers(values: &[f64]) -> (KnowledgeBase, LogicBuffer) {
    let kb = new_kb();
    for value in values {
        assert_buf(
            &kb,
            LogicBuffer {
                nodes: vec![LogicNode::Predicate((
                    "quantity".into(),
                    vec![LogicalTerm::Number(*value), LogicalTerm::Unspecified],
                ))],
                roots: vec![0],
            },
        );
    }
    (kb, make_find_query("quantity"))
}

#[test]
fn nonfinite_operands_and_results_have_distinct_typed_failures() {
    for (values, expected) in [
        (
            vec![3.0, f64::INFINITY],
            CollectionFailureKind::NonFiniteOperand,
        ),
        (
            vec![f64::MAX, f64::MAX * 0.75],
            CollectionFailureKind::NonFiniteResult,
        ),
    ] {
        let (kb, query) = native_numbers(&values);
        let failure = unavailable(
            kb.aggregate_outcome(query.clone(), "x", AggregateOp::Sum)
                .unwrap(),
        );
        assert_eq!(failure.kind, expected);
        assert_eq!(
            failure.message,
            reasoning_message(kb.aggregate(query, "x", AggregateOp::Sum).unwrap_err())
        );
    }
}

#[test]
fn malformed_input_and_recovery_failures_remain_outer_engine_errors() {
    let kb = new_kb();
    let malformed = LogicBuffer {
        nodes: vec![],
        roots: vec![0],
    };
    let legacy = reasoning_message(kb.query_find(malformed.clone()).unwrap_err());
    assert_eq!(
        reasoning_message(kb.query_find_outcome(malformed).unwrap_err()),
        legacy
    );
    kb.require_recovery("test recovery boundary".into());
    let query = compile_surface("dog($x).");
    assert_eq!(
        reasoning_message(kb.query_find_outcome(query.clone()).unwrap_err()),
        reasoning_message(kb.query_find(query).unwrap_err())
    );
}
