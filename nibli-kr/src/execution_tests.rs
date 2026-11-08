use nibli_types::execution::{
    CompilationArtifact, ExecutionEvent, ExecutionEventKind, ExecutionObserver, ExecutionPhase,
};
use std::sync::Mutex;

#[derive(Default)]
struct Observations {
    events: Mutex<Vec<ExecutionEvent>>,
    artifacts: Mutex<Vec<CompilationArtifact>>,
}
impl ExecutionObserver for Observations {
    fn observe(&self, event: ExecutionEvent) {
        self.events.lock().unwrap().push(event);
    }
    fn phase(&self, _: ExecutionPhase) {}
    fn compilation(&self, artifact: CompilationArtifact) {
        self.artifacts.lock().unwrap().push(artifact);
    }
}

#[test]
fn recorded_compilation_preserves_logic_and_parser_statement_spans() {
    let text = "greater(3.5, 2). dog(Adam).";
    let expected = nibli_semantics::compile_from_ast(super::parse_checked(text).unwrap()).unwrap();
    let observer = Observations::default();
    let ast = super::parse_checked_with_observer(text, &observer, "source-1").unwrap();
    let actual =
        nibli_semantics::compile_from_ast_with_observer(ast, &observer, "source-1").unwrap();
    assert_eq!(actual, expected);
    let artifacts = observer.artifacts.lock().unwrap();
    let parsed = artifacts
        .iter()
        .find(|a| !a.parsed_sentences.is_empty())
        .unwrap();
    assert_eq!(parsed.statement_spans.len(), 2);
    let spans = parsed
        .statement_spans
        .iter()
        .map(|s| &text[s.start..s.end])
        .collect::<Vec<_>>();
    assert_eq!(spans, ["greater(3.5, 2).", "dog(Adam)."]);
    assert!(!parsed.parsed_sentences.is_empty());
    assert_eq!(artifacts.last().unwrap().logic.as_ref(), Some(&expected));
    let events = observer.events.lock().unwrap();
    assert_eq!(
        events
            .iter()
            .filter(|e| e.kind == ExecutionEventKind::Parse)
            .count(),
        2
    );
    assert!(events.iter().any(|e| e.kind == ExecutionEventKind::Lower));
    assert!(events.iter().all(|e| {
        e.source
            .as_ref()
            .is_some_and(|s| s.artifact_id == "source-1")
    }));
}

#[test]
fn rejected_emission_does_not_claim_successful_lowering() {
    let text = "unknown_uncommitted_relation(Adam).";
    let observer = Observations::default();
    let plain = super::parse_checked(text).unwrap_err().to_string();
    let recorded = super::parse_checked_with_observer(text, &observer, "bad")
        .unwrap_err()
        .to_string();
    assert_eq!(plain, recorded);
    assert!(
        observer
            .artifacts
            .lock()
            .unwrap()
            .iter()
            .any(|a| a.id == "bad" && a.source == text)
    );
    let events = observer.events.lock().unwrap();
    assert!(events.iter().any(|e| e.kind == ExecutionEventKind::Parse));
    assert!(
        events
            .iter()
            .any(|e| e.kind == ExecutionEventKind::Validate && e.detail.contains("rejected"))
    );
    assert!(!events.iter().any(|e| e.kind == ExecutionEventKind::Lower));
}

#[test]
fn corrupt_ast_is_rejected_before_recorded_lowering() {
    let mut ast = super::parse_checked("dog(Adam).").unwrap();
    ast.roots[0] = u32::MAX;
    let observer = Observations::default();
    assert!(nibli_semantics::compile_from_ast_with_observer(ast, &observer, "corrupt").is_err());
    let events = observer.events.lock().unwrap();
    assert!(
        events
            .iter()
            .any(|e| e.kind == ExecutionEventKind::Validate && e.detail.contains("rejected"))
    );
    assert!(!events.iter().any(|e| e.kind == ExecutionEventKind::Lower));
}
