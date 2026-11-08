//! Bounded observations of the actual compiler and reasoner; proofs remain certificates.
use std::collections::{HashMap, HashSet, hash_map::Entry};
use std::sync::{Arc, Mutex};

use super::CoreSession;
use nibli_types::error::NibliError;
use nibli_types::execution::*;
use nibli_types::logic::{EngineProfile, LogicBuffer, ProofTrace, QueryResult};

pub struct Recorded<T> {
    pub outcome: Result<T, NibliError>,
    pub record: ExecutionRecord,
}

struct CollectorState {
    record: ExecutionRecord,
    phase: ExecutionPhase,
    frames: Vec<String>,
    sequence: u64,
    source_artifact: Option<String>,
    notified_phase: Option<ExecutionPhase>,
}
struct Collector(Mutex<CollectorState>, Option<ExecutionObserverHandle>);

impl Collector {
    fn new(
        session: &CoreSession,
        input: String,
        mut options: RecordingOptions,
        phase_observer: Option<ExecutionObserverHandle>,
    ) -> Self {
        let ceiling = match options.mode {
            RecordingMode::Disabled => RecordingOptions::disabled(),
            RecordingMode::Standard => RecordingOptions::standard(),
            RecordingMode::Full => RecordingOptions::full(),
        };
        options.max_events = options.max_events.min(ceiling.max_events);
        options.max_bytes = options.max_bytes.min(ceiling.max_bytes);
        let mut record = ExecutionRecord {
            schema_version: EXECUTION_SCHEMA_VERSION,
            engine_version: env!("CARGO_PKG_VERSION").into(),
            capabilities: vec![
                "compiler".into(),
                "search".into(),
                "probe_and_proof".into(),
                "atomic_changes".into(),
                "recoverable_snapshot".into(),
            ],
            options,
            status: if options.mode == RecordingMode::Disabled {
                RecordingStatus::Disabled
            } else {
                RecordingStatus::Complete
            },
            truncation_reason: None,
            recorded_bytes: 0,
            input: String::new(),
            profile: session.execution_profile(),
            snapshot_unavailable_reason: None,
            initial_snapshot: None,
            final_snapshot: None,
            artifacts: vec![],
            events: vec![],
            result: None,
            error: None,
        };
        if options.mode != RecordingMode::Disabled {
            let input_bytes = serde_json::to_vec(&input)
                .expect("input serialization")
                .len();
            if input_bytes <= options.max_bytes {
                record.recorded_bytes = input_bytes;
                record.input = input;
            } else {
                truncate(&mut record, "input exceeds recording byte budget");
            }
        }
        let collector = Self(
            Mutex::new(CollectorState {
                record,
                phase: ExecutionPhase::Compile,
                frames: vec![],
                sequence: 0,
                source_artifact: None,
                notified_phase: None,
            }),
            phase_observer,
        );
        if options.mode != RecordingMode::Disabled {
            match session.snapshot() {
                Ok(snapshot) => collector.snapshot(snapshot, false),
                Err(error) => collector.snapshot_unavailable(error),
            }
        }
        collector
    }
    fn snapshot_unavailable(&self, error: NibliError) {
        let mut state = self.0.lock().unwrap();
        state
            .record
            .capabilities
            .retain(|capability| capability != "recoverable_snapshot");
        state.record.snapshot_unavailable_reason = Some(error.to_string());
    }
    fn snapshot(&self, snapshot: SessionSnapshot, final_state: bool) {
        let mut state = self.0.lock().unwrap();
        if state.record.status == RecordingStatus::Disabled {
            return;
        }
        let bytes = serde_json::to_vec(&snapshot)
            .expect("snapshot serialization")
            .len();
        if fits(&state.record, bytes) {
            state.record.recorded_bytes += bytes;
            if final_state {
                state.record.final_snapshot = Some(snapshot);
            } else {
                state.record.initial_snapshot = Some(snapshot);
            }
        } else {
            truncate(&mut state.record, "snapshot exceeds recording byte budget");
        }
    }
    fn finish(&self, result: Option<QueryResult>, error: Option<String>) -> ExecutionRecord {
        let mut state = self.0.lock().unwrap();
        state.record.result = result;
        if let Some(error) = error {
            if state.record.status != RecordingStatus::Disabled
                && state.record.status != RecordingStatus::Truncated
            {
                state.record.status = RecordingStatus::Aborted;
            }
            // Error summaries are bounded too. The typed outcome retains the full error.
            let remaining = state
                .record
                .options
                .max_bytes
                .saturating_sub(state.record.recorded_bytes);
            let mut low = 0;
            let mut high = error.len().min(remaining);
            while low < high {
                let mut middle = low + (high - low).div_ceil(2);
                while !error.is_char_boundary(middle) {
                    middle -= 1;
                }
                if middle == low {
                    break;
                }
                let bytes = serde_json::to_vec(&error[..middle])
                    .expect("error serialization")
                    .len();
                if bytes <= remaining {
                    low = middle;
                } else {
                    high = middle - 1;
                }
            }
            let bytes = serde_json::to_vec(&error[..low])
                .expect("error serialization")
                .len();
            if bytes <= remaining {
                state.record.recorded_bytes += bytes;
                state.record.error = Some(error[..low].to_owned());
            }
        }
        state.record.clone()
    }
}
fn fits(record: &ExecutionRecord, bytes: usize) -> bool {
    record
        .recorded_bytes
        .checked_add(bytes)
        .is_some_and(|n| n <= record.options.max_bytes)
}
fn truncate(record: &mut ExecutionRecord, reason: &str) {
    if record.status != RecordingStatus::Disabled {
        record.status = RecordingStatus::Truncated;
        if record.truncation_reason.is_none() {
            record.truncation_reason = Some(reason.into());
        }
    }
}
impl ExecutionObserver for Collector {
    fn recording_enabled(&self) -> bool {
        !matches!(
            self.0.lock().unwrap().record.status,
            RecordingStatus::Disabled | RecordingStatus::Truncated
        )
    }
    fn phase(&self, phase: ExecutionPhase) {
        let changed = {
            let mut state = self.0.lock().unwrap();
            state.phase = phase;
            let changed = state.notified_phase != Some(phase);
            state.notified_phase = Some(phase);
            changed
        };
        // The host callback never runs under the collector mutex. It receives
        // only stage transitions, independent of history truncation or disabling.
        if changed && let Some(observer) = &self.1 {
            observer.phase(phase);
        }
    }
    fn observe(&self, mut event: ExecutionEvent) {
        let mut state = self.0.lock().unwrap();
        if matches!(
            state.record.status,
            RecordingStatus::Disabled | RecordingStatus::Truncated
        ) {
            return;
        }
        if state.record.events.len() >= state.record.options.max_events {
            truncate(&mut state.record, "event count budget reached");
            return;
        }
        event.sequence = state.sequence.to_string();
        event.phase = state.phase;
        if event.source.is_none() && event.state.logic_node.is_some() {
            event.source = state.source_artifact.as_ref().map(|id| SourceReference {
                artifact_id: id.clone(),
                span: None,
            });
        }
        if event.kind == ExecutionEventKind::GoalEnter {
            event.parent_frame_id = state.frames.last().cloned();
            event.frame_id = Some(event.sequence.clone());
        } else {
            event.frame_id = state.frames.last().cloned();
            event.parent_frame_id = state.frames.iter().rev().nth(1).cloned();
        }
        // Include an array separator byte (also for the first item, conservatively).
        let bytes = serde_json::to_vec(&event)
            .expect("event serialization")
            .len()
            + 1;
        if !fits(&state.record, bytes) {
            truncate(&mut state.record, "event byte budget reached");
            return;
        }
        if event.kind == ExecutionEventKind::GoalEnter {
            state.frames.push(event.sequence.clone());
        }
        if event.kind == ExecutionEventKind::GoalExit {
            state.frames.pop();
        }
        state.sequence += 1;
        state.record.recorded_bytes += bytes;
        state.record.events.push(event);
    }
    fn compilation(&self, mut artifact: CompilationArtifact) {
        let mut state = self.0.lock().unwrap();
        if matches!(
            state.record.status,
            RecordingStatus::Disabled | RecordingStatus::Truncated
        ) {
            return;
        }
        state.source_artifact = Some(artifact.id.clone());
        let existing = state
            .record
            .artifacts
            .iter()
            .position(|a| a.id == artifact.id);
        let old_bytes = if let Some(i) = existing {
            let old = &state.record.artifacts[i];
            if artifact.source.is_empty() {
                artifact.source = old.source.clone();
            }
            if artifact.statement_spans.is_empty() {
                artifact.statement_spans = old.statement_spans.clone();
            }
            if artifact.parsed_predicates.is_empty() {
                artifact.parsed_predicates = old.parsed_predicates.clone();
            }
            if artifact.parsed_arguments.is_empty() {
                artifact.parsed_arguments = old.parsed_arguments.clone();
            }
            if artifact.parsed_sentences.is_empty() {
                artifact.parsed_sentences = old.parsed_sentences.clone();
            }
            if artifact.parsed_roots.is_empty() {
                artifact.parsed_roots = old.parsed_roots.clone();
            }
            if artifact.logic.is_none() {
                artifact.logic = old.logic.clone();
            }
            if artifact.lowered_logic.is_none() {
                artifact.lowered_logic = old.lowered_logic.clone();
            }
            serde_json::to_vec(old)
                .expect("artifact serialization")
                .len()
                + 1
        } else {
            0
        };
        let bytes = serde_json::to_vec(&artifact)
            .expect("artifact serialization")
            .len()
            + 1;
        if state.record.recorded_bytes - old_bytes + bytes > state.record.options.max_bytes {
            truncate(&mut state.record, "compiler artifact byte budget reached");
            return;
        }
        state.record.recorded_bytes = state.record.recorded_bytes - old_bytes + bytes;
        if let Some(i) = existing {
            state.record.artifacts[i] = artifact;
        } else {
            state.record.artifacts.push(artifact);
        }
    }
}

fn decimal_id(value: &str) -> Result<u64, NibliError> {
    value
        .parse::<u64>()
        .ok()
        .filter(|n| n.to_string() == value)
        .ok_or_else(|| {
            NibliError::Reasoning(format!("invalid canonical decimal assertion ID: {value}"))
        })
}

impl CoreSession {
    fn execution_profile(&self) -> EngineProfile {
        EngineProfile {
            strict: self.kb.is_strict(),
            existential_import: self.kb.is_existential_import(),
            materialization: self.kb.materialization_enabled(),
            max_chain_depth: self.max_chain_depth(),
        }
    }
    pub fn snapshot(&self) -> Result<SessionSnapshot, NibliError> {
        self.kb.validate_source_snapshot_configuration()?;
        let assertions = self.kb.snapshot_assertions()?;
        self.validate_snapshot_sources(&assertions)?;
        let mut compute_predicates: Vec<_> = self.compute_predicates.iter().cloned().collect();
        compute_predicates.sort();
        Ok(SessionSnapshot {
            schema_version: SNAPSHOT_SCHEMA_VERSION,
            engine_version: env!("CARGO_PKG_VERSION").into(),
            profile: self.execution_profile(),
            compute_predicates,
            assertions,
            next_fact_id: self.kb.assertion_id_frontier()?.to_string(),
            derived_only: self.kb.derived_only_relations(),
            admitted: self.kb.admitted_relations(),
        })
    }
    // Both export and import establish the source-replay contract. Identical
    // multi-root packets compile once per call; withdrawn labels stay inert.
    fn validate_snapshot_sources(
        &self,
        assertions: &[SnapshotAssertion],
    ) -> Result<(), NibliError> {
        let mut compiled: HashMap<&str, Vec<LogicBuffer>> = HashMap::new();
        for record in assertions {
            let Some(buffer) = &record.buffer else {
                continue;
            };
            let roots = match compiled.entry(record.label.as_str()) {
                Entry::Occupied(entry) => entry.into_mut(),
                Entry::Vacant(entry) => {
                    let logic = self.compile_text(&record.label).map_err(|_| {
                        // IDs were minted by the KB or checked before this helper.
                        // Do not copy arbitrary source/compiler diagnostics into
                        // the recorder's bounded snapshot-availability summary.
                        NibliError::Reasoning(format!(
                            "source snapshot assertion #{} has no recompilable KR label",
                            record.id
                        ))
                    })?;
                    entry.insert(logic.split_roots())
                }
            };
            if !roots.iter().any(|root| root == buffer) {
                return Err(NibliError::Reasoning(format!(
                    "source snapshot assertion #{} does not match its compiled KR root",
                    record.id
                )));
            }
        }
        Ok(())
    }

    /// Validate sources and IDs, then rebuild into a fresh unpublished session.
    /// Compiled payloads are checked against canonical compilation, never trusted.
    pub fn from_snapshot(snapshot: &SessionSnapshot) -> Result<Self, NibliError> {
        let invalid = |s: &str| NibliError::Reasoning(format!("invalid session snapshot: {s}"));
        if snapshot.schema_version != SNAPSHOT_SCHEMA_VERSION
            || snapshot.engine_version != env!("CARGO_PKG_VERSION")
        {
            return Err(invalid("schema or engine version mismatch"));
        }
        let frontier = decimal_id(&snapshot.next_fact_id)?;
        for registry in [&snapshot.derived_only, &snapshot.admitted] {
            let mut previous: Option<&str> = None;
            for relation in registry {
                // Declaration payloads are literal data, not surface aliases or
                // executable identifiers. Preserve even withdrawn declarations.
                if previous.is_some_and(|p| p >= relation.as_str()) {
                    return Err(invalid("unsorted or duplicate admission relation"));
                }
                previous = Some(relation);
            }
        }
        let mut session = Self::new();
        session.set_max_chain_depth(snapshot.profile.max_chain_depth)?;
        session.set_existential_import(snapshot.profile.existential_import)?;
        session.set_materialization(snapshot.profile.materialization);
        let mut compute = HashSet::new();
        for name in &snapshot.compute_predicates {
            if super::canonical_corpus_relation(name) != Some(name.as_str())
                || !compute.insert(name.clone())
            {
                return Err(invalid("invalid or duplicate compute predicate"));
            }
        }
        session.compute_predicates = compute;
        let mut identities = HashSet::new();
        let mut records = Vec::new();
        for record in &snapshot.assertions {
            let id = decimal_id(&record.id)?;
            if id >= frontier || !identities.insert(id) {
                return Err(invalid("duplicate ID or invalid frontier"));
            }
            records.push((id, record));
        }
        session.validate_snapshot_sources(&snapshot.assertions)?;
        records.sort_by_key(|(id, _)| *id);
        session.kb.transaction(|candidate| {
            for (id, record) in records {
                if let Some(buffer) = &record.buffer {
                    candidate
                        .assert_fact_with_id(buffer.clone(), record.label.clone(), id)
                        .map_err(NibliError::Reasoning)?;
                } else {
                    candidate.restore_withdrawn_assertion(id, record.label.clone())?;
                }
            }
            candidate.restore_next_fact_id(frontier)?;
            // Explicit programmatic declarations can grandfather older sources.
            for relation in &snapshot.derived_only {
                candidate.declare_derived(relation);
            }
            for relation in &snapshot.admitted {
                candidate.declare_admitted(relation);
            }
            if candidate.derived_only_relations() != snapshot.derived_only
                || candidate.admitted_relations() != snapshot.admitted
            {
                return Err(invalid(
                    "admission metadata disagrees with source declarations",
                ));
            }
            // Strict governs future admission. Sources accepted before a later
            // strict toggle must replay faithfully, as ordinary rebuild does.
            candidate.set_strict(snapshot.profile.strict);
            Ok(())
        })?;
        Ok(session)
    }
    fn compile_observed(
        &self,
        text: &str,
        observer: &dyn ExecutionObserver,
        artifact_id: &str,
    ) -> Result<LogicBuffer, NibliError> {
        observer.phase(ExecutionPhase::Compile);
        let ast = nibli_kr::parse_checked_with_observer(text, observer, artifact_id)?;
        let mut buffer =
            nibli_semantics::compile_from_ast_with_observer(ast, observer, artifact_id)?;
        nibli_reason::transform_compute_nodes(&mut buffer, &self.compute_predicates);
        let mut event = ExecutionEvent::new(
            ExecutionEventKind::ComputeMark,
            "Applied the session compute registry to the compiled buffer",
        );
        event.source = Some(SourceReference {
            artifact_id: artifact_id.into(),
            span: None,
        });
        observer.observe(event);
        observer.compilation(CompilationArtifact {
            id: artifact_id.into(),
            source: String::new(),
            statement_spans: vec![],
            parsed_predicates: vec![],
            parsed_arguments: vec![],
            parsed_sentences: vec![],
            parsed_roots: vec![],
            lowered_logic: None,
            logic: Some(buffer.clone()),
        });
        Ok(buffer)
    }
    pub fn query_text_recorded(
        &self,
        text: &str,
        options: RecordingOptions,
    ) -> Recorded<(QueryResult, ProofTrace)> {
        self.query_text_recorded_inner(text, options, None)
    }

    /// Run with a live host phase tap. Only `observer.phase` is called; event and
    /// artifact payloads remain in the bounded record. The callback must not
    /// re-enter this session. Notifications describe phase entry, not completion.
    pub fn query_text_recorded_with_phase_observer(
        &self,
        text: &str,
        options: RecordingOptions,
        observer: ExecutionObserverHandle,
    ) -> Recorded<(QueryResult, ProofTrace)> {
        self.query_text_recorded_inner(text, options, Some(observer))
    }

    fn query_text_recorded_inner(
        &self,
        text: &str,
        options: RecordingOptions,
        phase_observer: Option<ExecutionObserverHandle>,
    ) -> Recorded<(QueryResult, ProofTrace)> {
        let observing = options.mode != RecordingMode::Disabled || phase_observer.is_some();
        let collector = Arc::new(Collector::new(self, text.into(), options, phase_observer));
        let previous = self.kb.replace_execution_observer(if observing {
            Some(collector.clone())
        } else {
            None
        });
        let outcome = (|| {
            collector.phase(ExecutionPhase::Compile);
            let buffer = if options.mode == RecordingMode::Disabled {
                self.compile_query_text(text)?
            } else {
                self.compile_observed(text, collector.as_ref(), "0")?
            };
            self.kb.query_entailment_with_proof(buffer)
        })();
        self.kb.replace_execution_observer(previous);
        collector.phase(ExecutionPhase::Complete);
        let mut event = ExecutionEvent::new(ExecutionEventKind::Outcome, "Query completed");
        event.result = outcome.as_ref().ok().map(|(r, _)| r.clone());
        collector.observe(event);
        let record = collector.finish(
            outcome.as_ref().ok().map(|(r, _)| r.clone()),
            outcome.as_ref().err().map(ToString::to_string),
        );
        Recorded { outcome, record }
    }
    pub fn apply_changes_recorded(
        &self,
        changes: &[SessionChange],
        options: RecordingOptions,
    ) -> Recorded<ChangeResult> {
        self.apply_changes_recorded_inner(changes, options, None)
    }

    /// Atomic changes with phase-entry notifications for worker progress and
    /// cancellation coordination. Only `observer.phase` is forwarded.
    pub fn apply_changes_recorded_with_phase_observer(
        &self,
        changes: &[SessionChange],
        options: RecordingOptions,
        observer: ExecutionObserverHandle,
    ) -> Recorded<ChangeResult> {
        self.apply_changes_recorded_inner(changes, options, Some(observer))
    }

    fn apply_changes_recorded_inner(
        &self,
        changes: &[SessionChange],
        options: RecordingOptions,
        phase_observer: Option<ExecutionObserverHandle>,
    ) -> Recorded<ChangeResult> {
        let observing = options.mode != RecordingMode::Disabled || phase_observer.is_some();
        let input = serde_json::to_string(changes).expect("change serialization");
        let collector = Arc::new(Collector::new(self, input, options, phase_observer));
        let previous = self.kb.replace_execution_observer(if observing {
            Some(collector.clone())
        } else {
            None
        });
        collector.phase(ExecutionPhase::Mutation);
        let outcome = self.kb.transaction(|candidate| {
            let mut operation_ids = Vec::new();
            for (index, change) in changes.iter().enumerate() {
                match change {
                    SessionChange::Assert { text } => {
                        collector.phase(ExecutionPhase::Compile);
                        let buffer = if options.mode == RecordingMode::Disabled {
                            self.compile_text(text)?
                        } else {
                            self.compile_observed(text, collector.as_ref(), &index.to_string())?
                        };
                        collector.phase(ExecutionPhase::Admission);
                        candidate.validate_assertion(&buffer)?;
                        let mut ids = Vec::new();
                        for root in buffer.split_roots() {
                            ids.push(candidate.assert_fact(root, text.clone())?.to_string());
                        }
                        operation_ids.push(ids);
                    }
                    SessionChange::Withdraw { id } => {
                        collector.phase(ExecutionPhase::Mutation);
                        candidate.retract_fact(decimal_id(id)?)?;
                        operation_ids.push(vec![id.clone()]);
                    }
                }
            }
            Ok(ChangeResult { operation_ids })
        });
        self.kb.replace_execution_observer(previous);
        if options.mode != RecordingMode::Disabled {
            match self.snapshot() {
                Ok(snapshot) => collector.snapshot(snapshot, true),
                Err(error) => collector.snapshot_unavailable(error),
            }
        }
        collector.phase(ExecutionPhase::Complete);
        collector.observe(ExecutionEvent::new(
            if outcome.is_ok() {
                ExecutionEventKind::Commit
            } else {
                ExecutionEventKind::Rollback
            },
            if outcome.is_ok() {
                "Whole change set is now live"
            } else {
                "Whole change set discarded; original session retained"
            },
        ));
        let record = collector.finish(None, outcome.as_ref().err().map(ToString::to_string));
        Recorded { outcome, record }
    }
}
