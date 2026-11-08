//! Inspectable execution records, independent of a proof's selected derivation.
//!
//! These are observation DTOs, not an alternative evaluator. Identifiers which
//! cross a JSON boundary are decimal strings so browser clients preserve u64.

use std::sync::Arc;

use crate::logic::{EngineProfile, LogicBuffer, QueryResult};

pub const EXECUTION_SCHEMA_VERSION: u32 = 1;
pub const SNAPSHOT_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum RecordingMode {
    Disabled,
    Standard,
    Full,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct RecordingOptions {
    pub mode: RecordingMode,
    pub max_events: usize,
    pub max_bytes: usize,
}

impl RecordingOptions {
    pub const fn standard() -> Self {
        Self {
            mode: RecordingMode::Standard,
            max_events: 10_000,
            max_bytes: 8 * 1024 * 1024,
        }
    }

    pub const fn full() -> Self {
        Self {
            mode: RecordingMode::Full,
            max_events: 100_000,
            max_bytes: 64 * 1024 * 1024,
        }
    }

    pub const fn disabled() -> Self {
        Self {
            mode: RecordingMode::Disabled,
            max_events: 0,
            max_bytes: 0,
        }
    }
}

impl Default for RecordingOptions {
    fn default() -> Self {
        Self::standard()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum RecordingStatus {
    Disabled,
    Complete,
    Truncated,
    Aborted,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum ExecutionPhase {
    Compile,
    Admission,
    Materialization,
    Probe,
    Proof,
    Enumeration,
    ConstraintScan,
    Configuration,
    Mutation,
    Complete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum ExecutionEventKind {
    Parse,
    Validate,
    Lower,
    ComputeMark,
    SearchPass,
    GoalEnter,
    GoalExit,
    Candidate,
    Unification,
    RuleCondition,
    RuleFire,
    FactInsert,
    CacheHit,
    CacheMiss,
    CacheStore,
    CacheInvalidate,
    Witness,
    EnumerationCandidate,
    EnumerationBinding,
    EnumerationIncomplete,
    ConstraintCheck,
    ConstraintViolation,
    ConstraintGap,
    ProfileChange,
    ShortCircuit,
    CycleCut,
    DepthBound,
    ProofLink,
    Materialize,
    MutationBegin,
    Assert,
    Withdraw,
    Replay,
    Rebuild,
    Commit,
    Rollback,
    Outcome,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum MemoKind {
    PredicateResult,
    RemainingDepth,
    ProofNode,
    Compute,
    Materialization,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExecutionBinding {
    pub variable: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceReference {
    pub artifact_id: String,
    pub span: Option<SourceSpan>,
}

/// A selected operation's actual local state. The input KB is stored once in
/// the run snapshot rather than cloned into every event.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExecutionState {
    pub goal: Option<String>,
    pub logic_node: Option<u32>,
    pub depth: Option<u32>,
    pub bindings: Vec<ExecutionBinding>,
    pub candidate: Option<String>,
    pub rule: Option<String>,
    pub memo: Option<MemoKind>,
    pub memo_scope: Option<String>,
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExecutionEvent {
    /// Assigned by the run collector, never used as a logical identity.
    pub sequence: String,
    pub phase: ExecutionPhase,
    pub kind: ExecutionEventKind,
    pub frame_id: Option<String>,
    pub parent_frame_id: Option<String>,
    pub source: Option<SourceReference>,
    pub assertion_ids: Vec<String>,
    pub proof_node: Option<u32>,
    pub detail: String,
    pub state: ExecutionState,
    pub result: Option<QueryResult>,
}

impl ExecutionEvent {
    pub fn new(kind: ExecutionEventKind, detail: impl Into<String>) -> Self {
        Self {
            sequence: String::new(),
            phase: ExecutionPhase::Compile,
            kind,
            frame_id: None,
            parent_frame_id: None,
            source: None,
            assertion_ids: Vec::new(),
            proof_node: None,
            detail: detail.into(),
            state: ExecutionState::default(),
            result: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CompilationArtifact {
    pub id: String,
    pub source: String,
    pub statement_spans: Vec<SourceSpan>,
    pub parsed_predicates: Vec<String>,
    pub parsed_arguments: Vec<String>,
    pub parsed_sentences: Vec<String>,
    pub parsed_roots: Vec<u32>,
    /// Compiler output before the compute registry is applied.
    pub lowered_logic: Option<LogicBuffer>,
    /// Final IR passed to the evaluator (compute routing included).
    pub logic: Option<LogicBuffer>,
}

/// Compilation and optional structural preflight; neither installs an assertion.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CompileInspection {
    pub logic: LogicBuffer,
    pub structural_preflight: StructuralPreflight,
}

/// Structural validity does not establish admission against current knowledge.
/// Actual admission can only be tested by applying the change to a candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "status", rename_all = "snake_case"))]
pub enum StructuralPreflight {
    NotRequested,
    Passed,
    Refused { message: String },
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SnapshotAssertion {
    pub id: String,
    pub label: String,
    /// None retains a withdrawn source without interpreting its old payload.
    pub buffer: Option<LogicBuffer>,
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SessionSnapshot {
    pub schema_version: u32,
    pub engine_version: String,
    pub profile: EngineProfile,
    pub compute_predicates: Vec<String>,
    pub assertions: Vec<SnapshotAssertion>,
    pub next_fact_id: String,
    pub derived_only: Vec<String>,
    pub admitted: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ExecutionRecord {
    pub schema_version: u32,
    pub engine_version: String,
    pub capabilities: Vec<String>,
    pub options: RecordingOptions,
    pub status: RecordingStatus,
    pub truncation_reason: Option<String>,
    /// Bytes of retained events, artifacts and snapshots in JSON; the envelope is excluded.
    pub recorded_bytes: usize,
    pub input: String,
    pub profile: EngineProfile,
    /// Source-only recovery is unavailable for unsupported native configuration.
    /// This does not change the query outcome or history completeness.
    pub snapshot_unavailable_reason: Option<String>,
    pub initial_snapshot: Option<SessionSnapshot>,
    pub final_snapshot: Option<SessionSnapshot>,
    pub artifacts: Vec<CompilationArtifact>,
    pub events: Vec<ExecutionEvent>,
    pub result: Option<QueryResult>,
    pub error: Option<String>,
}

/// The observer is deliberately independent of evaluator/proof implementations.
/// Calls must be non-reentrant and must never affect the operation's semantics.
pub trait ExecutionObserver: Send + Sync {
    /// Allows a bounded collector to stop payload construction while phase
    /// notifications continue. The default preserves custom observer behavior.
    fn recording_enabled(&self) -> bool {
        true
    }
    fn observe(&self, event: ExecutionEvent);
    fn phase(&self, phase: ExecutionPhase);
    fn compilation(&self, artifact: CompilationArtifact);
}

pub type ExecutionObserverHandle = Arc<dyn ExecutionObserver>;

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(tag = "kind", rename_all = "snake_case"))]
pub enum SessionChange {
    Assert { text: String },
    Withdraw { id: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ChangeResult {
    /// In operation order. An assertion has its minted root IDs; withdrawal
    /// has the withdrawn ID. Empty input produces no entries.
    pub operation_ids: Vec<Vec<String>>,
}
