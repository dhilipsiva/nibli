//! Native nibli engine library: calls nibli-kr/nibli-semantics/nibli-reason directly as Rust crates.
//! No WASM, no Wasmtime — full stack traces for debugging.

use std::cell::RefCell;
use std::path::Path;

use nibli_store::NibliStore;

pub use nibli_reason::ComputeRequest as EngineComputeRequest;
pub use nibli_reason::{ContradictionGap, ContradictionGapReason, ContradictionReport};
pub use nibli_types::logic::{
    AggregateOp as EngineAggregateOp, AggregateOutcome as EngineAggregateOutcome,
    AssertionRecordSummary as EngineAssertionRecordSummary,
    AssertionStatus as EngineAssertionStatus, EngineProfile, FactSummary as EngineFactSummary,
    LogicBuffer as EngineLogicBuffer, LogicNode as EngineLogicNode,
    LogicalTerm as EngineLogicalTerm, PROOF_ENVELOPE_SCHEMA, ProofEnvelope as EngineProofEnvelope,
    QueryResult as EngineQueryResult, ResourceKind as EngineResourceKind,
    UnknownReason as EngineUnknownReason, WitnessBinding as EngineWitnessBinding,
    WitnessOrigin as EngineWitnessOrigin, validate_envelope,
};

/// The pipeline's typed error (`Syntax`/`Semantic`/`Reasoning`/`Backend`),
/// re-exported so embedders, tests, and the server can pattern-match the error
/// CLASS instead of string-parsing the `[Xxx Error]` Display prefix.
pub use nibli_types::error::NibliError as EngineError;
use nibli_types::logic;

mod compute_client;

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE CONVERSION
// ═══════════════════════════════════════════════════════════════════════
//
// The canonical proof types ARE the wire types now (serde-derived in nibli-types),
// so there is no canonical->wire conversion; `nibli-protocol` only supplies JSON
// helpers. Readable rendering lives in `nibli-render`. Term display is an inherent
// method on the canonical `LogicalTerm` enum.

pub fn display_term(term: &EngineLogicalTerm) -> String {
    term.trace_display()
}

pub fn display_query_result(result: &EngineQueryResult) -> String {
    match result.detail_label() {
        Some(detail) => format!("{} ({})", result.status_label(), detail),
        None => result.status_label().to_string(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

pub struct NibliEngine {
    /// The shared compile/assert/query core (nibli-session) — the same
    /// CoreSession the pipeline/wasm/ui surfaces wrap, so native and WASM
    /// agree BY CONSTRUCTION.
    core: nibli_session::CoreSession,
    store: RefCell<Option<NibliStore>>,
}

/// Keeps storage commit classification intact until the live transaction guard
/// has been released, so an uncertain commit can close every shared KB handle.
enum MutationError {
    Engine(EngineError),
    Store(nibli_store::StoreError),
}

impl From<EngineError> for MutationError {
    fn from(error: EngineError) -> Self {
        Self::Engine(error)
    }
}

impl From<nibli_store::StoreError> for MutationError {
    fn from(error: nibli_store::StoreError) -> Self {
        Self::Store(error)
    }
}

impl Default for NibliEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl NibliEngine {
    /// Access the underlying KnowledgeBase for sort/constraint declarations.
    pub fn kb(&self) -> &nibli_reason::KnowledgeBase {
        self.core.kb()
    }

    /// Install a cooperative cancellation flag on the underlying reasoning core.
    /// When the flag is raised, an in-flight query aborts via the error channel
    /// (returned as a `String` error from the query methods). The native
    /// nibli-server watchdog uses this to free a blocking thread when a request's
    /// wall-clock budget elapses, instead of letting a pathological query run to
    /// completion. No clock is read inside the engine.
    pub fn set_cancel_flag(&self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.core.kb().set_cancel_flag(flag);
    }

    /// Remove any installed cancellation flag.
    pub fn clear_cancel_flag(&self) {
        self.core.kb().clear_cancel_flag();
    }

    /// Enable/disable the engine's informational stdout diagnostics
    /// (`[Rule]`/`[Skolem]`/`[Constraint] Registered`). Default OFF — nibli-engine
    /// is a silent library, so the server/validate/tavla do not spam stdout on a
    /// per-query corpus re-assertion. Interactive callers (the native `nibli`
    /// REPL) opt in. Configuration — survives `reset()`.
    pub fn set_verbose(&self, verbose: bool) {
        self.core.kb().set_verbose(verbose);
    }

    /// Enable/disable STRICT MODE (default off — permissive warn-and-insert):
    /// when on, an arity mismatch or integrity-constraint violation REJECTS the
    /// offending fact and fails the assertion. Like `set_verbose`, the library
    /// stays permissive by default; embedders opt in programmatically (the
    /// runtime surfaces read `NIBLI_STRICT=1` — nibli-host forwards it into the
    /// guest, where `nibli-pipeline::Session::new` applies it).
    pub fn set_strict(&self, strict: bool) {
        self.core.kb().set_strict(strict);
    }

    /// Configure bounded reasoning. Zero is invalid; the default is ten.
    pub fn set_max_chain_depth(&self, depth: u32) -> Result<(), EngineError> {
        self.core.set_max_chain_depth(depth)
    }

    /// The effective reasoning depth for queries and proof certificates.
    pub fn max_chain_depth(&self) -> u32 {
        self.core.max_chain_depth()
    }

    /// Enable/disable legacy EXISTENTIAL-IMPORT MODE (default OFF). ON makes a
    /// description universal mint logical witnesses that participate in every
    /// quantifier/find/count surface. The change transactionally rebuilds the KB.
    pub fn set_existential_import(&self, on: bool) -> Result<(), EngineError> {
        self.core.set_existential_import(on)
    }

    /// Whether legacy existential import is active for this whole engine.
    pub fn is_existential_import(&self) -> bool {
        self.core.is_existential_import()
    }

    /// Enable/disable STRATUM-ORDERED MATERIALISATION (default ON). When on, the
    /// relations a query reads under `~` are saturated bottom-up in stratum order and
    /// each NAF check becomes a set-membership test. OFF restores the pure
    /// backward-chaining path. The runtime surfaces read `NIBLI_MATERIALIZE=0`
    /// (nibli-host forwards it into the guest, where `nibli-pipeline::Session::new`
    /// applies it).
    pub fn set_materialization(&self, on: bool) {
        self.core.kb().set_materialization(on);
    }

    /// What the last query's saturation covered: `(completed, [(relation, why not)])`.
    /// The only way to see whether a slow `~p(x)` actually got the lookup.
    pub fn materialization_report(
        &self,
    ) -> Result<nibli_reason::MaterializationReport, EngineError> {
        self.core.kb().materialization_report()
    }

    /// Register this engine's external compute dispatch (per-instance). Without
    /// it, a registered external predicate such as `exponential` yields
    /// `UNKNOWN (backend-unavailable)`; built-in arithmetic
    /// (`product`/`sum`/`quotient`) works regardless. Replaces the old
    /// thread-local registration that the multithreaded server could not use.
    /// This is the native embedder's admission-policy boundary: an `Ok(bool)` is
    /// trusted for the current proof-local check, while an error becomes
    /// `UNKNOWN (backend-unavailable)`. The current proof schema does not retain
    /// backend identity, wire transcripts, freshness data, or policy receipts.
    /// See `nibli_reason::KnowledgeBase::set_compute_dispatch`.
    pub fn set_compute_dispatch(
        &self,
        eval: fn(&str, &[EngineLogicalTerm]) -> Result<bool, String>,
        batch_eval: fn(&[nibli_reason::ComputeRequest]) -> Vec<Result<bool, String>>,
    ) {
        self.core.kb().set_compute_dispatch(eval, batch_eval);
    }

    /// Enable external compute dispatch to a Python-style JSON-Lines backend at
    /// `addr` (e.g. `"127.0.0.1:5555"`). Wires the native TCP client as this
    /// engine's compute dispatch, so registered external predicates (for
    /// example `exponential`/`logarithm`) are evaluated by the backend; valid
    /// numeric built-in arithmetic (`product`/`sum`/`quotient`) is still
    /// resolved in-engine. Opt-in — engines that do not call this leave the
    /// dispatch hook unwired (`set_compute_dispatch` isolation preserved). The
    /// address is stored per-thread; in the
    /// multithreaded server each `spawn_blocking` worker connects lazily and
    /// reuses its connection. Register a corpus-resolvable text predicate
    /// separately via [`Self::register_compute_predicate`]. An arbitrary raw
    /// [`EngineLogicNode::ComputeNode`] query reaches this same dispatcher
    /// without text registration. Trust boundary: this stock client is
    /// deliberately plaintext and unauthenticated, with no identity, integrity,
    /// request binding, freshness/replay, revocation, version, or audit metadata.
    /// Use `set_compute_dispatch` (or a custom component host) when a deployment
    /// requires stronger admission; `addr` is routing, not authentication.
    pub fn enable_compute_backend(&self, addr: &str) {
        compute_client::set_addr(addr);
        self.core.kb().set_compute_dispatch(
            compute_client::native_eval_fn,
            compute_client::native_batch_eval_fn,
        );
    }

    /// Create an engine without persistence (existing behavior).
    pub fn new() -> Self {
        NibliEngine {
            core: nibli_session::CoreSession::new(),
            store: RefCell::new(None),
        }
    }

    /// Create an engine with disk persistence at the given path.
    /// Opens a `RedbFactStore` for typed fact persistence and replays
    /// the legacy `NibliStore` (LogicBuffer-level) for backward compatibility.
    pub fn open(db_path: &Path) -> Result<Self, String> {
        let mut store = NibliStore::open(db_path, "local".to_string())
            .map_err(|e| format!("Store error: {e}"))?;

        // Upgrade a legacy v2 registry to v3. Engine-written DBs hold bare
        // `LogicBuffer` payloads (never `StoredAssertion::Text`), so this is a
        // version restamp only — NOT `migrate_v2_text_rows` (decoding a bare
        // buffer as a `StoredAssertion` is a category error). Any genuinely
        // undecodable row still fails closed in `replay_from_store` below.
        if store.needs_migration() {
            store
                .finalize_v3()
                .map_err(|e| format!("Store error: {e}"))?;
        }

        // Open persistent typed fact store alongside the legacy store.
        let typed_db_path = db_path.with_extension("typed.redb");
        // The fact REGISTRY (the store opened above) is the durable source of
        // truth: retraction tombstones live there, and remote merges land
        // there. The typed store is only the KB's write-through mirror — a
        // store-level retraction never touches its rows. Discard it WITHOUT
        // decoding first: old hash-only/corrupt mirror rows are recoverable
        // because the canonical LogicBuffer registry below rebuilds the mirror.
        // Direct RedbFactStore::open callers retain the strict validation path.
        let typed_store = nibli_store::typed_store::RedbFactStore::open_for_rebuild(&typed_db_path)
            .map_err(|e| format!("TypedStore error: {e}"))?;

        let kb = nibli_reason::KnowledgeBase::with_store(Box::new(typed_store))
            .map_err(|e| format!("TypedStore compatibility error: {e}"))?;
        let engine = NibliEngine {
            core: nibli_session::CoreSession::with_kb(kb),
            store: RefCell::new(Some(store)),
        };
        engine.replay_from_store()?;
        Ok(engine)
    }

    /// Replay all persisted facts into the in-memory KB.
    fn replay_from_store(&self) -> Result<(), String> {
        let store = self.store.borrow();
        let Some(store) = store.as_ref() else {
            return Ok(()); // No store configured — nothing to replay.
        };
        let facts = store
            .all_fact_records()
            .map_err(|e| format!("Store error: {e}"))?;
        for fact in &facts {
            if fact.retracted {
                self.core
                    .restore_withdrawn_assertion(fact.id, fact.label.clone())
                    .map_err(|e| format!("Replay error (withdrawn fact {}): {e}", fact.id))?;
                continue;
            }
            let buf: logic::LogicBuffer = postcard::from_bytes(&fact.payload)
                .map_err(|e| format!("Deserialize error: {e}"))?;
            // Re-marks against the live registry (builtins only at open —
            // registrations are session state, not persisted), so a stored
            // plain row for a compute name fails closed instead of replaying
            // as an unreachable ordinary fact.
            self.core
                .assert_buffer_with_id(buf, fact.label.clone(), fact.id)
                .map_err(|e| format!("Replay error (fact {}): {e}", fact.id))?;
        }
        Ok(())
    }

    /// Validate KR text without asserting — returns Ok if it parses and compiles.
    /// This is intentionally compile-only: CountNode and ComputeNode are valid
    /// query IR even though `assert_text` will reject them as query-only (and
    /// the reference external compute names are rejected there registered or
    /// not). Compile-only does not mean vocabulary-free: unknown text names and
    /// wrong corpus arities still fail. Use `assert_text` for text assertion
    /// admission; raw-buffer callers can run
    /// `KnowledgeBase::validate_assertion` before `assert_fact`.
    pub fn validate(&self, text: &str) -> Result<(), String> {
        self.compile_text(text)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Route a committed-corpus predicate to external compute dispatch.
    ///
    /// This does not declare KR vocabulary or infer arity. Unknown names are
    /// rejected here and remain text compile errors. Surface aliases and
    /// committed compounds normalize to the canonical relation emitted in IR;
    /// the registry/backend use that canonical name. Arbitrary names require a
    /// caller-built raw [`EngineLogicNode::ComputeNode`] queried through
    /// [`Self::kb`], or a future explicit vocabulary/schema extension. Refused
    /// while live stored statements reference the canonical relation — see
    /// `CoreSession::register_compute_predicate`.
    pub fn register_compute_predicate(&mut self, name: String) -> Result<(), EngineError> {
        self.core.register_compute_predicate(name)
    }

    /// The session's canonical compiled compute-relation names, sorted (the
    /// built-in arithmetic names are pre-registered and included). Backs the
    /// bare `:compute` report.
    pub fn compute_predicates(&self) -> Vec<String> {
        let mut names: Vec<String> = self.core.compute_predicates().iter().cloned().collect();
        names.sort();
        names
    }

    fn compile_text(&self, input: &str) -> Result<logic::LogicBuffer, EngineError> {
        // The SOLE text→AST seam — every public text method funnels through
        // here, delegating to the SHARED chain (nibli-session), the same core
        // the WASM surfaces wrap; `EngineError` is the re-exported `NibliError`.
        self.core.compile_text(input)
    }

    fn compile_query_text(&self, input: &str) -> Result<logic::LogicBuffer, EngineError> {
        self.core.compile_query_text(input)
    }

    /// Stage against detached state, commit the canonical registry, then publish
    /// into the original shared KB identity. No compensating logical mutations
    /// are needed if validation or a pre-commit storage operation fails.
    fn apply_mutation<R>(
        &self,
        operation: impl FnOnce(
            &nibli_reason::KnowledgeBase,
            Option<&mut NibliStore>,
        ) -> Result<R, MutationError>,
    ) -> Result<R, EngineError> {
        let mut store = self.store.try_borrow_mut().map_err(|_| {
            EngineError::Reasoning("Store error: persistence state is already borrowed".to_string())
        })?;
        let mut uncertain_commit = None;
        let result = self.core.kb().transaction(|candidate| {
            operation(candidate, store.as_mut()).map_err(|error| match error {
                MutationError::Engine(error) => error,
                MutationError::Store(error) => {
                    if matches!(error, nibli_store::StoreError::CommitOutcomeUnknown(_)) {
                        uncertain_commit = Some(error.to_string());
                    }
                    EngineError::Reasoning(format!("Store error: {error}"))
                }
            })
        });
        if let Some(reason) = uncertain_commit {
            self.core.kb().require_recovery(reason);
        }
        result
    }

    /// Reset the knowledge base, clearing all facts and rules.
    pub fn reset(&self) -> Result<(), EngineError> {
        self.apply_mutation(|candidate, store| {
            candidate.reset()?;
            if let Some(store) = store {
                store.clear()?;
            }
            Ok(())
        })
    }

    /// Parse KR text, compile to FOL, and assert into the knowledge base.
    ///
    /// A multi-statement text becomes N independently retractable facts — one per root —
    /// each with its own id, store record, and retraction (connectives compile to a
    /// single root and stay one fact). Returns the minted ids in root order. A
    /// single-sentence text yields exactly one id. Exact-count and executable
    /// compute formulas in asserted position (outside opaque quoted content) are
    /// query-only. Validation and reasoning are atomic across every root in this
    /// call; a later refusal publishes no prefix, consumes no IDs, and adds no
    /// active or withdrawn durable records.
    pub fn assert_text(&self, text: &str) -> Result<Vec<u64>, EngineError> {
        let buf = self.compile_text(text)?;
        self.core.kb().validate_assertion(&buf)?;
        self.assert_buffers(buf.split_roots(), text.to_string())
    }

    fn assert_buffers(
        &self,
        buffers: Vec<logic::LogicBuffer>,
        label: String,
    ) -> Result<Vec<u64>, EngineError> {
        self.apply_mutation(|candidate, store| {
            let mut next_id = candidate.next_fact_id()?;
            if let Some(store) = store.as_ref() {
                next_id = next_id.max(store.next_fact_id()?);
            }
            let mut ids = Vec::with_capacity(buffers.len());
            let mut rows = Vec::with_capacity(buffers.len());
            for buffer in buffers {
                let id = next_id;
                next_id = next_id
                    .checked_add(1)
                    .ok_or_else(|| EngineError::Reasoning("fact ID space exhausted".to_string()))?;
                let payload = postcard::to_allocvec(&buffer)
                    .map_err(|e| EngineError::Reasoning(format!("Serialize error: {e}")))?;
                candidate
                    .assert_fact_with_id(buffer, label.clone(), id)
                    .map_err(EngineError::Reasoning)?;
                ids.push(id);
                rows.push((id, label.clone(), payload));
            }
            if let Some(store) = store {
                store.insert_facts(&rows)?;
            }
            Ok(ids)
        })
    }

    /// Assert a fact directly by relation name and arguments, bypassing text
    /// parsing. Uses the same staged atomic mutation as [`Self::assert_text`]
    /// when persistence is configured (label `":assert {relation}"`) and is
    /// event-decomposed to the surface shape.
    pub fn assert_fact_direct(
        &self,
        relation: String,
        args: Vec<EngineLogicalTerm>,
    ) -> Result<u64, EngineError> {
        let buffer = self.core.compile_injected_fact(&relation, &args)?;
        self.core.kb().validate_assertion(&buffer)?;
        Ok(self.assert_buffers(vec![buffer], format!(":assert {relation}"))?[0])
    }

    /// Certify a KR query: verdict + trace + session profile + lockstep
    /// engine version bound into one `ProofEnvelope` (re-exported as
    /// `EngineProofEnvelope`; `validate_envelope` is the KB-independent
    /// checker). Exposes `CoreSession::certify_text`.
    pub fn certify_text(
        &self,
        text: &str,
    ) -> Result<nibli_types::logic::ProofEnvelope, EngineError> {
        self.core.certify_text(text)
    }

    /// Parse KR query, run entailment check, return result + formatted proof + JSON proof.
    pub fn query_text_with_proof(
        &self,
        text: &str,
    ) -> Result<(EngineQueryResult, String, String), EngineError> {
        let (result, trace) = self.core.query_text_with_proof(text)?;
        // `trace` IS the wire `ProofTrace` (canonical == wire now) — no conversion.
        let formatted = nibli_render::render_proof_text(&trace, nibli_render::Register::Spec);
        let json = nibli_protocol::proof_trace_to_json(&trace);
        Ok((result, formatted, json))
    }

    /// Parse a KR query, run the entailment check, and return the typed
    /// result together with the raw wire [`nibli_protocol::ProofTrace`] — for
    /// callers/tests that need structured proof access (the plain-English "why"
    /// summary, the collapsed macro-DAG view) rather than the pre-formatted text.
    pub fn query_text_raw_proof(
        &self,
        text: &str,
    ) -> Result<(EngineQueryResult, nibli_protocol::ProofTrace), EngineError> {
        self.core.query_text_with_proof(text)
    }

    /// Evaluate a corpus-resolvable KR query against the KB and return the typed
    /// query result. Compute registration changes routing after compilation; it
    /// does not make an unknown text predicate compile.
    pub fn query_holds(&self, text: &str) -> Result<EngineQueryResult, EngineError> {
        self.core.query_text(text)
    }

    /// Parse a KR query and extract all satisfying witness bindings.
    /// Returns a reasoning error instead of partial rows when any evaluated
    /// candidate leaf is `Unknown(_)` or `ResourceExceeded(_)`.
    pub fn query_find_text(
        &self,
        text: &str,
    ) -> Result<Vec<Vec<EngineWitnessBinding>>, EngineError> {
        self.core.query_find_text(text)
    }

    /// Count the number of distinct witness binding sets satisfying a KR query.
    /// Exposes `nibli_reason::KnowledgeBase::count_witnesses` at the embedding level.
    /// Inherits the reasoner's complete-or-error collection contract.
    pub fn count_witnesses_text(&self, text: &str) -> Result<usize, EngineError> {
        self.core.count_witnesses_text(text)
    }

    /// Aggregate the numeric values bound to `variable` across all witness binding
    /// sets of a KR query, applying `op` (Sum/Min/Max/Avg) — FAIL CLOSED,
    /// propagated uncollapsed from `nibli_reason::KnowledgeBase::aggregate`:
    /// `AggregateOutcome::Empty` for a definitive zero-witness enumeration,
    /// `Value { value, witnesses }` (contributing-witness provenance) for an
    /// all-numeric finite aggregate, and an error for incomplete enumeration, a
    /// missing/nonnumeric binding, or a non-finite operand/result.
    pub fn aggregate_text(
        &self,
        text: &str,
        variable: &str,
        op: nibli_types::logic::AggregateOp,
    ) -> Result<nibli_types::logic::AggregateOutcome, EngineError> {
        self.core.aggregate_text(text, variable, op)
    }

    /// Compile corpus-resolvable KR text to the typed FOL `LogicBuffer` without
    /// asserting. This is compile-only, not an assertion-admission check; it
    /// still enforces fail-closed vocabulary and corpus arity.
    ///
    /// Returns the IR directly — the caller renders it (e.g. via
    /// `nibli_render::render_logic_tree` / `render_logic_buffer`). No
    /// S-expression string is produced.
    pub fn compile_debug(&self, text: &str) -> Result<EngineLogicBuffer, EngineError> {
        self.compile_text(text)
    }

    /// Query-intent alias for [`Self::compile_debug`]. Assertions and queries
    /// consume the same canonical typed FOL `LogicBuffer`, including
    /// connected-clause `$name` co-reference.
    pub fn compile_query_debug(&self, text: &str) -> Result<EngineLogicBuffer, EngineError> {
        self.compile_query_text(text)
    }

    /// List all active (non-retracted) facts with their IDs and labels.
    pub fn list_facts(&self) -> Result<Vec<EngineFactSummary>, EngineError> {
        self.core.kb().list_facts()
    }

    /// List every retained assertion record, including withdrawn premises.
    pub fn list_assertion_records(
        &self,
    ) -> Result<Vec<logic::AssertionRecordSummary>, EngineError> {
        self.core.list_assertion_records()
    }

    /// Retract a fact by ID and rebuild derived state.
    ///
    /// When persistence is configured, the retraction is also written through to
    /// the on-disk store as a tombstone, so a subsequent `open()` does NOT replay
    /// (resurrect) the retracted fact. Validation and rebuilding happen on a
    /// detached candidate, which is published only after the tombstone commits.
    pub fn retract_fact(&self, id: u64) -> Result<(), EngineError> {
        self.apply_mutation(|candidate, store| {
            candidate.retract_fact(id)?;
            if let Some(store) = store {
                // An assertion installed directly through kb() has no durable
                // row. This low-level use remains non-persistent by contract.
                match store.retract_fact(id) {
                    Ok(()) | Err(nibli_store::StoreError::NotFound(_)) => {}
                    Err(error) => return Err(error.into()),
                }
            }
            Ok(())
        })
    }

    /// Compatibility findings-only scan. Use [`Self::check_contradictions_report`]
    /// to distinguish a clean scan from checks that could not be decided.
    pub fn check_contradictions(&self) -> Vec<String> {
        self.core.kb().check_contradictions()
    }

    /// Scan represented constraints, reporting both contradictions and checks
    /// that could not be decided. This is not unrestricted FOL consistency.
    pub fn check_contradictions_report(&self) -> ContradictionReport {
        self.core.kb().check_contradictions_report()
    }

    /// Enable tracing for a predicate (interactive debugging).
    pub fn trace_predicate(&self, predicate: &str) {
        self.core.kb().trace_predicate(predicate);
    }

    /// Disable tracing for a predicate.
    pub fn untrace_predicate(&self, predicate: &str) {
        self.core.kb().untrace_predicate(predicate);
    }

    /// List all currently traced predicates.
    pub fn traced_predicates(&self) -> Vec<String> {
        self.core.kb().traced_predicates()
    }
}

#[cfg(test)]
mod tests {
    use super::{MutationError, NibliEngine};
    use std::fs;
    use std::path::{Path, PathBuf};

    fn temp_db_path(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("nibli_engine_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{name}.redb"))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    /// The persisted payload is now `nibli_types::logic::LogicBuffer` serialized
    /// directly via serde/postcard (the `StoredLogicBuffer` mirror was deleted).
    /// This pins that round-trip over every node + term variant — the property the
    /// replay path (`replay_from_store`) and the write path (`assert_text`) depend on.
    #[test]
    fn logic_buffer_serde_postcard_roundtrip_covers_all_variants() {
        use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

        let buf = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate((
                    "gerku".into(),
                    vec![
                        LogicalTerm::Constant("adam".into()),
                        LogicalTerm::Variable("x".into()),
                        LogicalTerm::Description("le-dog".into()),
                        LogicalTerm::Unspecified,
                    ],
                )),
                LogicNode::Predicate(("danlu".into(), vec![LogicalTerm::Constant("adam".into())])),
                LogicNode::AndNode((0, 1)),
                LogicNode::ExistsNode(("x".into(), 2)),
                LogicNode::PastNode(0),
                LogicNode::NotNode(1),
                LogicNode::ForAllNode(("y".into(), 5)),
                LogicNode::ComputeNode((
                    "product".into(),
                    vec![LogicalTerm::Number(3.0), LogicalTerm::Number(4.0)],
                )),
                LogicNode::CountNode(("z".into(), 2, 0)),
                LogicNode::OrNode((0, 1)),
                LogicNode::PresentNode(0),
                LogicNode::FutureNode(0),
                LogicNode::ObligatoryNode(0),
                LogicNode::PermittedNode(0),
            ],
            roots: vec![2, 3],
        };

        let bytes = postcard::to_allocvec(&buf).unwrap();
        let decoded: LogicBuffer = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(buf, decoded);
    }

    #[test]
    fn persistent_assert_does_not_mutate_kb_when_store_is_unavailable() {
        let path = temp_db_path("atomic_assert_store_busy");
        cleanup(&path);

        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        let _borrow = engine.store.borrow();

        let err = engine
            .assert_text("big(some dog).")
            .expect_err("Store borrow conflict should abort assertion");
        assert!(
            err.to_string().contains("Store error"),
            "Expected store error, got: {err}"
        );
        assert!(
            engine
                .query_holds("big(some dog).")
                .expect("Query should still run")
                .is_false(),
            "Failed persistent assertions must not leak into the live KB"
        );

        drop(_borrow);
        let store = engine.store.borrow();
        let facts = store
            .as_ref()
            .unwrap()
            .all_active_facts()
            .expect("Store should remain empty");
        assert!(
            facts.is_empty(),
            "Failed persistent assertions must not leak into the store"
        );

        drop(store);
        let id = engine.assert_text("person(Adam).").unwrap()[0];
        let borrow = engine.store.borrow();
        assert!(engine.retract_fact(id).is_err());
        assert!(engine.reset().is_err());
        assert!(engine.query_holds("person(Adam).").unwrap().is_true());
        drop(borrow);
        cleanup(&path);
    }

    #[test]
    fn rejected_multiroot_policy_batch_changes_neither_live_nor_durable_state() {
        let path = temp_db_path("atomic_policy_batch");
        cleanup(&path);
        {
            let engine = NibliEngine::open(&path).unwrap();
            for text in [
                "derived_only(\"person\"). person(Adam).",
                "admits(\"person\"). person(Adam). dog(Rex).",
            ] {
                assert!(engine.assert_text(text).is_err(), "{text}");
                assert!(engine.list_assertion_records().unwrap().is_empty());
                assert_eq!(engine.kb().next_fact_id().unwrap(), 0);
                assert_eq!(
                    engine
                        .store
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .total_fact_count()
                        .unwrap(),
                    0
                );
            }
            assert_eq!(
                engine.assert_text("person(Adam). dog(Rex).").unwrap(),
                vec![0, 1]
            );
        }
        let engine = NibliEngine::open(&path).unwrap();
        assert!(engine.query_holds("person(Adam).").unwrap().is_true());
        assert!(engine.query_holds("dog(Rex).").unwrap().is_true());
        cleanup(&path);
    }

    #[test]
    fn precommit_failure_discards_candidate_retraction_reset_and_policy_changes() {
        let engine = NibliEngine::new();
        let id = engine.assert_text("person(Adam).").unwrap()[0];
        for reset in [false, true] {
            let error = engine
                .apply_mutation::<()>(|candidate, _| {
                    if reset {
                        candidate.reset()?;
                    } else {
                        candidate.retract_fact(id)?;
                    }
                    Err(nibli_store::StoreError::Io("injected pre-commit failure".into()).into())
                })
                .unwrap_err();
            assert!(error.to_string().contains("injected"));
            assert!(engine.query_holds("person(Adam).").unwrap().is_true());
            assert_eq!(engine.list_facts().unwrap().len(), 1);
        }
    }

    #[test]
    fn uncertain_commit_closes_shared_handles_until_fresh_open() {
        let path = temp_db_path("uncertain_commit_reopen");
        cleanup(&path);
        {
            let engine = NibliEngine::open(&path).unwrap();
            let handle = engine.kb();
            let buffer = engine.compile_debug("person(Adam).").unwrap();
            let error = engine
                .apply_mutation::<()>(|candidate, store| {
                    candidate.assert_fact(buffer.clone(), "person(Adam).".into())?;
                    // Simulate the ambiguous failure's committed branch. The engine
                    // cannot tell this apart from a commit that did not land.
                    store.unwrap().insert_fact(
                        0,
                        "person(Adam).".into(),
                        postcard::to_allocvec(&buffer).unwrap(),
                    )?;
                    Err(MutationError::Store(
                        nibli_store::StoreError::CommitOutcomeUnknown(
                            "injected lost commit acknowledgement".into(),
                        ),
                    ))
                })
                .unwrap_err();
            assert!(error.to_string().contains("commit outcome unknown"));
            assert!(engine.query_holds("person(Adam).").is_err());
            assert!(engine.assert_text("dog(Rex).").is_err());
            assert!(engine.reset().is_err());
            assert!(handle.list_facts().is_err());
            assert!(handle.materialization_report().is_err());
            assert!(handle.stratification_report().is_err());
            assert!(handle.prepare_materialization_plan().is_err());
            assert!(handle.assert_fact(buffer, "bypass".into()).is_err());
        }
        let engine = NibliEngine::open(&path).unwrap();
        assert!(engine.query_holds("person(Adam).").unwrap().is_true());
        assert_eq!(engine.assert_text("dog(Rex).").unwrap(), vec![1]);
        cleanup(&path);
    }

    #[test]
    fn withdrawn_envelopes_restore_without_decoding_payload_or_reusing_ids() {
        let path = temp_db_path("withdrawn_payload_reopen");
        cleanup(&path);
        {
            let mut store = nibli_store::NibliStore::open(&path, "local".into()).unwrap();
            store
                .insert_fact(41, "obsolete withdrawn syntax".into(), vec![255, 255])
                .unwrap();
            store.retract_fact(41).unwrap();
        }
        {
            let engine = NibliEngine::open(&path).unwrap();
            assert!(engine.list_facts().unwrap().is_empty());
            let records = engine.list_assertion_records().unwrap();
            assert_eq!(records.len(), 1);
            assert_eq!(records[0].id, 41);
            assert_eq!(records[0].label, "obsolete withdrawn syntax");
            assert_eq!(
                records[0].status,
                nibli_types::logic::AssertionStatus::Withdrawn
            );
            assert_eq!(engine.assert_text("person(Adam).").unwrap(), vec![42]);
        }
        let engine = NibliEngine::open(&path).unwrap();
        assert_eq!(engine.list_assertion_records().unwrap().len(), 2);
        assert!(engine.query_holds("person(Adam).").unwrap().is_true());
        engine.reset().unwrap();
        assert!(engine.list_assertion_records().unwrap().is_empty());
        cleanup(&path);
    }
}
