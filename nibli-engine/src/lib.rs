//! Native nibli engine library: calls gerna/smuni/logji directly as Rust crates.
//! No WASM, no Wasmtime — full stack traces for debugging.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashSet;
use std::path::Path;

use nibli_store::NibliStore;

pub use logji::ComputeRequest as EngineComputeRequest;
pub use nibli_types::logic::{
    AggregateOp as EngineAggregateOp, FactSummary as EngineFactSummary,
    LogicBuffer as EngineLogicBuffer, LogicNode as EngineLogicNode,
    LogicalTerm as EngineLogicalTerm, QueryResult as EngineQueryResult,
    ResourceKind as EngineResourceKind, UnknownReason as EngineUnknownReason,
    WitnessBinding as EngineWitnessBinding,
};

use nibli_types::error::NibliError as PipelineError;
use nibli_types::logic as logji_logic;

mod compute_client;

fn format_error(e: &PipelineError) -> String {
    e.to_string()
}

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE CONVERSION
// ═══════════════════════════════════════════════════════════════════════
//
// The canonical -> wire conversion lives in `nibli_protocol::from_canonical*`
// (shared with nibli-wasm — formerly duplicated here); readable rendering lives
// in `nibli-render`.

pub fn display_term(term: &EngineLogicalTerm) -> String {
    nibli_protocol::from_canonical_term(term).trace_display()
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

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

pub struct NibliEngine {
    kb: logji::KnowledgeBase,
    compute_predicates: HashSet<String>,
    store: RefCell<Option<NibliStore>>,
}

impl Default for NibliEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl NibliEngine {
    /// Access the underlying KnowledgeBase for sort/constraint declarations.
    pub fn kb(&self) -> &logji::KnowledgeBase {
        &self.kb
    }

    /// Install a cooperative cancellation flag on the underlying reasoning core.
    /// When the flag is raised, an in-flight query aborts via the error channel
    /// (returned as a `String` error from the query methods). The native
    /// nibli-server watchdog uses this to free a blocking thread when a request's
    /// wall-clock budget elapses, instead of letting a pathological query run to
    /// completion. No clock is read inside the engine.
    pub fn set_cancel_flag(&self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.kb.set_cancel_flag(flag);
    }

    /// Remove any installed cancellation flag.
    pub fn clear_cancel_flag(&self) {
        self.kb.clear_cancel_flag();
    }

    /// Register this engine's external compute dispatch (per-instance). Without
    /// it, external predicates (e.g. `tenfa`/`dugri`) return an error; built-in
    /// arithmetic (pilji/sumji/dilcu) works regardless. Replaces the old
    /// thread-local registration that the multithreaded server could not use.
    /// See `logji::KnowledgeBase::set_compute_dispatch` for the trust boundary.
    pub fn set_compute_dispatch(
        &self,
        eval: fn(&str, &[EngineLogicalTerm]) -> Result<bool, String>,
        batch_eval: fn(&[logji::ComputeRequest]) -> Vec<Result<bool, String>>,
    ) {
        self.kb.set_compute_dispatch(eval, batch_eval);
    }

    /// Enable external compute dispatch to a Python-style JSON-Lines backend at
    /// `addr` (e.g. `"127.0.0.1:5555"`). Wires the native TCP client as this
    /// engine's compute dispatch, so registered external predicates (e.g.
    /// `tenfa`/`dugri`) are evaluated by the backend; built-in arithmetic
    /// (pilji/sumji/dilcu) is still resolved in-engine. Opt-in — engines that do
    /// not call this leave external compute unregistered (`set_compute_dispatch`
    /// isolation preserved). The address is stored per-thread; in the
    /// multithreaded server each `spawn_blocking` worker connects lazily and
    /// reuses its connection. Register the external predicate names separately
    /// via `register_compute_predicate`. Trust boundary: the backend is a
    /// plaintext, unauthenticated peer in the trusted computing base.
    pub fn enable_compute_backend(&self, addr: &str) {
        compute_client::set_addr(addr);
        self.kb.set_compute_dispatch(
            compute_client::native_eval_fn,
            compute_client::native_batch_eval_fn,
        );
    }

    fn default_compute_predicates() -> HashSet<String> {
        let mut preds = HashSet::new();
        preds.insert("pilji".to_string());
        preds.insert("sumji".to_string());
        preds.insert("dilcu".to_string());
        preds
    }

    /// Create an engine without persistence (existing behavior).
    pub fn new() -> Self {
        println!("Native engine ready");
        NibliEngine {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(None),
        }
    }

    /// Create an engine with disk persistence at the given path.
    /// Opens a `RedbFactStore` for typed fact persistence and replays
    /// the legacy `NibliStore` (LogicBuffer-level) for backward compatibility.
    pub fn open(db_path: &Path) -> Result<Self, String> {
        let store = NibliStore::open(db_path, "local".to_string())
            .map_err(|e| format!("Store error: {e}"))?;

        // Open persistent typed fact store alongside the legacy store.
        let typed_db_path = db_path.with_extension("typed.redb");
        let mut typed_store = nibli_store::typed_store::RedbFactStore::open(&typed_db_path)
            .map_err(|e| format!("TypedStore error: {e}"))?;

        // The fact REGISTRY (the store opened above) is the durable source of
        // truth: retraction tombstones live there, and remote merges land
        // there. The typed store is only the KB's write-through mirror — a
        // store-level retraction never touches its rows, so an eagerly loaded
        // mirror resurrects retracted facts (query-visible even though
        // list-facts is empty). Clear the mirror and let the registry replay
        // below rebuild it from the active records.
        {
            use logji::fact_store::FactStore as _;
            typed_store.clear();
        }

        let engine = NibliEngine {
            kb: logji::KnowledgeBase::with_store(Box::new(typed_store)),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(Some(store)),
        };
        engine.replay_from_store()?;
        println!("Native engine ready (persistent: {})", db_path.display());
        Ok(engine)
    }

    /// Replay all persisted facts into the in-memory KB.
    fn replay_from_store(&self) -> Result<(), String> {
        let store = self.store.borrow();
        let Some(store) = store.as_ref() else {
            return Ok(()); // No store configured — nothing to replay.
        };
        let facts = store
            .all_active_facts()
            .map_err(|e| format!("Store error: {e}"))?;
        for fact in &facts {
            let buf: logji_logic::LogicBuffer = postcard::from_bytes(&fact.payload)
                .map_err(|e| format!("Deserialize error: {e}"))?;
            self.kb
                .assert_fact_with_id(buf, fact.label.clone(), fact.id)
                .map_err(|e| format!("Replay error (fact {}): {e}", fact.id))?;
        }
        if !facts.is_empty() {
            println!("[Store] Replayed {} persisted facts", facts.len());
        }
        Ok(())
    }

    /// Validate Lojban text without asserting — returns Ok if it parses and compiles.
    pub fn validate(&self, text: &str) -> Result<(), String> {
        self.compile_text(text)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Register a predicate name for external compute dispatch.
    pub fn register_compute_predicate(&mut self, name: String) {
        self.compute_predicates.insert(name);
    }

    fn compile_text(&self, input: &str) -> Result<logji_logic::LogicBuffer, PipelineError> {
        let parse_result = gerna::parse_text_native(input.to_string())?;

        if parse_result.buffer.roots.is_empty() && !parse_result.errors.is_empty() {
            let first = &parse_result.errors[0];
            return Err(PipelineError::Syntax(nibli_types::error::SyntaxDetail {
                message: parse_result
                    .errors
                    .iter()
                    .map(|e| e.message.clone())
                    .collect::<Vec<_>>()
                    .join("; "),
                line: first.line,
                column: first.column,
            }));
        }

        if !parse_result.errors.is_empty() {
            let warnings: Vec<String> = parse_result
                .errors
                .iter()
                .map(|e| e.message.clone())
                .collect();
            return Err(PipelineError::Syntax(nibli_types::error::SyntaxDetail {
                message: format!(
                    "Assertion aborted: {} sentence(s) failed to parse: {}",
                    warnings.len(),
                    warnings.join("; ")
                ),
                line: 0,
                column: 0,
            }));
        }

        let mut buf = smuni::compile_from_gerna_ast(parse_result.buffer)?;
        logji::transform_compute_nodes(&mut buf, &self.compute_predicates);
        Ok(buf)
    }

    /// Reset the knowledge base, clearing all facts and rules.
    pub fn reset(&self) {
        self.kb.reset().ok();
        if let Ok(mut store) = self.store.try_borrow_mut()
            && let Some(s) = store.as_mut()
        {
            let _ = s.clear();
        }
    }

    /// Parse Lojban text, compile to FOL, and assert into the knowledge base.
    pub fn assert_text(&self, text: &str) -> Result<u64, String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        let label = text.to_string();
        let mut store = self
            .store
            .try_borrow_mut()
            .map_err(|_| "Store error: persistence state is already borrowed".to_string())?;

        if let Some(s) = store.as_mut() {
            let payload =
                postcard::to_allocvec(&buf).map_err(|e| format!("Serialize error: {e}"))?;
            let fact_id = s.next_fact_id().map_err(|e| format!("Store error: {e}"))?;
            s.insert_fact(fact_id, label.clone(), payload)
                .map_err(|e| format!("Store error: {e}"))?;
            self.kb
                .assert_fact_with_id(buf, label, fact_id)
                .map_err(|e| format_error(&PipelineError::Semantic(e)))?;
            Ok(fact_id)
        } else {
            self.kb.assert_fact(buf, label).map_err(|e| e.to_string())
        }
    }

    /// Assert a fact directly by relation name and arguments, bypassing Lojban parsing.
    pub fn assert_fact_direct(
        &self,
        relation: String,
        args: Vec<EngineLogicalTerm>,
    ) -> Result<u64, String> {
        let label = format!(":assert {}", relation);
        // Event-decompose to the SAME shape a surface assertion produces, so the
        // injected fact is matched by surface text queries (not just raw-FOL /
        // same-shape direct queries). `du` stays flat — see compile_injected_fact.
        let buf = smuni::compile_injected_fact(&relation, &args);
        self.kb.assert_fact(buf, label).map_err(|e| e.to_string())
    }

    /// Parse Lojban query, run entailment check, return result + formatted proof + JSON proof.
    pub fn query_text_with_proof(
        &self,
        text: &str,
    ) -> Result<(EngineQueryResult, String, String), String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        let (result, trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| e.to_string())?;
        let wire = nibli_protocol::from_canonical(&trace);
        let formatted = nibli_render::render_proof_text(&wire, nibli_render::Register::Spec);
        let json = wire.to_json();
        Ok((result, formatted, json))
    }

    /// Evaluate a Lojban query against the KB and return the typed query result.
    pub fn query_holds(&self, text: &str) -> Result<EngineQueryResult, String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        self.kb.query_entailment(buf).map_err(|e| e.to_string())
    }

    /// Parse Lojban query and extract all satisfying witness bindings.
    pub fn query_find_text(&self, text: &str) -> Result<Vec<Vec<EngineWitnessBinding>>, String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        self.kb.query_find(buf).map_err(|e| e.to_string())
    }

    /// Count the number of distinct witness binding sets satisfying a Lojban query.
    /// Exposes `logji::KnowledgeBase::count_witnesses` at the embedding level.
    pub fn count_witnesses_text(&self, text: &str) -> Result<usize, String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        self.kb.count_witnesses(buf).map_err(|e| e.to_string())
    }

    /// Aggregate the numeric values bound to `variable` across all witness binding
    /// sets of a Lojban query, applying `op` (Sum/Min/Max/Avg). Returns `Ok(None)`
    /// when no numeric witnesses are found. Exposes `logji::KnowledgeBase::aggregate`.
    pub fn aggregate_text(
        &self,
        text: &str,
        variable: &str,
        op: nibli_types::logic::AggregateOp,
    ) -> Result<Option<f64>, String> {
        let buf = self.compile_text(text).map_err(|e| e.to_string())?;
        self.kb
            .aggregate(buf, variable, op)
            .map_err(|e| e.to_string())
    }

    /// Compile Lojban text to the typed FOL `LogicBuffer` without asserting.
    ///
    /// Returns the IR directly — the caller renders it (e.g. via
    /// `nibli_render::render_logic_tree` / `render_logic_buffer`). No
    /// S-expression string is produced.
    pub fn compile_debug(&self, text: &str) -> Result<EngineLogicBuffer, String> {
        self.compile_text(text).map_err(|e| e.to_string())
    }

    /// List all active (non-retracted) facts with their IDs and labels.
    pub fn list_facts(&self) -> Result<Vec<EngineFactSummary>, String> {
        self.kb.list_facts().map_err(|e| e.to_string())
    }

    /// Retract a fact by ID and rebuild derived state.
    ///
    /// When persistence is configured, the retraction is also written through to
    /// the on-disk store as a tombstone, so a subsequent `open()` does NOT replay
    /// (resurrect) the retracted fact. The in-memory KB is retracted first (this
    /// validates the ID and rebuilds derived state); the durable tombstone is only
    /// written if that succeeds, keeping both layers consistent.
    pub fn retract_fact(&self, id: u64) -> Result<(), String> {
        self.kb.retract_fact(id).map_err(|e| e.to_string())?;

        let mut store = self
            .store
            .try_borrow_mut()
            .map_err(|_| "Store error: persistence state is already borrowed".to_string())?;
        if let Some(s) = store.as_mut() {
            // Idempotent at the store layer: retracting an already-tombstoned or
            // never-persisted-but-known fact is fine. A NotFound here means the id
            // lives only in the in-memory KB (e.g. assert_fact_direct, which bypasses
            // the store) — that is not a durability failure, so swallow it.
            match s.retract_fact(id) {
                Ok(()) => {}
                Err(nibli_store::StoreError::NotFound(_)) => {}
                Err(e) => return Err(format!("Store error: {e}")),
            }
        }
        Ok(())
    }

    /// Scan the KB for contradictions. Returns human-readable descriptions.
    pub fn check_contradictions(&self) -> Vec<String> {
        self.kb.check_contradictions()
    }

    /// Enable tracing for a predicate (interactive debugging).
    pub fn trace_predicate(&self, predicate: &str) {
        self.kb.trace_predicate(predicate);
    }

    /// Disable tracing for a predicate.
    pub fn untrace_predicate(&self, predicate: &str) {
        self.kb.untrace_predicate(predicate);
    }

    /// List all currently traced predicates.
    pub fn traced_predicates(&self) -> Vec<String> {
        self.kb.traced_predicates()
    }
}

#[cfg(test)]
mod tests {
    use super::NibliEngine;
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
                    "pilji".into(),
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
            .assert_text("lo gerku cu barda")
            .expect_err("Store borrow conflict should abort assertion");
        assert!(
            err.contains("Store error"),
            "Expected store error, got: {err}"
        );
        assert!(
            engine
                .query_holds("lo gerku cu barda")
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
        cleanup(&path);
    }
}
