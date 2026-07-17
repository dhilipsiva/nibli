//! The shared session core — the ONE compile/assert/query chain every runtime
//! surface wraps with only boundary conversion.
//!
//! Before this crate, the compile chain (`nibli_kr::parse_checked` →
//! `nibli_semantics::compile_from_ast` → `nibli_reason::transform_compute_nodes`)
//! plus the compute-predicate registry and the assert/query wrappers were
//! hand-mirrored across nibli-engine (native), nibli-pipeline (WASM component),
//! nibli-wasm (wasm-bindgen), nibli-ui (Dioxus), and nibli-verify's battery —
//! the pipeline's copy literally commented "the mirror of nibli-engine's
//! compile_text, so native and WASM agree". [`CoreSession`] is that agreement
//! BY CONSTRUCTION.
//!
//! What stays surface-side, deliberately:
//! - the ERROR BOUNDARY (this crate speaks canonical [`NibliError`]; the
//!   pipeline converts to its WIT twin, nibli-wasm flattens to `String`);
//! - verdict/proof SERIALIZATION (WIT records, JSON, rendered text);
//! - the LINT policy (`nibli_kr::lint` — stdout `[Note:]` echoes vs UI note
//!   data vs none) and env reads (`NIBLI_QUIET`/`NIBLI_STRICT` are wasip2/host
//!   concerns; the browser has no process env);
//! - STORE write-through (nibli-engine's durable registry mints its own ids
//!   and reaches the KB through [`CoreSession::kb`]);
//! - compute-dispatch WIRING (the pipeline bridges to its WIT host import,
//!   the engine offers an opt-in TCP client, the browser leaves external
//!   compute unregistered) — the [`CoreSession::set_compute_dispatch`]
//!   passthrough is the seam.
//!
//! nibli-formalize's gates intentionally do NOT use this crate: they stop
//! before compute-marking (the translator never needs `ComputeNode`s), keep
//! the AST for the render round-trip gate, and carry their own `GateError`
//! taxonomy (see nibli-formalize/src/gates.rs).

use std::collections::HashSet;

use nibli_types::error::NibliError;
use nibli_types::logic::{
    AggregateOp, FactSummary, LogicBuffer, LogicalTerm, ProofTrace, QueryResult, WitnessBinding,
};

/// Compile KR text WITHOUT compute-marking: parse + semantic compile only.
/// For consumers that deliberately stop before `transform_compute_nodes`
/// (display paths; nibli-formalize's gates mirror this shape independently).
pub fn compile_unmarked(text: &str) -> Result<LogicBuffer, NibliError> {
    let ast = nibli_kr::parse_checked(text)?;
    nibli_semantics::compile_from_ast(ast)
}

/// THE compile chain: parse + semantic compile + compute-marking against the
/// given predicate set. Free-fn form for per-call-set users (nibli-ui builds
/// its set fresh each query); [`CoreSession::compile_text`] is the
/// session-owned form.
pub fn compile_text(
    text: &str,
    compute_predicates: &HashSet<String>,
) -> Result<LogicBuffer, NibliError> {
    let mut buf = compile_unmarked(text)?;
    nibli_reason::transform_compute_nodes(&mut buf, compute_predicates);
    Ok(buf)
}

/// The shared session: a [`nibli_reason::KnowledgeBase`] + the compute-predicate
/// registry, with the compile/assert/query verbs every surface previously
/// hand-mirrored. No env reads, no linting, no persistence — those are
/// per-surface boundary policy (see the module doc).
pub struct CoreSession {
    kb: nibli_reason::KnowledgeBase,
    compute_predicates: HashSet<String>,
}

impl Default for CoreSession {
    fn default() -> Self {
        Self::new()
    }
}

impl CoreSession {
    /// A fresh in-memory session seeded with the built-in arithmetic compute
    /// predicates (`nibli_reason::default_compute_predicates`).
    pub fn new() -> Self {
        Self::with_kb(nibli_reason::KnowledgeBase::new())
    }

    /// Wrap an already-constructed KB (e.g. one built with a persistent
    /// write-through fact store via `KnowledgeBase::with_store`).
    pub fn with_kb(kb: nibli_reason::KnowledgeBase) -> Self {
        CoreSession {
            kb,
            compute_predicates: nibli_reason::default_compute_predicates(),
        }
    }

    /// The underlying KB, for surface-specific extras (cancel flags, predicate
    /// tracing, contradiction scans, store replay via `assert_fact_with_id`).
    pub fn kb(&self) -> &nibli_reason::KnowledgeBase {
        &self.kb
    }

    /// The current compute-predicate set (the marking input).
    pub fn compute_predicates(&self) -> &HashSet<String> {
        &self.compute_predicates
    }

    /// Register a predicate name for external compute dispatch.
    pub fn register_compute_predicate(&mut self, name: String) {
        self.compute_predicates.insert(name);
    }

    /// Register this session's external compute dispatch (per-instance; see
    /// `nibli_reason::KnowledgeBase::set_compute_dispatch` for the trust
    /// boundary). Without it, external predicates error; built-in arithmetic
    /// still resolves in-engine.
    pub fn set_compute_dispatch(
        &self,
        eval: fn(&str, &[LogicalTerm]) -> Result<bool, String>,
        batch_eval: fn(&[nibli_reason::ComputeRequest]) -> Vec<Result<bool, String>>,
    ) {
        self.kb.set_compute_dispatch(eval, batch_eval);
    }

    /// Engine stdout diagnostics (`[Rule]`/`[Skolem]`/`[Constraint]`).
    /// Default OFF — a silent library; surfaces opt in.
    pub fn set_verbose(&self, verbose: bool) {
        self.kb.set_verbose(verbose);
    }

    /// STRICT MODE (default off — permissive warn-and-insert).
    pub fn set_strict(&self, strict: bool) {
        self.kb.set_strict(strict);
    }

    /// THE compile chain against this session's compute-predicate set.
    pub fn compile_text(&self, text: &str) -> Result<LogicBuffer, NibliError> {
        compile_text(text, &self.compute_predicates)
    }

    /// Compile KR text and assert it, splitting a multi-statement input into
    /// one INDEPENDENT fact per root (`split_roots` — connectives compile to a
    /// single root and stay one compound fact). The full input text is each
    /// root's label. Returns one `(id, compiled-sub-buffer)` pair per root so
    /// a persisting caller can store the FACT itself and replay it
    /// recompile-free; callers that only need ids map the pairs down.
    pub fn assert_text(&self, text: &str) -> Result<Vec<(u64, LogicBuffer)>, NibliError> {
        let buf = self.compile_text(text)?;
        let mut out = Vec::new();
        for sub in buf.split_roots() {
            let id = self.kb.assert_fact(sub.clone(), text.to_string())?;
            out.push((id, sub));
        }
        Ok(out)
    }

    /// Assert a fact directly by relation name and arguments, bypassing text
    /// parsing, under an optional caller-chosen id (store replay). The label
    /// is `":assert {relation}"`. Event-decomposes to the SAME shape a surface
    /// assertion produces, so the injected fact is matched by surface text
    /// queries (not just raw-FOL / same-shape direct queries). Identity stays
    /// flat; arity follows the injected-arity policy (fail-closed) — see
    /// `nibli_semantics::compile_injected_fact`.
    pub fn assert_fact_direct(
        &self,
        relation: &str,
        args: &[LogicalTerm],
        id: Option<u64>,
    ) -> Result<u64, NibliError> {
        let label = format!(":assert {}", relation);
        let buf = nibli_semantics::compile_injected_fact(relation, args)?;
        match id {
            Some(i) => {
                // The assert is the reasoning stage (buffer already past
                // nibli-semantics); nibli-reason's `assert_fact_with_id`
                // returns a String, so wrap as Reasoning.
                self.kb
                    .assert_fact_with_id(buf, label, i)
                    .map_err(NibliError::Reasoning)?;
                Ok(i)
            }
            None => self.kb.assert_fact(buf, label),
        }
    }

    /// Compile a KR query and run the entailment check.
    pub fn query_text(&self, text: &str) -> Result<QueryResult, NibliError> {
        let buf = self.compile_text(text)?;
        self.kb.query_entailment(buf)
    }

    /// Compile a KR query, run the entailment check, and return the typed
    /// result with the canonical wire [`ProofTrace`].
    pub fn query_text_with_proof(
        &self,
        text: &str,
    ) -> Result<(QueryResult, ProofTrace), NibliError> {
        let buf = self.compile_text(text)?;
        self.kb.query_entailment_with_proof(buf)
    }

    /// Compile a KR query and extract all satisfying witness binding sets.
    pub fn query_find_text(&self, text: &str) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        let buf = self.compile_text(text)?;
        self.kb.query_find(buf)
    }

    /// Count the distinct witness binding sets satisfying a KR query.
    pub fn count_witnesses_text(&self, text: &str) -> Result<usize, NibliError> {
        let buf = self.compile_text(text)?;
        self.kb.count_witnesses(buf)
    }

    /// Aggregate the numeric values bound to `variable` across all witness
    /// binding sets of a KR query. `Ok(None)` when no numeric witnesses exist.
    pub fn aggregate_text(
        &self,
        text: &str,
        variable: &str,
        op: AggregateOp,
    ) -> Result<Option<f64>, NibliError> {
        let buf = self.compile_text(text)?;
        self.kb.aggregate(buf, variable, op)
    }

    /// Retract a fact by id and rebuild derived state (KB only — durable
    /// tombstones are the persisting surface's concern).
    pub fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.kb.retract_fact(id)
    }

    /// Reset the KB, clearing all facts and rules.
    pub fn reset(&self) -> Result<(), NibliError> {
        self.kb.reset()
    }

    /// List all active (non-retracted) facts with their ids and labels.
    pub fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.kb.list_facts()
    }
}
