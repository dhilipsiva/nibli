//! nibli-pipeline (fasten/orchestrator) WASM component: chains nibli-kr → nibli-semantics → nibli-reason.
//!
//! Single WASM component that calls nibli-kr/nibli-semantics/nibli-reason as internal Rust crate
//! dependencies. Provides a high-level [`Session`] resource via the `nibli-pipeline` WIT
//! export interface.

#[allow(warnings)]
mod bindings;

// The component's own WIT export types (the boundary we serialize through)
use bindings::exports::nibli::engine::engine::{Guest, GuestSession};
use bindings::nibli::engine::compute_backend as cb;
use bindings::nibli::engine::error_types as export_err;
use bindings::nibli::engine::logic_types as export_logic;

// Canonical pipeline types (shared across nibli-kr/nibli-semantics/nibli-reason)
use nibli_types::error as pipeline_err;
use nibli_types::logic;

use std::cell::RefCell;

/// WIT component implementation for the `nibli-pipeline` interface.
struct NibliPipeline;

/// A user-facing session wrapping the full nibli-kr → nibli-semantics → nibli-reason pipeline.
pub struct Session {
    /// The SHARED compile/assert/query core (nibli-session) — the same
    /// CoreSession nibli-engine wraps natively, so native and WASM agree BY
    /// CONSTRUCTION. RefCell only for `register_compute_predicate` (the WIT
    /// resource methods take `&self`; the KB inside has its own interior
    /// mutability).
    core: RefCell<nibli_session::CoreSession>,
    /// The KR lint session (NIBLI_KR §12 L1–L9): non-blocking
    /// `[Note: …]` guest-stdout echoes on interactive text inputs — the
    /// `[Skolem]`/`[Rule]` precedent, gated by the same NIBLI_QUIET verbose
    /// flag and reset with the KB. Stateful (L1/L4/L7 are per-session).
    linter: RefCell<nibli_kr::lint::Linter>,
    /// The NIBLI_QUIET-derived verbose flag, kept for the lint echoes (the
    /// kb's copy is not readable back).
    verbose: bool,
}

// ─── Type conversion: nibli-reason → nibli-pipeline export boundary ───

fn convert_logical_term_to_export(t: &logic::LogicalTerm) -> export_logic::LogicalTerm {
    match t {
        logic::LogicalTerm::Variable(v) => export_logic::LogicalTerm::Variable(v.clone()),
        logic::LogicalTerm::Constant(c) => export_logic::LogicalTerm::Constant(c.clone()),
        logic::LogicalTerm::Description(d) => export_logic::LogicalTerm::Description(d.clone()),
        logic::LogicalTerm::Number(n) => export_logic::LogicalTerm::Number(*n),
        logic::LogicalTerm::Unspecified => export_logic::LogicalTerm::Unspecified,
    }
}

/// Convert one nibli-reason `LogicNode` to the WIT export node (pure 1:1 — the WIT
/// `logic-node` variant mirrors `nibli_types::logic::LogicNode` exactly).
fn convert_logic_node_to_export(n: &logic::LogicNode) -> export_logic::LogicNode {
    use export_logic::LogicNode as E;
    use logic::LogicNode as L;
    match n {
        L::Predicate((rel, args)) => E::Predicate((
            rel.clone(),
            args.iter().map(convert_logical_term_to_export).collect(),
        )),
        L::ComputeNode((rel, args)) => E::ComputeNode((
            rel.clone(),
            args.iter().map(convert_logical_term_to_export).collect(),
        )),
        L::AndNode((l, r)) => E::AndNode((*l, *r)),
        L::OrNode((l, r)) => E::OrNode((*l, *r)),
        L::NotNode(i) => E::NotNode(*i),
        L::ExistsNode((v, b)) => E::ExistsNode((v.clone(), *b)),
        L::ForAllNode((v, b)) => E::ForAllNode((v.clone(), *b)),
        L::PastNode(i) => E::PastNode(*i),
        L::PresentNode(i) => E::PresentNode(*i),
        L::FutureNode(i) => E::FutureNode(*i),
        L::ObligatoryNode(i) => E::ObligatoryNode(*i),
        L::PermittedNode(i) => E::PermittedNode(*i),
        L::CountNode((v, c, b)) => E::CountNode((v.clone(), *c, *b)),
    }
}

/// Convert the full nibli-reason `LogicBuffer` to the WIT export buffer (typed IR
/// crosses the boundary; the host renders it — no S-expression string).
fn convert_logic_buffer_to_export(buf: &logic::LogicBuffer) -> export_logic::LogicBuffer {
    export_logic::LogicBuffer {
        nodes: buf.nodes.iter().map(convert_logic_node_to_export).collect(),
        roots: buf.roots.clone(),
    }
}

fn convert_logical_term_from_export(t: &export_logic::LogicalTerm) -> logic::LogicalTerm {
    match t {
        export_logic::LogicalTerm::Variable(v) => logic::LogicalTerm::Variable(v.clone()),
        export_logic::LogicalTerm::Constant(c) => logic::LogicalTerm::Constant(c.clone()),
        export_logic::LogicalTerm::Description(d) => logic::LogicalTerm::Description(d.clone()),
        export_logic::LogicalTerm::Number(n) => logic::LogicalTerm::Number(*n),
        export_logic::LogicalTerm::Unspecified => logic::LogicalTerm::Unspecified,
    }
}

/// Convert one WIT import node back to the nibli-reason `LogicNode` (pure 1:1 inverse
/// of `convert_logic_node_to_export`; `CountNode`'s middle field is a COUNT,
/// not a node index — copied verbatim, never remapped).
fn convert_logic_node_from_export(n: &export_logic::LogicNode) -> logic::LogicNode {
    use export_logic::LogicNode as E;
    use logic::LogicNode as L;
    match n {
        E::Predicate((rel, args)) => L::Predicate((
            rel.clone(),
            args.iter().map(convert_logical_term_from_export).collect(),
        )),
        E::ComputeNode((rel, args)) => L::ComputeNode((
            rel.clone(),
            args.iter().map(convert_logical_term_from_export).collect(),
        )),
        E::AndNode((l, r)) => L::AndNode((*l, *r)),
        E::OrNode((l, r)) => L::OrNode((*l, *r)),
        E::NotNode(i) => L::NotNode(*i),
        E::ExistsNode((v, b)) => L::ExistsNode((v.clone(), *b)),
        E::ForAllNode((v, b)) => L::ForAllNode((v.clone(), *b)),
        E::PastNode(i) => L::PastNode(*i),
        E::PresentNode(i) => L::PresentNode(*i),
        E::FutureNode(i) => L::FutureNode(*i),
        E::ObligatoryNode(i) => L::ObligatoryNode(*i),
        E::PermittedNode(i) => L::PermittedNode(*i),
        E::CountNode((v, c, b)) => L::CountNode((v.clone(), *c, *b)),
    }
}

/// Convert a WIT import buffer back to the nibli-reason `LogicBuffer` (inverse of
/// `convert_logic_buffer_to_export`) — the `assert-buffer-with-id` replay path.
fn convert_logic_buffer_from_export(buf: &export_logic::LogicBuffer) -> logic::LogicBuffer {
    logic::LogicBuffer {
        nodes: buf
            .nodes
            .iter()
            .map(convert_logic_node_from_export)
            .collect(),
        roots: buf.roots.clone(),
    }
}

fn convert_query_result_to_export(result: &logic::QueryResult) -> export_logic::QueryResult {
    match result {
        logic::QueryResult::True => export_logic::QueryResult::True,
        logic::QueryResult::False => export_logic::QueryResult::False,
        logic::QueryResult::Unknown(logic::UnknownReason::CycleCut) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::CycleCut)
        }
        logic::QueryResult::Unknown(logic::UnknownReason::IncompleteKnowledge) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::IncompleteKnowledge)
        }
        logic::QueryResult::Unknown(logic::UnknownReason::NafDependent) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::NafDependent)
        }
        logic::QueryResult::Unknown(logic::UnknownReason::BackendUnavailable) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::BackendUnavailable)
        }
        logic::QueryResult::Unknown(logic::UnknownReason::NonFinite) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::NonFinite)
        }
        logic::QueryResult::ResourceExceeded(logic::ResourceKind::Depth) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Depth)
        }
        logic::QueryResult::ResourceExceeded(logic::ResourceKind::Fuel) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Fuel)
        }
        logic::QueryResult::ResourceExceeded(logic::ResourceKind::Memory) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Memory)
        }
    }
}

// nibli-reason's `ProofRule` is now the named-field canonical type; the WIT export type
// stays tuple-shaped (generated from world.wit), so this maps named fields → tuples.
fn convert_proof_rule(r: &logic::ProofRule) -> export_logic::ProofRule {
    match r {
        logic::ProofRule::Conjunction => export_logic::ProofRule::Conjunction,
        logic::ProofRule::DisjunctionCheck { detail } => {
            export_logic::ProofRule::DisjunctionCheck(detail.clone())
        }
        logic::ProofRule::DisjunctionIntro { side } => {
            export_logic::ProofRule::DisjunctionIntro(side.clone())
        }
        logic::ProofRule::Negation => export_logic::ProofRule::Negation,
        logic::ProofRule::ModalPassthrough { kind } => {
            export_logic::ProofRule::ModalPassthrough(kind.clone())
        }
        logic::ProofRule::ExistsWitness { var, term } => export_logic::ProofRule::ExistsWitness((
            var.clone(),
            convert_logical_term_to_export(term),
        )),
        logic::ProofRule::ExistsFailed => export_logic::ProofRule::ExistsFailed,
        logic::ProofRule::ForallVacuous => export_logic::ProofRule::ForallVacuous,
        logic::ProofRule::ForallVerified { entities } => export_logic::ProofRule::ForallVerified(
            entities
                .iter()
                .map(convert_logical_term_to_export)
                .collect(),
        ),
        logic::ProofRule::ForallCounterexample { entity } => {
            export_logic::ProofRule::ForallCounterexample(convert_logical_term_to_export(entity))
        }
        logic::ProofRule::CountResult { expected, actual } => {
            export_logic::ProofRule::CountResult((*expected, *actual))
        }
        logic::ProofRule::PredicateCheck { method, detail } => {
            export_logic::ProofRule::PredicateCheck((method.clone(), detail.clone()))
        }
        logic::ProofRule::ComputeCheck { method, detail } => {
            export_logic::ProofRule::ComputeCheck((method.clone(), detail.clone()))
        }
        logic::ProofRule::Asserted { fact } => export_logic::ProofRule::Asserted(fact.clone()),
        logic::ProofRule::Derived { label, fact } => {
            export_logic::ProofRule::Derived((label.clone(), fact.clone()))
        }
        logic::ProofRule::ProofRef { fact } => export_logic::ProofRule::ProofRef(fact.clone()),
        logic::ProofRule::EqualitySubstitution {
            original,
            equality_facts,
            substituted,
        } => export_logic::ProofRule::EqualitySubstitution((
            original.clone(),
            equality_facts.clone(),
            substituted.clone(),
        )),
        logic::ProofRule::RuleAttemptFailed {
            rule_label,
            failed_condition,
        } => export_logic::ProofRule::RuleAttemptFailed((
            rule_label.clone(),
            failed_condition.clone(),
        )),
        logic::ProofRule::PredicateNotFound { predicate } => {
            export_logic::ProofRule::PredicateNotFound(predicate.clone())
        }
    }
}

fn convert_proof_trace(t: logic::ProofTrace) -> export_logic::ProofTrace {
    export_logic::ProofTrace {
        steps: t
            .steps
            .iter()
            .map(|s| export_logic::ProofStep {
                rule: convert_proof_rule(&s.rule),
                holds: s.holds,
                children: s.children.clone(),
            })
            .collect(),
        root: t.root,
        // Compute the closed-world / NAF note once, here in the guest, so the
        // host need not recompute it from the steps (single source of truth:
        // nibli-reason's ProofTrace::has_naf_dependency).
        naf_dependent: t.has_naf_dependency(),
        // The dual CWA-FALSE flag needs the verdict (not recomputable from steps),
        // so it is read from the field nibli-reason already populated.
        cwa_false: t.cwa_false,
    }
}

fn convert_witness_bindings(
    wbs: Vec<Vec<logic::WitnessBinding>>,
) -> Vec<Vec<export_logic::WitnessBinding>> {
    wbs.into_iter()
        .map(|bindings| {
            bindings
                .into_iter()
                .map(|wb| export_logic::WitnessBinding {
                    variable: wb.variable,
                    term: convert_logical_term_to_export(&wb.term),
                })
                .collect()
        })
        .collect()
}

fn convert_fact_summaries(fs: Vec<logic::FactSummary>) -> Vec<export_logic::FactSummary> {
    fs.into_iter()
        .map(|f| export_logic::FactSummary {
            id: f.id,
            label: f.label,
            root_count: f.root_count,
        })
        .collect()
}

/// Convert pipeline error → WIT export error (for the WASM component boundary).
fn convert_pipeline_error(e: pipeline_err::NibliError) -> export_err::NibliError {
    match e {
        pipeline_err::NibliError::Syntax(d) => {
            export_err::NibliError::Syntax(export_err::SyntaxDetail {
                message: d.message,
                line: d.line,
                column: d.column,
            })
        }
        pipeline_err::NibliError::Semantic(m) => export_err::NibliError::Semantic(m),
        pipeline_err::NibliError::Reasoning(m) => export_err::NibliError::Reasoning(m),
        pipeline_err::NibliError::Backend((k, m)) => export_err::NibliError::Backend((k, m)),
    }
}

// ─── Compute dispatch bridge (nibli-reason → nibli-pipeline WIT import) ───

fn eval_via_host(rel: &str, args: &[logic::LogicalTerm]) -> Result<bool, String> {
    let converted: Vec<export_logic::LogicalTerm> =
        args.iter().map(convert_logical_term_to_export).collect();
    cb::evaluate(rel, &converted).map_err(|e| match e {
        export_err::NibliError::Backend((_, m)) => m,
        other => format!("{:?}", other),
    })
}

fn batch_eval_via_host(requests: &[nibli_reason::ComputeRequest]) -> Vec<Result<bool, String>> {
    let wit_requests: Vec<cb::ComputeRequest> = requests
        .iter()
        .map(|r| cb::ComputeRequest {
            relation: r.relation.clone(),
            args: r.args.iter().map(convert_logical_term_to_export).collect(),
        })
        .collect();
    let results = cb::evaluate_batch(&wit_requests);
    results
        .into_iter()
        .map(|r| match r {
            cb::ComputeResult::Ok(b) => Ok(b),
            cb::ComputeResult::Err(msg) => Err(msg),
        })
        .collect()
}

// ─── WIT exports ───
// (The compile chain lives in nibli-session's CoreSession — the SAME core
// nibli-engine wraps natively, so native and WASM agree by construction; the
// old `compile_pipeline` mirror is gone.)

impl Guest for NibliPipeline {
    type Session = Session;
}

impl Session {
    /// LEGACY REPLAY body for `assert_text_with_id`: recompiles `input` and
    /// asserts the WHOLE buffer (multi-root stays composite) under the
    /// CALLER-CHOSEN id — exactly the pre-split single-fact granularity, kept
    /// so durable stores written before buffer persistence (text-payload rows)
    /// replay unchanged. New code persists the per-root buffers `assert_text`
    /// returns and replays via `assert_buffer_with_id`. (`compile_pipeline`
    /// fails closed on any parse error, so no per-caller warning check is
    /// needed.)
    fn assert_text_inner(&self, input: String, id: u64) -> Result<(), export_err::NibliError> {
        let core = self.core.borrow();
        let buf = core.compile_text(&input).map_err(convert_pipeline_error)?;
        core.kb()
            .assert_fact_with_id(buf, input, id)
            // The assert is the reasoning stage (buffer already past nibli-semantics);
            // nibli-reason's `assert_fact_with_id` returns a String, so wrap as Reasoning.
            .map_err(export_err::NibliError::Reasoning)?;
        Ok(())
    }

    /// Emit the KR lint notes for an interactive text input (NIBLI_KR
    /// §12 L1–L9) to guest stdout as `[Note: …]` lines — the `[Skolem]`/`[Rule]`
    /// echo precedent: verbose-gated (NIBLI_QUIET suppresses), non-blocking
    /// (never affects the compile result). The legacy replay path
    /// (`assert_text_with_id`) deliberately does NOT lint — replay is
    /// mechanical, not authoring.
    fn emit_lints(&self, input: &str) {
        if !self.verbose {
            return;
        }
        for note in self.linter.borrow_mut().lint(input) {
            println!("[Note: {}]", note.message);
        }
    }

    /// Shared body for `assert_fact` / `assert_fact_with_id` — delegates to
    /// the core's `assert_fact_direct` (label `":assert {relation}"`,
    /// event-decomposed to the surface shape, caller-chosen id for replay);
    /// only the WIT term/error conversion happens here.
    fn assert_fact_inner(
        &self,
        relation: String,
        args: Vec<export_logic::LogicalTerm>,
        id: Option<u64>,
    ) -> Result<u64, export_err::NibliError> {
        let logic_args: Vec<logic::LogicalTerm> =
            args.iter().map(convert_logical_term_from_export).collect();
        self.core
            .borrow()
            .assert_fact_direct(&relation, &logic_args, id)
            .map_err(convert_pipeline_error)
    }
}

impl GuestSession for Session {
    fn new() -> Self {
        // Register compute dispatch PER-KB so nibli-reason can call the host's
        // compute-backend (was a thread-local global — now per-instance).
        let core = nibli_session::CoreSession::new();
        core.set_compute_dispatch(eval_via_host, batch_eval_via_host);
        // The nibli-host REPL opts the guest INTO verbose stdout — the per-assertion
        // `[Skolem]`/`[Rule]`/`[Constraint]` diagnostics — unlike the native
        // nibli-engine library, which stays quiet by default. The host forwards
        // `NIBLI_QUIET=1` into the WASI environment to suppress that bookkeeping
        // (the book's default capture mode); any other value stays verbose. A
        // post-trap rebuild re-runs this constructor, so the setting survives replay.
        // (The env reads live HERE, not in the shared core — the browser
        // surfaces have no process env.)
        let verbose = std::env::var("NIBLI_QUIET").ok().as_deref() != Some("1");
        core.set_verbose(verbose);
        // Same pattern for STRICT MODE: the host forwards `NIBLI_STRICT=1` into
        // the WASI env; the `:strict` REPL toggle re-applies via `set-strict`
        // after any post-trap rebuild.
        if std::env::var("NIBLI_STRICT").ok().as_deref() == Some("1") {
            core.set_strict(true);
        }
        Session {
            core: RefCell::new(core),
            linter: RefCell::new(nibli_kr::lint::Linter::new()),
            verbose,
        }
    }

    fn set_strict(&self, strict: bool) {
        self.core.borrow().set_strict(strict);
    }

    /// Assert KR text, splitting a multi-statement input into one independent
    /// fact per root (`split_roots` — connectives compile to a single root and
    /// stay one compound fact, matching the native surfaces). Returns one
    /// (id, buffer) pair per asserted root so a persisting host can store the
    /// compiled FACT itself and replay it recompile-free via
    /// `assert-buffer-with-id`.
    fn assert_text(
        &self,
        input: String,
    ) -> Result<Vec<(u64, export_logic::LogicBuffer)>, export_err::NibliError> {
        self.emit_lints(&input);
        let pairs = self
            .core
            .borrow()
            .assert_text(&input)
            .map_err(convert_pipeline_error)?;
        Ok(pairs
            .into_iter()
            .map(|(id, sub)| (id, convert_logic_buffer_to_export(&sub)))
            .collect())
    }

    fn assert_text_with_id(&self, input: String, id: u64) -> Result<(), export_err::NibliError> {
        self.assert_text_inner(input, id)
    }

    /// Recompile-free replay: assert an already-compiled buffer (as returned
    /// by `assert-text`) under a caller-chosen id.
    fn assert_buffer_with_id(
        &self,
        buffer: export_logic::LogicBuffer,
        label: String,
        id: u64,
    ) -> Result<(), export_err::NibliError> {
        let buf = convert_logic_buffer_from_export(&buffer);
        self.core
            .borrow()
            .kb()
            .assert_fact_with_id(buf, label, id)
            .map_err(export_err::NibliError::Reasoning)
    }

    fn query_text(
        &self,
        input: String,
    ) -> Result<export_logic::QueryResult, export_err::NibliError> {
        self.emit_lints(&input);
        self.core
            .borrow()
            .query_text(&input)
            .map(|result| convert_query_result_to_export(&result))
            .map_err(convert_pipeline_error)
    }

    fn query_find_text(
        &self,
        input: String,
    ) -> Result<Vec<Vec<export_logic::WitnessBinding>>, export_err::NibliError> {
        self.emit_lints(&input);
        let result = self
            .core
            .borrow()
            .query_find_text(&input)
            .map_err(convert_pipeline_error)?;
        Ok(convert_witness_bindings(result))
    }

    fn query_text_with_proof(
        &self,
        input: String,
    ) -> Result<(export_logic::QueryResult, export_logic::ProofTrace), export_err::NibliError> {
        self.emit_lints(&input);
        let (result, trace) = self
            .core
            .borrow()
            .query_text_with_proof(&input)
            .map_err(convert_pipeline_error)?;
        Ok((
            convert_query_result_to_export(&result),
            convert_proof_trace(trace),
        ))
    }

    fn compile_debug(
        &self,
        input: String,
    ) -> Result<export_logic::LogicBuffer, export_err::NibliError> {
        let buf = self
            .core
            .borrow()
            .compile_text(&input)
            .map_err(convert_pipeline_error)?;
        Ok(convert_logic_buffer_to_export(&buf))
    }

    fn reset_kb(&self) -> Result<(), export_err::NibliError> {
        self.linter.borrow_mut().reset();
        self.core.borrow().reset().map_err(convert_pipeline_error)
    }

    fn register_compute_predicate(&self, name: String) {
        self.core.borrow_mut().register_compute_predicate(name);
    }

    fn assert_fact(
        &self,
        relation: String,
        args: Vec<export_logic::LogicalTerm>,
    ) -> Result<u64, export_err::NibliError> {
        self.assert_fact_inner(relation, args, None)
    }

    fn assert_fact_with_id(
        &self,
        relation: String,
        args: Vec<export_logic::LogicalTerm>,
        id: u64,
    ) -> Result<(), export_err::NibliError> {
        self.assert_fact_inner(relation, args, Some(id)).map(|_| ())
    }

    fn retract_fact(&self, id: u64) -> Result<(), export_err::NibliError> {
        self.core
            .borrow()
            .retract_fact(id)
            .map_err(convert_pipeline_error)
    }

    fn list_facts(&self) -> Result<Vec<export_logic::FactSummary>, export_err::NibliError> {
        let facts = self
            .core
            .borrow()
            .list_facts()
            .map_err(convert_pipeline_error)?;
        Ok(convert_fact_summaries(facts))
    }
}

bindings::export!(NibliPipeline with_types_in bindings);
