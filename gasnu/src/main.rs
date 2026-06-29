//! Nibli gasnu (agent/runner): Wasmtime WASI P2 host + interactive REPL.
//!
//! Loads the fused WASM engine component, provides the `compute-backend` host
//! implementation (built-in arithmetic + external TCP backend), and runs an
//! interactive REPL (reedline-based) with these prefixes:
//!
//! - **(bare text)** — Assert Lojban facts
//! - **`?`** — Query with proof trace
//! - **`??`** — Query with witness extraction (find satisfying bindings)
//! - **`:debug`** — Compile to logic representation without asserting
//! - **`:load`** — Load a `.lojban` file (assert each line, skip `#` comments)
//! - **`:assert`** — Assert ground facts directly (bypasses Lojban parsing)
//! - **`:retract`** — Retract a fact by ID (triggers KB rebuild)
//! - **`:facts`** — List all active facts in the KB
//! - **`:compute`** — Register predicates for compute dispatch
//! - **`:backend`** — Show/change external compute backend address
//! - **`:reset`** — Clear the knowledge base
//! - **`:fuel`** / **`:memory`** — Show/set WASM execution limits

use anyhow::Result;
use nibli_protocol::compute_client::{BackendArg, BackendClient, BackendRequest};
use nibli_protocol::{ProofRule as ProtoRule, ProofStep as ProtoStep, ProofTrace as ProtoTrace};
use nibli_store::{NibliStore, StoredAssertion, StoredLogicalTerm as StoredTerm};
use reedline::{DefaultPrompt, Reedline, Signal};
use std::fs::File;
use std::io::{BufRead, BufReader, IsTerminal, Write};
use std::path::Path;
use wasmtime::component::{Component, HasSelf, Linker, ResourceAny};
use wasmtime::{Config, Engine, Store, StoreLimits, StoreLimitsBuilder};
use wasmtime_wasi::{ResourceTable, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

// ── Host state ──

/// Wasmtime host state: WASI context, resource table, memory limits,
/// and the (shared) external compute backend client.
struct HostState {
    ctx: WasiCtx,
    table: ResourceTable,
    limits: StoreLimits,
    /// External compute backend (JSON-Lines TCP). Client lives in nibli-protocol;
    /// built-in arithmetic is resolved by `try_builtin_arithmetic` before dispatch.
    backend: BackendClient,
}

/// Convert a WIT `compute-backend.logical-term` into the shared wire arg type.
fn term_to_arg(term: &compute_backend::LogicalTerm) -> BackendArg {
    use compute_backend::LogicalTerm;
    match term {
        LogicalTerm::Variable(s) => BackendArg::Variable(s.clone()),
        LogicalTerm::Constant(s) => BackendArg::Constant(s.clone()),
        LogicalTerm::Description(s) => BackendArg::Description(s.clone()),
        LogicalTerm::Unspecified => BackendArg::Unspecified,
        LogicalTerm::Number(n) => BackendArg::Number(*n),
    }
}

impl WasiView for HostState {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

mod pipeline_bind {
    wasmtime::component::bindgen!({ path: "../wit/world.wit", world: "lasna-pipeline" });
}

use pipeline_bind::lojban::nibli::compute_backend;
use pipeline_bind::lojban::nibli::error_types::NibliError;
use pipeline_bind::lojban::nibli::logic_types::LogicalTerm as EngineLogicalTerm;
use pipeline_bind::lojban::nibli::logic_types::{
    LogicBuffer as EngineLogicBuffer, LogicNode as EngineLogicNode, ProofRule, ProofTrace,
    QueryResult as EngineQueryResult, ResourceKind as EngineResourceKind,
    UnknownReason as EngineUnknownReason,
};
// Target types for the WIT → canonical reverse converter (so the host can render
// the `:debug` logic buffer via nibli-render).
use nibli_types::logic::{
    LogicBuffer as NibliBuffer, LogicNode as NibliNode, LogicalTerm as NibliTerm,
};

/// Format a LogicalTerm from the engine bindings for display.
fn format_term(term: &EngineLogicalTerm) -> String {
    wit_term_to_types(term).trace_display()
}

fn format_query_result(result: &EngineQueryResult) -> String {
    match result {
        EngineQueryResult::True => "TRUE".to_string(),
        EngineQueryResult::False => "FALSE".to_string(),
        EngineQueryResult::Unknown(EngineUnknownReason::CycleCut) => {
            "UNKNOWN (cycle-cut)".to_string()
        }
        EngineQueryResult::Unknown(EngineUnknownReason::IncompleteKnowledge) => {
            "UNKNOWN (incomplete-knowledge)".to_string()
        }
        EngineQueryResult::Unknown(EngineUnknownReason::NafDependent) => {
            "UNKNOWN (naf-dependent)".to_string()
        }
        EngineQueryResult::Unknown(EngineUnknownReason::BackendUnavailable) => {
            "UNKNOWN (backend-unavailable)".to_string()
        }
        EngineQueryResult::Unknown(EngineUnknownReason::NonFinite) => {
            "UNKNOWN (non-finite)".to_string()
        }
        EngineQueryResult::ResourceExceeded(EngineResourceKind::Depth) => {
            "RESOURCE_EXCEEDED (depth)".to_string()
        }
        EngineQueryResult::ResourceExceeded(EngineResourceKind::Fuel) => {
            "RESOURCE_EXCEEDED (fuel)".to_string()
        }
        EngineQueryResult::ResourceExceeded(EngineResourceKind::Memory) => {
            "RESOURCE_EXCEEDED (memory)".to_string()
        }
    }
}

/// Convert a WIT `LogicalTerm` to the canonical `nibli_types` term (pure 1:1).
fn wit_term_to_types(t: &EngineLogicalTerm) -> NibliTerm {
    match t {
        EngineLogicalTerm::Variable(v) => NibliTerm::Variable(v.clone()),
        EngineLogicalTerm::Constant(c) => NibliTerm::Constant(c.clone()),
        EngineLogicalTerm::Description(d) => NibliTerm::Description(d.clone()),
        EngineLogicalTerm::Unspecified => NibliTerm::Unspecified,
        EngineLogicalTerm::Number(n) => NibliTerm::Number(*n),
    }
}

/// Convert a WIT `LogicNode` to the canonical `nibli_types` node (pure 1:1 — the
/// WIT `logic-node` variant mirrors `nibli_types::logic::LogicNode` exactly).
fn wit_logic_node_to_types(n: &EngineLogicNode) -> NibliNode {
    use EngineLogicNode as W;
    use NibliNode as N;
    match n {
        W::Predicate((rel, args)) => {
            N::Predicate((rel.clone(), args.iter().map(wit_term_to_types).collect()))
        }
        W::ComputeNode((rel, args)) => {
            N::ComputeNode((rel.clone(), args.iter().map(wit_term_to_types).collect()))
        }
        W::AndNode((l, r)) => N::AndNode((*l, *r)),
        W::OrNode((l, r)) => N::OrNode((*l, *r)),
        W::NotNode(i) => N::NotNode(*i),
        W::ExistsNode((v, b)) => N::ExistsNode((v.clone(), *b)),
        W::ForAllNode((v, b)) => N::ForAllNode((v.clone(), *b)),
        W::PastNode(i) => N::PastNode(*i),
        W::PresentNode(i) => N::PresentNode(*i),
        W::FutureNode(i) => N::FutureNode(*i),
        W::ObligatoryNode(i) => N::ObligatoryNode(*i),
        W::PermittedNode(i) => N::PermittedNode(*i),
        W::CountNode((v, c, b)) => N::CountNode((v.clone(), *c, *b)),
    }
}

/// Convert the WIT `LogicBuffer` (returned by `:debug`) to the canonical
/// `nibli_types` buffer so the host can render it via nibli-render.
fn wit_logic_buffer_to_types(buf: &EngineLogicBuffer) -> NibliBuffer {
    NibliBuffer {
        nodes: buf.nodes.iter().map(wit_logic_node_to_types).collect(),
        roots: buf.roots.clone(),
    }
}

/// Convert a WIT ProofRule to the protocol wire type. Embedded terms reuse
/// `wit_term_to_types` (WIT enum → canonical `LogicalTerm` enum) — the proto term
/// is now that same canonical enum, so no separate term converter is needed.
fn rule_to_proto(rule: &ProofRule) -> ProtoRule {
    match rule {
        ProofRule::Conjunction => ProtoRule::Conjunction,
        ProofRule::DisjunctionCheck(s) => ProtoRule::DisjunctionCheck { detail: s.clone() },
        ProofRule::DisjunctionIntro(s) => ProtoRule::DisjunctionIntro { side: s.clone() },
        ProofRule::Negation => ProtoRule::Negation,
        ProofRule::ModalPassthrough(s) => ProtoRule::ModalPassthrough { kind: s.clone() },
        ProofRule::ExistsWitness((var, term)) => ProtoRule::ExistsWitness {
            var: var.clone(),
            term: wit_term_to_types(term),
        },
        ProofRule::ExistsFailed => ProtoRule::ExistsFailed,
        ProofRule::ForallVacuous => ProtoRule::ForallVacuous,
        ProofRule::ForallVerified(entities) => ProtoRule::ForallVerified {
            entities: entities.iter().map(wit_term_to_types).collect(),
        },
        ProofRule::ForallCounterexample(term) => ProtoRule::ForallCounterexample {
            entity: wit_term_to_types(term),
        },
        ProofRule::CountResult((expected, actual)) => ProtoRule::CountResult {
            expected: *expected,
            actual: *actual,
        },
        ProofRule::PredicateCheck((method, detail)) => ProtoRule::PredicateCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        ProofRule::ComputeCheck((method, detail)) => ProtoRule::ComputeCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        ProofRule::Asserted(fact) => ProtoRule::Asserted { fact: fact.clone() },
        ProofRule::Derived((label, fact)) => ProtoRule::Derived {
            label: label.clone(),
            fact: fact.clone(),
        },
        ProofRule::ProofRef(fact) => ProtoRule::ProofRef { fact: fact.clone() },
        ProofRule::EqualitySubstitution((original, du_facts, substituted)) => {
            ProtoRule::EqualitySubstitution {
                original: original.clone(),
                du_facts: du_facts.clone(),
                substituted: substituted.clone(),
            }
        }
        ProofRule::RuleAttemptFailed((label, cond)) => ProtoRule::RuleAttemptFailed {
            rule_label: label.clone(),
            failed_condition: cond.clone(),
        },
        ProofRule::PredicateNotFound(pred) => ProtoRule::PredicateNotFound {
            predicate: pred.clone(),
        },
    }
}

/// Convert a WIT ProofTrace to the protocol wire type for shared formatting.
fn trace_to_proto(trace: &ProofTrace) -> ProtoTrace {
    ProtoTrace {
        steps: trace
            .steps
            .iter()
            .map(|s| ProtoStep {
                rule: rule_to_proto(&s.rule),
                holds: s.holds,
                children: s.children.clone(),
            })
            .collect(),
        root: trace.root,
        // Read the engine-computed flags from the WIT trace (single source of
        // truth) instead of recomputing them from the steps.
        naf_dependent: trace.naf_dependent,
        cwa_false: trace.cwa_false,
    }
}

/// Try built-in arithmetic evaluation for a single predicate.
/// Returns Some(bool) for pilji/sumji/dilcu with 3+ numeric args.
fn try_builtin_arithmetic(relation: &str, args: &[compute_backend::LogicalTerm]) -> Option<bool> {
    use compute_backend::LogicalTerm;
    let extract_num = |t: &LogicalTerm| -> Option<f64> {
        if let LogicalTerm::Number(n) = t {
            Some(*n)
        } else {
            None
        }
    };
    if args.len() >= 3 {
        if let (Some(x1), Some(x2), Some(x3)) = (
            extract_num(&args[0]),
            extract_num(&args[1]),
            extract_num(&args[2]),
        ) {
            // The relation match + tolerant-equality comparison is shared with the
            // logji engine fast path (and the Python reference backend).
            return nibli_types::eval_arithmetic(relation, &[x1, x2, x3]);
        }
    }
    None
}

impl compute_backend::Host for HostState {
    fn evaluate(
        &mut self,
        relation: String,
        args: Vec<compute_backend::LogicalTerm>,
    ) -> std::result::Result<bool, NibliError> {
        // 1. Built-in arithmetic predicates: x1 = op(x2, x3) — zero overhead
        if let Some(r) = try_builtin_arithmetic(&relation, &args) {
            return Ok(r);
        }

        // 2. Forward to the external backend (if configured)
        let wire_args: Vec<BackendArg> = args.iter().map(term_to_arg).collect();
        self.backend
            .dispatch(&relation, &wire_args)
            .map_err(|msg| NibliError::Backend((relation, msg)))
    }

    fn evaluate_batch(
        &mut self,
        requests: Vec<compute_backend::ComputeRequest>,
    ) -> Vec<compute_backend::ComputeResult> {
        let mut results = vec![compute_backend::ComputeResult::Err(String::new()); requests.len()];
        let mut pending_idx: Vec<usize> = Vec::new();
        let mut pending_reqs: Vec<BackendRequest> = Vec::new();

        // 1. Resolve built-in arithmetic locally; collect external requests.
        for (i, req) in requests.iter().enumerate() {
            if let Some(r) = try_builtin_arithmetic(&req.relation, &req.args) {
                results[i] = compute_backend::ComputeResult::Ok(r);
            } else {
                pending_idx.push(i);
                pending_reqs.push(BackendRequest {
                    relation: req.relation.clone(),
                    args: req.args.iter().map(term_to_arg).collect(),
                });
            }
        }

        if pending_reqs.is_empty() {
            return results;
        }

        // 2. Pipeline the external requests. The shared client handles the
        //    no-backend case (per-item "No compute backend configured"),
        //    retry-once, and idle-connection reaping.
        let batch = self.backend.dispatch_batch(&pending_reqs);
        for (idx, result) in pending_idx.into_iter().zip(batch) {
            results[idx] = match result {
                Ok(r) => compute_backend::ComputeResult::Ok(r),
                Err(e) => compute_backend::ComputeResult::Err(e),
            };
        }
        results
    }
}

/// Parse a `:assert` command string into (relation, args).
/// Numbers are detected automatically; everything else is treated as a Constant.
/// Format: `<relation> <arg1> <arg2> ...`
fn parse_assert_args(input: &str) -> std::result::Result<(String, Vec<EngineLogicalTerm>), String> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err("Usage: :assert <relation> <arg1> <arg2> ...".to_string());
    }
    let relation = parts[0].to_string();
    let args = parts[1..]
        .iter()
        .map(|&s| {
            if let Ok(n) = s.parse::<f64>() {
                EngineLogicalTerm::Number(n)
            } else {
                EngineLogicalTerm::Constant(s.to_string())
            }
        })
        .collect();
    Ok((relation, args))
}

/// Convert a WIT LogicalTerm to a StoredTerm for persistence.
fn wit_term_to_stored(t: &EngineLogicalTerm) -> StoredTerm {
    match t {
        EngineLogicalTerm::Variable(v) => StoredTerm::Variable(v.clone()),
        EngineLogicalTerm::Constant(c) => StoredTerm::Constant(c.clone()),
        EngineLogicalTerm::Description(d) => StoredTerm::Description(d.clone()),
        EngineLogicalTerm::Unspecified => StoredTerm::Unspecified,
        EngineLogicalTerm::Number(n) => StoredTerm::Number(*n),
    }
}

/// Convert a StoredTerm back to a WIT LogicalTerm for replay.
fn stored_term_to_wit(t: &StoredTerm) -> EngineLogicalTerm {
    match t {
        StoredTerm::Variable(v) => EngineLogicalTerm::Variable(v.clone()),
        StoredTerm::Constant(c) => EngineLogicalTerm::Constant(c.clone()),
        StoredTerm::Description(d) => EngineLogicalTerm::Description(d.clone()),
        StoredTerm::Unspecified => EngineLogicalTerm::Unspecified,
        StoredTerm::Number(n) => EngineLogicalTerm::Number(*n),
    }
}

/// Persist a text assertion to the store (if configured).
fn persist_text(nibli_store: &mut Option<NibliStore>, fact_id: u64, text: &str) {
    if let Some(s) = nibli_store.as_mut() {
        let assertion = StoredAssertion::Text(text.to_string());
        if let Ok(payload) = postcard::to_allocvec(&assertion) {
            let _ = s.insert_fact(fact_id, text.to_string(), payload);
        }
    }
}

/// Persist a direct assertion to the store (if configured).
fn persist_direct(
    nibli_store: &mut Option<NibliStore>,
    fact_id: u64,
    relation: &str,
    args: &[EngineLogicalTerm],
) {
    if let Some(s) = nibli_store.as_mut() {
        let assertion = StoredAssertion::Direct {
            relation: relation.to_string(),
            args: args.iter().map(wit_term_to_stored).collect(),
        };
        let label = format!(
            ":assert {} {}",
            relation,
            args.iter()
                .map(|a| format_term(a))
                .collect::<Vec<_>>()
                .join(" ")
        );
        if let Ok(payload) = postcard::to_allocvec(&assertion) {
            let _ = s.insert_fact(fact_id, label, payload);
        }
    }
}

fn refuel(store: &mut Store<HostState>, budget: u64) {
    let _ = store.set_fuel(budget);
}

/// Classify a Wasmtime host trap as a resource-limit kind, if it is one. Fuel
/// exhaustion is the typed `wasmtime::Trap::OutOfFuel` (or a cause-chain mention
/// of "fuel"); a memory-cap denial surfaces deeper in the chain
/// ("forcing trap when growing memory..."). Returns `None` for a genuine
/// non-resource trap (e.g. a guest panic). A query's resource trap is
/// synthesized into a RESOURCE_EXCEEDED verdict (see the `?` handler); a
/// non-query trap renders the `[Limit]`/`[Host Error]` message via
/// `format_host_error`. (Depth is never a host trap — the engine returns it
/// directly — so this only ever yields Fuel/Memory.)
fn classify_resource_trap(e: &anyhow::Error) -> Option<EngineResourceKind> {
    if let Some(trap) = e.downcast_ref::<wasmtime::Trap>() {
        if matches!(trap, wasmtime::Trap::OutOfFuel) {
            return Some(EngineResourceKind::Fuel);
        }
    }
    let chain_contains = |needle: &str| e.chain().any(|cause| cause.to_string().contains(needle));
    if chain_contains("fuel") {
        Some(EngineResourceKind::Fuel)
    } else if chain_contains("forcing trap when growing memory")
        || chain_contains("memory")
        || chain_contains("Memory")
    {
        Some(EngineResourceKind::Memory)
    } else {
        None
    }
}

/// Actionable hint shown under a query's host-synthesized RESOURCE_EXCEEDED
/// verdict, so the operator knows how to raise the budget and retry.
fn resource_hint(kind: EngineResourceKind) -> &'static str {
    match kind {
        EngineResourceKind::Fuel => {
            "WASM fuel budget exhausted; raise it with NIBLI_FUEL or :fuel, then re-run"
        }
        EngineResourceKind::Memory => {
            "WASM memory cap exceeded; raise it with NIBLI_MEMORY_MB or :memory, then re-run"
        }
        EngineResourceKind::Depth => "backward-chaining depth limit hit; raise max_chain_depth",
    }
}

/// Render a NON-query host trap (assertion / `:load` / find / `:retract`) as a
/// friendly message: a resource trap becomes a `[Limit]` line, a genuine trap
/// becomes `[Host Error]`. A QUERY trap is instead translated into a
/// RESOURCE_EXCEEDED verdict at the `?` handler.
fn format_host_error(e: &anyhow::Error) -> String {
    match classify_resource_trap(e) {
        Some(EngineResourceKind::Fuel) => {
            "[Limit] Execution fuel exhausted. Increase with NIBLI_FUEL env var or :fuel command."
                .to_string()
        }
        Some(EngineResourceKind::Memory) => {
            "[Limit] Memory limit exceeded. Increase with NIBLI_MEMORY_MB env var or :memory command."
                .to_string()
        }
        // Depth never traps the host; None is a genuine non-resource trap.
        _ => format!("[Host Error] {:?}", e),
    }
}

fn format_nibli_error(e: &NibliError) -> String {
    match e {
        NibliError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        NibliError::Semantic(msg) => format!("[Semantic Error] {}", msg),
        NibliError::Reasoning(msg) => format!("[Reasoning Error] {}", msg),
        NibliError::Backend((kind, msg)) => format!("[Backend Error] {} — {}", kind, msg),
    }
}

// ── REPL driver ──

/// One journaled, successful KB mutation. After a wasm trap poisons the
/// component instance, replaying these in order on a fresh instance rebuilds
/// a byte-identical session (the engine is deterministic: identical fact ids
/// and Skolem numbering). Queries are not journaled — their only KB side
/// effect (flat-path compute auto-ingestion) is recomputed on demand.
enum JournalEntry {
    /// `id` is the fact id assigned at the original assertion (or the durable
    /// store id at replay). Replayed via `assert-text-with-id` so a trap-rebuild
    /// AFTER a restart keeps the live fact-id namespace equal to the store's.
    AssertText {
        text: String,
        id: u64,
    },
    AssertDirect {
        relation: String,
        args: Vec<EngineLogicalTerm>,
        id: u64,
    },
    Retract(u64),
    RegisterCompute(String),
}

/// All host-side REPL state. Factored out of `main` (instead of a closure
/// over a dozen locals) so the trap-recovery path can swap the poisoned
/// Store/instance/session for fresh ones mid-session.
struct Repl {
    engine: Engine,
    component: Component,
    linker: Linker<HostState>,
    store: Store<HostState>,
    pipeline: pipeline_bind::LasnaPipeline,
    session_handle: ResourceAny,
    fuel_budget: u64,
    memory_limit_mb: usize,
    nibli_store: Option<NibliStore>,
    db_path: Option<String>,
    /// Successful KB mutations, in order — the rebuild-after-trap replay source.
    journal: Vec<JournalEntry>,
    /// True while replaying the journal (suppresses re-journaling and rebuild).
    replaying: bool,
    /// Set when a host-level error may have poisoned the component instance.
    /// The rebuild runs LAZILY before the next session call, so an intervening
    /// `:fuel`/`:memory` raise applies to the replay.
    needs_rebuild: bool,
}

impl Repl {
    /// Create a fresh Store + component instance + session resource.
    /// Used at startup and (after a wasm trap poisons the instance) by the
    /// rebuild path — `Component` and `Linker` are reusable across stores.
    fn instantiate_session(
        engine: &Engine,
        component: &Component,
        linker: &Linker<HostState>,
        fuel_budget: u64,
        memory_limit_mb: usize,
        backend_addr: Option<String>,
    ) -> Result<(Store<HostState>, pipeline_bind::LasnaPipeline, ResourceAny)> {
        let state = HostState {
            ctx: WasiCtxBuilder::new()
                .inherit_stdout()
                .inherit_stderr()
                .build(),
            table: ResourceTable::new(),
            limits: StoreLimitsBuilder::new()
                .memory_size(memory_limit_mb * 1024 * 1024)
                .trap_on_grow_failure(true)
                .build(),
            backend: {
                let mut b = BackendClient::new();
                if let Some(addr) = &backend_addr {
                    b.set_addr(addr);
                }
                b
            },
        };
        let mut store = Store::new(engine, state);
        store.set_fuel(fuel_budget)?;
        store.limiter(|state| &mut state.limits);
        let pipeline = pipeline_bind::LasnaPipeline::instantiate(&mut store, component, linker)?;
        let session_handle = pipeline
            .lojban_nibli_lasna()
            .session()
            .call_constructor(&mut store)?;
        Ok((store, pipeline, session_handle))
    }

    /// Make the session callable for the next command: rebuild lazily if a
    /// trap poisoned the instance, then refuel.
    fn prepare_session(&mut self) {
        if self.needs_rebuild && !self.replaying {
            self.rebuild_after_trap();
        }
        refuel(&mut self.store, self.fuel_budget);
    }

    /// A wasm trap permanently poisons the component instance (component-model
    /// semantics forbid re-entering it). Recover by abandoning the poisoned
    /// Store/instance/session — WITHOUT resource_drop, which would itself have
    /// to enter the dead instance — re-instantiating from the compiled
    /// Component, and replaying the journal. The engine is deterministic, so
    /// the rebuilt session is byte-identical (same fact ids, same Skolem
    /// numbering); the guest's per-assert diagnostics ([Skolem]/[Rule] lines)
    /// print during the replay, making the rebuilt state visible.
    fn rebuild_after_trap(&mut self) {
        self.needs_rebuild = false;
        println!(
            "[Session] Wasm trap poisoned the component instance; rebuilding and replaying {} command(s)...",
            self.journal.len()
        );
        let backend_addr = self.store.data().backend.addr().map(str::to_string);
        match Self::instantiate_session(
            &self.engine,
            &self.component,
            &self.linker,
            self.fuel_budget,
            self.memory_limit_mb,
            backend_addr,
        ) {
            Ok((store, pipeline, session_handle)) => {
                // The old store (with the dead session resource inside it) is
                // dropped here; its destructor never re-enters the instance.
                self.store = store;
                self.pipeline = pipeline;
                self.session_handle = session_handle;
            }
            Err(e) => {
                println!("[Session] Rebuild failed: {:?}", e);
                return;
            }
        }
        self.replaying = true;
        let journal = std::mem::take(&mut self.journal);
        let total = journal.len();
        let mut ok = 0usize;
        let mut failed: Option<String> = None;
        for entry in &journal {
            match self.replay_entry(entry) {
                Ok(()) => ok += 1,
                Err(e) => {
                    failed = Some(format!("{}", e));
                    break;
                }
            }
        }
        self.journal = journal;
        self.replaying = false;
        if let Some(err) = failed {
            println!(
                "[Session] Replay incomplete ({} of {}): {} — KB state may be partial; consider :reset",
                ok, total, err
            );
        }
    }

    /// Replay one journaled mutation against the fresh session. Persistence is
    /// NOT re-run: the mutation was persisted when it first succeeded, and
    /// re-inserting would spuriously advance the durable store's HLC clock.
    fn replay_entry(&mut self, entry: &JournalEntry) -> Result<()> {
        refuel(&mut self.store, self.fuel_budget);
        let session = self.pipeline.lojban_nibli_lasna().session();
        match entry {
            JournalEntry::AssertText { text, id } => {
                session
                    .call_assert_text_with_id(&mut self.store, self.session_handle, text, *id)?
                    .map_err(|e| anyhow::anyhow!("{}", format_nibli_error(&e)))?;
            }
            JournalEntry::AssertDirect { relation, args, id } => {
                session
                    .call_assert_fact_with_id(
                        &mut self.store,
                        self.session_handle,
                        relation,
                        args,
                        *id,
                    )?
                    .map_err(|e| anyhow::anyhow!("{}", format_nibli_error(&e)))?;
            }
            JournalEntry::Retract(id) => {
                session
                    .call_retract_fact(&mut self.store, self.session_handle, *id)?
                    .map_err(|e| anyhow::anyhow!("{}", format_nibli_error(&e)))?;
            }
            JournalEntry::RegisterCompute(name) => {
                session.call_register_compute_predicate(
                    &mut self.store,
                    self.session_handle,
                    name,
                )?;
            }
        }
        Ok(())
    }

    /// Replay persisted facts from the durable store into the WASM session.
    fn replay_persisted(&mut self) {
        let facts = match self.nibli_store.as_ref() {
            Some(s) => match s.all_active_facts() {
                Ok(facts) if !facts.is_empty() => facts,
                _ => return,
            },
            None => return,
        };
        println!("[Store] Replaying {} persisted facts...", facts.len());
        let mut replayed = 0u32;
        let mut replay_errors = 0u32;
        for fact in &facts {
            let assertion: StoredAssertion = match postcard::from_bytes(&fact.payload) {
                Ok(a) => a,
                Err(e) => {
                    println!("[Store] Fact #{} deserialize error: {}", fact.id, e);
                    replay_errors += 1;
                    continue;
                }
            };
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match assertion {
                StoredAssertion::Text(ref text) => {
                    // Replay with the DURABLE store id so the live session's
                    // fact-id namespace stays equal to the store's (no drift).
                    match session.call_assert_text_with_id(
                        &mut self.store,
                        self.session_handle,
                        text,
                        fact.id,
                    ) {
                        Ok(Ok(_)) => {
                            self.journal.push(JournalEntry::AssertText {
                                text: text.clone(),
                                id: fact.id,
                            });
                            replayed += 1;
                        }
                        Ok(Err(e)) => {
                            println!(
                                "[Store] Replay fact #{}: {}",
                                fact.id,
                                format_nibli_error(&e)
                            );
                            replay_errors += 1;
                        }
                        Err(e) => {
                            println!(
                                "[Store] Replay fact #{}: {}",
                                fact.id,
                                format_host_error(&e)
                            );
                            self.needs_rebuild = true;
                            replay_errors += 1;
                        }
                    }
                }
                StoredAssertion::Direct {
                    ref relation,
                    ref args,
                } => {
                    let wit_args: Vec<EngineLogicalTerm> =
                        args.iter().map(stored_term_to_wit).collect();
                    match session.call_assert_fact_with_id(
                        &mut self.store,
                        self.session_handle,
                        relation,
                        &wit_args,
                        fact.id,
                    ) {
                        Ok(Ok(_)) => {
                            self.journal.push(JournalEntry::AssertDirect {
                                relation: relation.clone(),
                                args: wit_args.clone(),
                                id: fact.id,
                            });
                            replayed += 1;
                        }
                        Ok(Err(e)) => {
                            println!(
                                "[Store] Replay fact #{}: {}",
                                fact.id,
                                format_nibli_error(&e)
                            );
                            replay_errors += 1;
                        }
                        Err(e) => {
                            println!(
                                "[Store] Replay fact #{}: {}",
                                fact.id,
                                format_host_error(&e)
                            );
                            self.needs_rebuild = true;
                            replay_errors += 1;
                        }
                    }
                }
            }
        }
        if replay_errors > 0 {
            println!("[Store] Replay: {} ok, {} errors", replayed, replay_errors);
        } else {
            println!("[Store] Replay complete ({} facts)", replayed);
        }
    }

    /// Per-command dispatch shared by interactive and script modes.
    /// Returns true when the session should quit (`:quit`), false to continue.
    fn dispatch(&mut self, input: &str) -> bool {
        match input {
            ":quit" | ":q" => return true,
            ":reset" | ":r" => {
                self.prepare_session();
                let session = self.pipeline.lojban_nibli_lasna().session();
                match session.call_reset_kb(&mut self.store, self.session_handle) {
                    Ok(Ok(())) => {
                        if let Some(s) = self.nibli_store.as_mut() {
                            let _ = s.clear();
                        }
                        self.journal.clear();
                        println!("[Reset] Knowledge base cleared.");
                    }
                    Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                    Err(e) => {
                        println!("{}", format_host_error(&e));
                        self.needs_rebuild = true;
                    }
                }
                return false;
            }
            ":db" => {
                match &self.nibli_store {
                    Some(s) => {
                        let active = s.active_fact_count().unwrap_or(0);
                        let total = s.total_fact_count().unwrap_or(0);
                        println!(
                            "[Store] {} (node: {})",
                            self.db_path.as_deref().unwrap_or("?"),
                            s.node_id()
                        );
                        println!(
                            "[Store] {} active facts, {} total (including retracted)",
                            active, total
                        );
                    }
                    None => println!(
                        "[Store] No persistent store configured. Set NIBLI_DB_PATH env var."
                    ),
                }
                return false;
            }
            ":fuel" | ":f" => {
                println!("[Fuel] Budget: {} per command", self.fuel_budget);
                return false;
            }
            ":memory" | ":m" => {
                println!("[Memory] Limit: {} MB", self.memory_limit_mb);
                return false;
            }
            ":backend" | ":b" => {
                let state = self.store.data();
                match state.backend.addr() {
                    Some(addr) => {
                        let status = if state.backend.is_connected() {
                            "connected"
                        } else {
                            "not connected (lazy)"
                        };
                        println!("[Backend] {} ({})", addr, status);
                    }
                    None => println!("[Backend] Not configured"),
                }
                return false;
            }
            ":facts" => {
                self.prepare_session();
                let session = self.pipeline.lojban_nibli_lasna().session();
                match session.call_list_facts(&mut self.store, self.session_handle) {
                    Ok(Ok(facts)) => {
                        if facts.is_empty() {
                            println!("[Facts] Knowledge base is empty.");
                        } else {
                            println!("[Facts] {} active fact(s):", facts.len());
                            for f in &facts {
                                let roots_label = if f.root_count == 1 { "root" } else { "roots" };
                                println!(
                                    "  #{}: {} ({} {})",
                                    f.id, f.label, f.root_count, roots_label
                                );
                            }
                        }
                    }
                    Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                    Err(e) => {
                        println!("{}", format_host_error(&e));
                        self.needs_rebuild = true;
                    }
                }
                return false;
            }
            ":help" | ":h" => {
                println!("  <text>              Assert Lojban as fact");
                println!("  ? <text>            Query (collapsed macro-logical proof)");
                println!("  :proof-verbose <text> Query (full role-level proof trace)");
                println!("  ?? <text>           Find witnesses (answer variables)");
                println!("  :debug <text>       Show compiled logic tree");
                println!("  :load <filepath>    Load a .lojban file (assert each line)");
                println!("  :dump <filepath>    Export KB as a .lojban file");
                println!("  :compute <name>     Register predicate for compute dispatch");
                println!("  :assert <rel> <args..> Assert a ground fact directly");
                println!("  :retract <id>       Retract a fact by ID (rebuilds KB)");
                println!("  :facts              List all active facts in the KB");
                println!("  :backend [host:port] Show or set compute backend address");
                println!("  :fuel [amount]      Show or set WASM fuel budget per command");
                println!("  :memory [mb]        Show or set WASM memory limit in MB");
                println!("  :db                 Show persistent store info");
                println!("  :export <redb-file> Export store to a new redb file");
                println!("  :reset              Clear all facts (fresh KB)");
                println!("  :quit               Exit");
                return false;
            }
            _ => {}
        }

        // ── Route by prefix ──
        if let Some(debug_text) = input.strip_prefix(":debug ") {
            let text = debug_text.trim();
            if text.is_empty() {
                println!("[Host] Usage: :debug <lojban text>");
                return false;
            }
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match session.call_compile_debug(&mut self.store, self.session_handle, text) {
                Ok(Ok(wit_buf)) => {
                    let buf = wit_logic_buffer_to_types(&wit_buf);
                    let tree = nibli_render::render_logic_tree(&buf, nibli_render::Register::Spec);
                    let english =
                        nibli_render::render_logic_buffer(&buf, nibli_render::Register::Spec);
                    println!("[Logic]\n{}", tree.trim_end());
                    println!("\n[English] {}", english);
                }
                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                Err(e) => {
                    println!("{}", format_host_error(&e));
                    self.needs_rebuild = true;
                }
            }
        } else if let Some(backend_arg) = input.strip_prefix(":backend ") {
            let addr = backend_arg.trim();
            if addr.is_empty() {
                let state = self.store.data();
                match state.backend.addr() {
                    Some(a) => println!("[Backend] {}", a),
                    None => println!("[Backend] Not configured"),
                }
            } else {
                // set_addr drops any stale connection when the address changes.
                self.store.data_mut().backend.set_addr(addr);
                println!("[Backend] Set to {} (connects on first use)", addr);
            }
        } else if let Some(fuel_arg) = input.strip_prefix(":fuel ") {
            let arg = fuel_arg.trim();
            match arg.parse::<u64>() {
                Ok(n) if n > 0 => {
                    self.fuel_budget = n;
                    println!("[Fuel] Budget set to {}", self.fuel_budget);
                }
                _ => println!("[Host] Usage: :fuel <positive-integer>"),
            }
        } else if let Some(mem_arg) = input.strip_prefix(":memory ") {
            let arg = mem_arg.trim();
            match arg.parse::<usize>() {
                Ok(n) if n > 0 => {
                    self.memory_limit_mb = n;
                    let limit = self.memory_limit_mb;
                    let state = self.store.data_mut();
                    state.limits = StoreLimitsBuilder::new()
                        .memory_size(limit * 1024 * 1024)
                        .trap_on_grow_failure(true)
                        .build();
                    println!("[Memory] Limit set to {} MB", self.memory_limit_mb);
                }
                _ => println!("[Host] Usage: :memory <positive-integer-mb>"),
            }
        } else if let Some(compute_name) = input.strip_prefix(":compute ") {
            let name = compute_name.trim();
            if name.is_empty() {
                println!("[Host] Usage: :compute <predicate-name>");
                return false;
            }
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match session.call_register_compute_predicate(
                &mut self.store,
                self.session_handle,
                name,
            ) {
                Ok(()) => {
                    self.journal
                        .push(JournalEntry::RegisterCompute(name.to_string()));
                    println!("[Compute] Registered '{}' for external dispatch", name)
                }
                Err(e) => {
                    println!("{}", format_host_error(&e));
                    self.needs_rebuild = true;
                }
            }
        } else if let Some(assert_args) = input.strip_prefix(":assert ") {
            let text = assert_args.trim();
            if text.is_empty() {
                println!("[Host] Usage: :assert <relation> <arg1> <arg2> ...");
                return false;
            }
            match parse_assert_args(text) {
                Ok((relation, args)) => {
                    let display_args: Vec<String> = args
                        .iter()
                        .map(|a| match a {
                            EngineLogicalTerm::Number(n) => format!("{}", n),
                            EngineLogicalTerm::Constant(s) => s.clone(),
                            _ => "?".to_string(),
                        })
                        .collect();
                    self.prepare_session();
                    let session = self.pipeline.lojban_nibli_lasna().session();
                    match session.call_assert_fact(
                        &mut self.store,
                        self.session_handle,
                        &relation,
                        &args,
                    ) {
                        Ok(Ok(fact_id)) => {
                            persist_direct(&mut self.nibli_store, fact_id, &relation, &args);
                            self.journal.push(JournalEntry::AssertDirect {
                                relation: relation.clone(),
                                args: args.clone(),
                                id: fact_id,
                            });
                            println!(
                                "[Fact #{}] {}({}) asserted.",
                                fact_id,
                                relation,
                                display_args.join(", ")
                            );
                        }
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => {
                            println!("{}", format_host_error(&e));
                            self.needs_rebuild = true;
                        }
                    }
                }
                Err(e) => println!("[Error] {}", e),
            }
        } else if let Some(retract_arg) = input.strip_prefix(":retract ") {
            let arg = retract_arg.trim();
            match arg.parse::<u64>() {
                Ok(id) => {
                    self.prepare_session();
                    let session = self.pipeline.lojban_nibli_lasna().session();
                    match session.call_retract_fact(&mut self.store, self.session_handle, id) {
                        Ok(Ok(())) => {
                            if let Some(s) = self.nibli_store.as_mut() {
                                let _ = s.retract_fact(id);
                            }
                            self.journal.push(JournalEntry::Retract(id));
                            println!("[Retract] Fact #{} retracted. KB rebuilt.", id);
                        }
                        Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                        Err(e) => {
                            println!("{}", format_host_error(&e));
                            self.needs_rebuild = true;
                        }
                    }
                }
                Err(_) => println!("[Host] Usage: :retract <fact-id>"),
            }
        } else if let Some(load_arg) = input.strip_prefix(":load ") {
            let filepath = load_arg.trim();
            if filepath.is_empty() {
                println!("[Host] Usage: :load <filepath>");
                return false;
            }
            let path = Path::new(filepath);
            if !path.exists() {
                println!("[Load] File not found: {}", filepath);
                return false;
            }
            let file = match File::open(path) {
                Ok(f) => f,
                Err(e) => {
                    println!("[Load] Cannot open file: {}", e);
                    return false;
                }
            };
            let reader = BufReader::new(file);
            let mut asserted = 0u32;
            let mut skipped = 0u32;
            let mut errors = 0u32;
            for (line_num, line_result) in reader.lines().enumerate() {
                let line = match line_result {
                    Ok(l) => l,
                    Err(e) => {
                        println!("[Load] Read error at line {}: {}", line_num + 1, e);
                        errors += 1;
                        continue;
                    }
                };
                let trimmed = line.trim();
                // Skip blank lines and comments (lines starting with #)
                if trimmed.is_empty() || trimmed.starts_with('#') {
                    skipped += 1;
                    continue;
                }
                self.prepare_session();
                let session = self.pipeline.lojban_nibli_lasna().session();
                match session.call_assert_text(&mut self.store, self.session_handle, trimmed) {
                    Ok(Ok(fact_id)) => {
                        persist_text(&mut self.nibli_store, fact_id, trimmed);
                        self.journal.push(JournalEntry::AssertText {
                            text: trimmed.to_string(),
                            id: fact_id,
                        });
                        println!("[Fact #{}] {}", fact_id, trimmed);
                        asserted += 1;
                    }
                    Ok(Err(e)) => {
                        println!("[Load] line {}: {}", line_num + 1, format_nibli_error(&e));
                        errors += 1;
                    }
                    Err(e) => {
                        println!("[Load] line {}: {}", line_num + 1, format_host_error(&e));
                        self.needs_rebuild = true;
                        errors += 1;
                    }
                }
            }
            println!(
                "[Load] Done: {} asserted, {} skipped, {} errors",
                asserted, skipped, errors
            );
        } else if let Some(dump_arg) = input.strip_prefix(":dump ") {
            let filepath = dump_arg.trim();
            if filepath.is_empty() {
                println!("[Host] Usage: :dump <filepath>");
                return false;
            }
            // Get facts from WASM session (works with or without persistent store)
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match session.call_list_facts(&mut self.store, self.session_handle) {
                Ok(Ok(facts)) => {
                    if facts.is_empty() {
                        println!("[Dump] Knowledge base is empty — nothing to dump.");
                    } else {
                        match File::create(filepath) {
                            Ok(mut file) => {
                                let mut written = 0u32;
                                for f in &facts {
                                    // The label is the original Lojban text (or :assert form)
                                    if writeln!(file, "{}", f.label).is_ok() {
                                        written += 1;
                                    }
                                }
                                println!("[Dump] Wrote {} facts to {}", written, filepath);
                            }
                            Err(e) => println!("[Dump] Cannot create file: {}", e),
                        }
                    }
                }
                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                Err(e) => {
                    println!("{}", format_host_error(&e));
                    self.needs_rebuild = true;
                }
            }
        } else if let Some(export_arg) = input.strip_prefix(":export ") {
            let filepath = export_arg.trim();
            if filepath.is_empty() {
                println!("[Host] Usage: :export <redb-filepath>");
                return false;
            }
            match self.nibli_store.as_ref() {
                None => {
                    println!("[Export] No persistent store. Set NIBLI_DB_PATH to enable.")
                }
                Some(s) => match s.export_to_file(Path::new(filepath)) {
                    Ok(count) => {
                        println!("[Export] {} facts exported to {}", count, filepath)
                    }
                    Err(e) => println!("[Export] Error: {}", e),
                },
            }
        } else if let Some(verbose_query) = input.strip_prefix(":proof-verbose ") {
            let text = verbose_query.trim();
            if text.is_empty() {
                println!("[Host] Usage: :proof-verbose <lojban query>");
                return false;
            }
            // The full role-level trace (the "under the hood" view); `?` shows
            // the collapsed macro-logical DAG by default.
            self.run_proof_query(text, true);
        } else if let Some(find_text) = input.strip_prefix("??") {
            let text = find_text.trim();
            if text.is_empty() {
                println!("[Host] Usage: ?? <lojban query with ma>");
                return false;
            }
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match session.call_query_find_text(&mut self.store, self.session_handle, text) {
                Ok(Ok(binding_sets)) => {
                    if binding_sets.is_empty() {
                        println!("[Find] No witnesses found.");
                    } else {
                        for bindings in &binding_sets {
                            let parts: Vec<String> = bindings
                                .iter()
                                .map(|b| format!("{} = {}", b.variable, format_term(&b.term)))
                                .collect();
                            println!("[Find] {}", parts.join(", "));
                        }
                    }
                }
                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                Err(e) => {
                    println!("{}", format_host_error(&e));
                    self.needs_rebuild = true;
                }
            }
        } else if let Some(query_text) = input.strip_prefix('?') {
            let text = query_text.trim();
            if text.is_empty() {
                println!("[Host] Usage: ? <lojban query>");
                return false;
            }
            self.run_proof_query(text, false);
        } else {
            self.prepare_session();
            let session = self.pipeline.lojban_nibli_lasna().session();
            match session.call_assert_text(&mut self.store, self.session_handle, input) {
                Ok(Ok(fact_id)) => {
                    persist_text(&mut self.nibli_store, fact_id, input);
                    self.journal.push(JournalEntry::AssertText {
                        text: input.to_string(),
                        id: fact_id,
                    });
                    println!("[Fact #{}] Asserted.", fact_id);
                }
                Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
                Err(e) => {
                    println!("{}", format_host_error(&e));
                    self.needs_rebuild = true;
                }
            }
        }
        false
    }

    /// Run a proof query and print the verdict, the `[Why]` summary, and the
    /// proof. `verbose = false` (the `?` default) prints the collapsed
    /// macro-logical DAG; `verbose = true` (the `:proof-verbose` escape hatch)
    /// prints the full role-level trace.
    fn run_proof_query(&mut self, text: &str, verbose: bool) {
        self.prepare_session();
        let session = self.pipeline.lojban_nibli_lasna().session();
        match session.call_query_text_with_proof(&mut self.store, self.session_handle, text) {
            Ok(Ok((result, trace))) => {
                println!("[Query] {}", format_query_result(&result));
                let proto = trace_to_proto(&trace);
                // Plain-English "why" summary above the proof.
                if let Some(why) =
                    nibli_render::summarize_proof(&proto, nibli_render::Register::Spec)
                {
                    println!("[Why] {why}");
                }
                if verbose {
                    print!(
                        "{}",
                        nibli_render::render_proof_text_indented(
                            &proto,
                            nibli_render::Register::Spec,
                            1
                        )
                    );
                } else {
                    print!(
                        "{}",
                        nibli_render::render_collapsed_text(
                            &proto,
                            nibli_render::Register::Spec,
                            1,
                            false
                        )
                    );
                }
            }
            Ok(Err(e)) => println!("{}", format_nibli_error(&e)),
            Err(e) => {
                // A query that traps on a Wasmtime fuel/memory limit is one of
                // the four-valued outputs: the host translates the trap into a
                // RESOURCE_EXCEEDED(Fuel|Memory) verdict (the engine returns
                // ResourceExceeded only for Depth). A genuine (non-resource)
                // trap stays a [Host Error]. Either way the instance is
                // poisoned, so the session still rebuilds.
                match classify_resource_trap(&e) {
                    Some(kind) => {
                        println!(
                            "[Query] {}",
                            format_query_result(&EngineQueryResult::ResourceExceeded(kind))
                        );
                        println!("  ({})", resource_hint(kind));
                    }
                    None => println!("{}", format_host_error(&e)),
                }
                self.needs_rebuild = true;
            }
        }
    }

    /// Release the session resource. Errors are deliberately ignored: if a
    /// trap poisoned the instance (and no rebuild ran since), entering it to
    /// drop the resource would fail with "cannot remove owned resource".
    fn shutdown(mut self) -> Result<()> {
        let _ = self.session_handle.resource_drop(&mut self.store);
        Ok(())
    }
}

fn main() -> Result<()> {
    println!("==================================================");
    println!(" Lojban Neuro-Symbolic Engine - V4 Typed Pipeline  ");
    println!("==================================================");

    let mut config = Config::new();
    config.wasm_component_model(true);
    config.consume_fuel(true);
    // Note: debug_info(true) triggers a Cranelift assertion failure
    // (value_is_real) on our WASM module — WASM debug symbols not supported.
    let engine = Engine::new(&config)?;

    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker)?;
    compute_backend::add_to_linker::<HostState, HasSelf<HostState>>(
        &mut linker,
        |state: &mut HostState| state,
    )?;

    let backend_addr = std::env::var("NIBLI_COMPUTE_ADDR").ok();
    if let Some(ref addr) = backend_addr {
        println!("Compute backend: {}", addr);
    } else {
        println!("Compute backend: built-in only (set NIBLI_COMPUTE_ADDR=host:port for external)");
    }

    let fuel_budget: u64 = std::env::var("NIBLI_FUEL")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(10_000_000_000);
    println!("Fuel budget: {} per command", fuel_budget);

    let memory_limit_mb: usize = std::env::var("NIBLI_MEMORY_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(512);
    println!("Memory limit: {} MB", memory_limit_mb);

    let wasm_path = std::env::var("NIBLI_WASM_PATH")
        .unwrap_or_else(|_| "target/wasm32-wasip2/debug/lasna.wasm".to_string());
    println!("Loading WebAssembly Component from {}...", wasm_path);
    let component = Component::from_file(&engine, &wasm_path)?;
    let (store, pipeline, session_handle) = Repl::instantiate_session(
        &engine,
        &component,
        &linker,
        fuel_budget,
        memory_limit_mb,
        backend_addr,
    )?;

    // ── Persistent store (optional) ──
    let db_path = std::env::var("NIBLI_DB_PATH").ok();
    let nibli_store: Option<NibliStore> = match &db_path {
        Some(p) => match NibliStore::open(Path::new(p), "gasnu-local".to_string()) {
            Ok(s) => {
                println!("Persistent store: {}", p);
                Some(s)
            }
            Err(e) => {
                println!(
                    "[Store] Failed to open {}: {} (running without persistence)",
                    p, e
                );
                None
            }
        },
        None => None,
    };

    let mut repl = Repl {
        engine,
        component,
        linker,
        store,
        pipeline,
        session_handle,
        fuel_budget,
        memory_limit_mb,
        nibli_store,
        db_path,
        journal: Vec::new(),
        replaying: false,
        needs_rebuild: false,
    };

    // Replay persisted facts into WASM session
    repl.replay_persisted();

    // Mode selection: interactive (reedline) vs. non-interactive script mode.
    // Script mode triggers when --script <file> is passed OR stdin is not a TTY,
    // letting REPL transcripts be captured byte-faithfully via a pipe.
    let script_path: Option<String> = {
        let args: Vec<String> = std::env::args().collect();
        args.windows(2)
            .find(|w| w[0] == "--script")
            .map(|w| w[1].clone())
    };
    let use_script_mode = script_path.is_some() || !std::io::stdin().is_terminal();

    println!(
        "Ready. Commands: :quit :reset :load <file> :facts :retract <id> :debug <text> :compute <name> :assert <rel> <args..> :backend [addr] :fuel [n] :memory [mb] :db :help"
    );
    println!(
        "Prefix '?' for queries with proof trace, '??' for find, plain text for assertions.\n"
    );

    if use_script_mode {
        // Read commands line-by-line from the script file (or piped stdin),
        // echoing `nibli> <input>` then the exact output the interactive path
        // prints. Blank lines and `#` comments are skipped silently.
        let reader: Box<dyn BufRead> = match &script_path {
            Some(p) => match File::open(p) {
                Ok(f) => Box::new(BufReader::new(f)),
                Err(e) => {
                    println!("[Script] Cannot open {}: {}", p, e);
                    return repl.shutdown();
                }
            },
            None => Box::new(BufReader::new(std::io::stdin())),
        };
        for line_result in reader.lines() {
            let line = match line_result {
                Ok(l) => l,
                Err(_) => break,
            };
            let input = line.trim();
            if input.is_empty() || input.starts_with('#') {
                continue;
            }
            println!("nibli> {}", input);
            if repl.dispatch(input) {
                break;
            }
        }
    } else {
        let mut line_editor = Reedline::create();
        let prompt = DefaultPrompt::default();
        loop {
            let sig = line_editor.read_line(&prompt);
            match sig {
                Ok(Signal::Success(buffer)) => {
                    let input = buffer.trim();
                    if input.is_empty() {
                        continue;
                    }
                    if repl.dispatch(input) {
                        break;
                    }
                }
                Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => break,
                Err(err) => {
                    println!("Error: {:?}", err);
                    break;
                }
            }
        }
    }

    repl.shutdown()
}

#[cfg(test)]
mod tests {
    use super::*;
    use compute_backend::Host;
    use std::io::Write;
    use std::net::TcpListener;
    use std::thread;

    /// Start a mock TCP server that sends a fixed response to the first request.
    fn mock_server(response: &str) -> (String, TcpListener) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let resp = response.to_string();
        let listener2 = listener.try_clone().unwrap();
        thread::spawn(move || {
            for stream in listener2.incoming() {
                let stream = stream.unwrap();
                let mut reader = BufReader::new(stream);
                let mut line = String::new();
                // Read request
                if reader.read_line(&mut line).is_ok() && !line.is_empty() {
                    // Send response
                    let mut resp_line = resp.clone();
                    resp_line.push('\n');
                    let _ = reader.get_mut().write_all(resp_line.as_bytes());
                    let _ = reader.get_mut().flush();
                }
            }
        });
        (addr, listener)
    }

    fn make_host(addr: Option<String>) -> HostState {
        let mut backend = BackendClient::new();
        if let Some(a) = &addr {
            backend.set_addr(a);
        }
        HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            limits: StoreLimitsBuilder::new()
                .memory_size(512 * 1024 * 1024)
                .build(),
            backend,
        }
    }

    // Pure-client dispatch tests (success/false/error/no-addr) now live in
    // `nibli_protocol::compute_client::tests`, which owns the shared client.

    #[test]
    fn test_builtin_arithmetic_bypasses_backend() {
        // Even with no backend, built-in arithmetic works
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(6.0),
            compute_backend::LogicalTerm::Number(2.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        // pilji: 6 == 2 * 3
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_arithmetic_float_tolerance() {
        // The host fast path shares the tolerant comparison: 0.1 + 0.2 rounds to
        // 0.30000000000000004, but `0.3 = 0.1 + 0.2` answers TRUE (matching the
        // logji engine and the Python backend).
        let args = vec![
            compute_backend::LogicalTerm::Number(0.3),
            compute_backend::LogicalTerm::Number(0.1),
            compute_backend::LogicalTerm::Number(0.2),
        ];
        assert_eq!(try_builtin_arithmetic("sumji", &args), Some(true));
    }

    #[test]
    fn test_evaluate_falls_through_to_backend() {
        let (addr, _listener) = mock_server(r#"{"result": true}"#);
        let mut host = make_host(Some(addr));

        let args = vec![
            compute_backend::LogicalTerm::Number(8.0),
            compute_backend::LogicalTerm::Number(2.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        // tenfa is NOT built-in, should forward to backend
        assert_eq!(host.evaluate("tenfa".to_string(), args).unwrap(), true);
    }

    // JSON wire-shape serialization is tested in
    // `nibli_protocol::compute_client::tests::json_serialization_shape`.

    // ── format_nibli_error tests ──

    #[test]
    fn test_format_nibli_error_syntax() {
        use pipeline_bind::lojban::nibli::error_types::SyntaxDetail;
        let e = NibliError::Syntax(SyntaxDetail {
            message: "expected selbri or terms".to_string(),
            line: 3,
            column: 7,
        });
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Syntax Error] line 3:7: expected selbri or terms");
    }

    #[test]
    fn test_format_nibli_error_semantic() {
        let e = NibliError::Semantic("go'i has no antecedent".to_string());
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Semantic Error] go'i has no antecedent");
    }

    #[test]
    fn test_format_nibli_error_reasoning() {
        let e = NibliError::Reasoning("assertion failed".to_string());
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Reasoning Error] assertion failed");
    }

    #[test]
    fn test_format_nibli_error_backend() {
        let e = NibliError::Backend(("tenfa".to_string(), "connection refused".to_string()));
        let out = format_nibli_error(&e);
        assert_eq!(out, "[Backend Error] tenfa \u{2014} connection refused");
    }

    // ── evaluate wraps errors as NibliError::Backend ──

    #[test]
    fn test_evaluate_wraps_dispatch_error_as_backend() {
        // No backend configured → the client returns Err(String) ("Unknown
        // compute predicate"); evaluate wraps it as NibliError::Backend.
        let mut host = make_host(None);
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.evaluate("tenfa".to_string(), args);
        match result {
            Err(NibliError::Backend((kind, msg))) => {
                assert_eq!(kind, "tenfa");
                assert!(msg.contains("Unknown compute predicate"));
            }
            other => panic!("expected NibliError::Backend, got {:?}", other),
        }
    }

    #[test]
    fn test_evaluate_backend_error_from_server() {
        let (addr, _listener) = mock_server(r#"{"error": "division by zero"}"#);
        let mut host = make_host(Some(addr));
        let args = vec![compute_backend::LogicalTerm::Number(1.0)];
        let result = host.evaluate("dilcu_ext".to_string(), args);
        match result {
            Err(NibliError::Backend((kind, msg))) => {
                assert_eq!(kind, "dilcu_ext");
                assert!(msg.contains("division by zero"));
            }
            other => panic!("expected NibliError::Backend, got {:?}", other),
        }
    }

    // ── Memory limit tests ──

    #[test]
    fn test_make_host_has_limits() {
        // HostState should contain StoreLimits
        let _host = make_host(None);
        // If it compiles and runs, the limits field is present
    }

    #[test]
    fn test_format_host_error_memory() {
        let e = anyhow::anyhow!("memory allocation limit exceeded");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("Memory limit"));
        assert!(out.contains("NIBLI_MEMORY_MB"));
        assert!(out.contains(":memory"));
    }

    #[test]
    fn test_format_host_error_memory_uppercase() {
        let e = anyhow::anyhow!("Memory allocation failed");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("Memory limit"));
    }

    #[test]
    fn test_format_host_error_fuel_unchanged() {
        let e = anyhow::anyhow!("all fuel consumed");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
        assert!(out.contains("fuel"));
        assert!(out.contains("NIBLI_FUEL"));
    }

    #[test]
    fn test_format_host_error_other_unchanged() {
        let e = anyhow::anyhow!("something else broke");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Host Error]"));
    }

    #[test]
    fn test_format_host_error_real_fuel_trap_chain() {
        // The real shape of a fuel trap: Display is the wasm-backtrace context
        // line (contains neither "fuel" nor "memory"); the typed Trap is the
        // root cause. The old top-line substring match misclassified this as
        // [Host Error].
        let e = anyhow::Error::from(wasmtime::Trap::OutOfFuel)
            .context("error while executing at wasm backtrace: ...");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"), "got: {out}");
        assert!(out.contains("fuel"));
        assert!(out.contains("NIBLI_FUEL"));
    }

    #[test]
    fn test_format_host_error_memory_grow_denial_chain() {
        // StoreLimits with trap_on_grow_failure(true) denies growth with this
        // message as the CAUSE under a backtrace context line.
        let e = anyhow::anyhow!("forcing trap when growing memory to 1073741824 bytes")
            .context("error while executing at wasm backtrace: ...");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"), "got: {out}");
        assert!(out.contains("Memory limit"));
        assert!(out.contains("NIBLI_MEMORY_MB"));
    }

    #[test]
    fn test_format_host_error_cannot_enter_is_host_error() {
        // The post-trap re-entry error must NOT classify as a resource limit.
        let e = anyhow::anyhow!("wasm trap: cannot enter component instance");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Host Error]"), "got: {out}");
    }

    // ── classify_resource_trap + query-verdict formatting ──
    //
    // The non-query path (`format_host_error`, above) renders a trap as a `[Limit]`
    // line; a `?` query instead translates the SAME trap into a four-valued
    // RESOURCE_EXCEEDED verdict. These pin both halves deterministically — the
    // classification of a real grow-denial / fuel chain, and the verdict rendering
    // — so the Memory path is gated in CI without a (build-fragile) live grow-trap.

    #[test]
    fn test_classify_resource_trap_memory_grow_denial() {
        // StoreLimits with trap_on_grow_failure(true) denies growth with this
        // message as the CAUSE under a backtrace context line.
        let e = anyhow::anyhow!("forcing trap when growing memory to 1073741824 bytes")
            .context("error while executing at wasm backtrace: ...");
        assert!(matches!(
            classify_resource_trap(&e),
            Some(EngineResourceKind::Memory)
        ));
    }

    #[test]
    fn test_classify_resource_trap_fuel_typed() {
        // The real shape of a fuel trap: the typed Trap::OutOfFuel is the root cause.
        let e = anyhow::Error::from(wasmtime::Trap::OutOfFuel)
            .context("error while executing at wasm backtrace: ...");
        assert!(matches!(
            classify_resource_trap(&e),
            Some(EngineResourceKind::Fuel)
        ));
    }

    #[test]
    fn test_classify_resource_trap_other_is_none() {
        // A genuine non-resource trap (post-trap re-entry) is not a resource limit.
        let e = anyhow::anyhow!("wasm trap: cannot enter component instance");
        assert!(classify_resource_trap(&e).is_none());
    }

    #[test]
    fn test_format_query_result_resource_exceeded_kinds() {
        // A query that traps on a host limit becomes one of the four-valued
        // outputs; each kind renders with its lowercase tag.
        assert_eq!(
            format_query_result(&EngineQueryResult::ResourceExceeded(
                EngineResourceKind::Memory
            )),
            "RESOURCE_EXCEEDED (memory)"
        );
        assert_eq!(
            format_query_result(&EngineQueryResult::ResourceExceeded(
                EngineResourceKind::Fuel
            )),
            "RESOURCE_EXCEEDED (fuel)"
        );
        assert_eq!(
            format_query_result(&EngineQueryResult::ResourceExceeded(
                EngineResourceKind::Depth
            )),
            "RESOURCE_EXCEEDED (depth)"
        );
    }

    #[test]
    fn test_format_query_result_backend_unavailable() {
        // An unreachable/unregistered compute backend surfaces as a distinct
        // UNKNOWN reason — never FALSE — so the operator can tell "the oracle is
        // down" from "the math is false".
        assert_eq!(
            format_query_result(&EngineQueryResult::Unknown(
                EngineUnknownReason::BackendUnavailable
            )),
            "UNKNOWN (backend-unavailable)"
        );
    }

    #[test]
    fn test_store_limits_builder_creates_valid_limits() {
        // Verify StoreLimitsBuilder API works as expected
        let limits = StoreLimitsBuilder::new()
            .memory_size(256 * 1024 * 1024)
            .build();
        // Assign into a HostState — if it compiles, the types are correct
        let _host = HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            limits,
            backend: BackendClient::new(),
        };
    }

    #[test]
    fn test_store_limiter_integration() {
        // Verify Store::limiter works with our HostState
        let mut config = Config::new();
        config.wasm_component_model(true);
        config.consume_fuel(true);
        let engine = Engine::new(&config).unwrap();

        let state = HostState {
            ctx: WasiCtxBuilder::new().build(),
            table: ResourceTable::new(),
            limits: StoreLimitsBuilder::new()
                .memory_size(64 * 1024 * 1024)
                .build(),
            backend: BackendClient::new(),
        };
        let mut store = Store::new(&engine, state);
        store.set_fuel(1_000_000).unwrap();
        store.limiter(|state| &mut state.limits);
        // Store is set up with both fuel and memory limits — if no panic, success
    }

    #[test]
    fn test_parse_assert_args_basic() {
        let (rel, args) = parse_assert_args("gerku alis").unwrap();
        assert_eq!(rel, "gerku");
        assert_eq!(args.len(), 1);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_number() {
        let (rel, args) = parse_assert_args("pilji 6 2 3").unwrap();
        assert_eq!(rel, "pilji");
        assert_eq!(args.len(), 3);
        match &args[0] {
            EngineLogicalTerm::Number(n) => assert_eq!(*n, 6.0),
            other => panic!("expected Number, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_empty() {
        assert!(parse_assert_args("").is_err());
    }

    // Reconnect-after-drop is exercised by the shared client's retry-once path
    // (`nibli_protocol::compute_client`).

    // ─── Built-in arithmetic edge cases ──────────────────────────

    #[test]
    fn test_builtin_pilji_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_pilji_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(13.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("pilji".to_string(), args).unwrap(), false);
    }

    #[test]
    fn test_builtin_sumji_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(7.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("sumji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_sumji_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(8.0),
            compute_backend::LogicalTerm::Number(3.0),
            compute_backend::LogicalTerm::Number(4.0),
        ];
        assert_eq!(host.evaluate("sumji".to_string(), args).unwrap(), false);
    }

    #[test]
    fn test_builtin_dilcu_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(4.0),
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        assert_eq!(host.evaluate("dilcu".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_dilcu_incorrect() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(5.0),
            compute_backend::LogicalTerm::Number(12.0),
            compute_backend::LogicalTerm::Number(3.0),
        ];
        assert_eq!(host.evaluate("dilcu".to_string(), args).unwrap(), false);
    }

    #[test]
    fn test_builtin_sumji_fractional_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(2.5),
            compute_backend::LogicalTerm::Number(1.0),
            compute_backend::LogicalTerm::Number(1.5),
        ];
        assert_eq!(host.evaluate("sumji".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_builtin_dilcu_fractional_correct() {
        let mut host = make_host(None);
        let args = vec![
            compute_backend::LogicalTerm::Number(2.5),
            compute_backend::LogicalTerm::Number(5.0),
            compute_backend::LogicalTerm::Number(2.0),
        ];
        assert_eq!(host.evaluate("dilcu".to_string(), args).unwrap(), true);
    }

    #[test]
    fn test_evaluate_batch_keeps_fractional_builtin_arithmetic_local() {
        let mut host = make_host(None);
        let requests = vec![
            compute_backend::ComputeRequest {
                relation: "sumji".to_string(),
                args: vec![
                    compute_backend::LogicalTerm::Number(2.5),
                    compute_backend::LogicalTerm::Number(1.0),
                    compute_backend::LogicalTerm::Number(1.5),
                ],
            },
            compute_backend::ComputeRequest {
                relation: "dilcu".to_string(),
                args: vec![
                    compute_backend::LogicalTerm::Number(2.5),
                    compute_backend::LogicalTerm::Number(5.0),
                    compute_backend::LogicalTerm::Number(2.0),
                ],
            },
        ];

        let results = host.evaluate_batch(requests);
        assert_eq!(results.len(), 2);
        assert!(matches!(
            results[0],
            compute_backend::ComputeResult::Ok(true)
        ));
        assert!(matches!(
            results[1],
            compute_backend::ComputeResult::Ok(true)
        ));
    }

    // ─── parse_assert_args edge cases ────────────────────────────

    #[test]
    fn test_parse_assert_args_multiple_constants() {
        let (rel, args) = parse_assert_args("nelci alis bob").unwrap();
        assert_eq!(rel, "nelci");
        assert_eq!(args.len(), 2);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
        match &args[1] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "bob"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_assert_args_mixed_number_and_constant() {
        let (rel, args) = parse_assert_args("pilji 6 alis 3").unwrap();
        assert_eq!(rel, "pilji");
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[0], EngineLogicalTerm::Number(n) if *n == 6.0));
        assert!(matches!(&args[1], EngineLogicalTerm::Constant(s) if s == "alis"));
        assert!(matches!(&args[2], EngineLogicalTerm::Number(n) if *n == 3.0));
    }

    #[test]
    fn test_parse_assert_args_relation_only_no_args() {
        // Just the relation name with no arguments — should this be valid?
        // It depends on implementation. Let's verify it doesn't panic.
        let result = parse_assert_args("gerku");
        // Relation without args — may error or return empty args
        if let Ok((rel, args)) = result {
            assert_eq!(rel, "gerku");
            assert!(args.is_empty());
        }
    }

    #[test]
    fn test_parse_assert_args_whitespace_handling() {
        let (rel, args) = parse_assert_args("  gerku   alis  ").unwrap();
        assert_eq!(rel, "gerku");
        assert_eq!(args.len(), 1);
        match &args[0] {
            EngineLogicalTerm::Constant(s) => assert_eq!(s, "alis"),
            other => panic!("expected Constant, got {:?}", other),
        }
    }

    // JSON response deserialization is tested in the shared client
    // (`nibli_protocol::compute_client::tests`).

    // ─── format_nibli_error comprehensive tests ──────────────────

    #[test]
    fn test_format_nibli_error_syntax_with_position() {
        use pipeline_bind::lojban::nibli::error_types::SyntaxDetail;
        let e = NibliError::Syntax(SyntaxDetail {
            message: "unexpected token".to_string(),
            line: 1,
            column: 15,
        });
        let out = format_nibli_error(&e);
        assert!(out.contains("[Syntax Error]"));
        assert!(out.contains("1:15"));
        assert!(out.contains("unexpected token"));
    }

    // ─── format_host_error edge cases ────────────────────────────

    #[test]
    fn test_format_host_error_generic_error() {
        let e = anyhow::anyhow!("unknown wasm trap");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Host Error]"));
        assert!(out.contains("unknown wasm trap"));
    }

    #[test]
    fn test_format_host_error_fuel_case_insensitive() {
        // "fuel" match should be case insensitive or at least match lower case
        let e = anyhow::anyhow!("all fuel consumed by execution");
        let out = format_host_error(&e);
        assert!(out.starts_with("[Limit]"));
    }

    // Dispatch over the various LogicalTerm arg kinds (constant/variable/
    // description/unspecified) is covered by the shared client's wire-shape +
    // dispatch tests and gasnu's `term_to_arg` (exercised via `evaluate`).
}
