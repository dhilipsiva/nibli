//! nibli-pipeline (fasten/orchestrator) WASM component: chains nibli-kr → nibli-semantics → nibli-reason.
//!
//! Single WASM component that calls nibli-kr/nibli-semantics/nibli-reason as internal Rust crate
//! dependencies. Provides a high-level [`Session`] resource via the `nibli-pipeline` WIT
//! export interface.

#[allow(warnings)]
mod bindings;

// The component's own WIT export types. Since the `[package.metadata.component.bindings]`
// `with`-remap (Cargo.toml), the ABI-matching boundary types ARE `nibli_types`
// directly — the generated `logic_types`/`error_types` modules now retain only
// the types that could NOT be remapped: `proof-rule`/`proof-step`/`proof-trace`
// (proof-rule is named-field in Rust but wit-bindgen emits only tuple/newtype
// variants). Those three keep the hand `convert_proof_*` bridge below.
use bindings::exports::nibli::engine::engine::{Guest, GuestSession};
use bindings::nibli::engine::compute_backend as cb;
use bindings::nibli::engine::logic_types as export_logic;

// Canonical pipeline types (shared across nibli-kr/nibli-semantics/nibli-reason).
// These are ALSO the WIT boundary types now (via the `with`-remap), so most of
// the former converter glue is gone — the boundary speaks `nibli_types`.
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

// ─── The one surviving type bridge: proof-rule / proof-trace ───
//
// `proof-rule` is the sole boundary type NOT `with`-remapped onto `nibli_types`
// (Cargo.toml): the canonical `logic::ProofRule` is named-field, but wit-bindgen
// can only emit tuple/newtype variants, so the generated `export_logic::ProofRule`
// stays tuple-shaped and needs a hand map. `proof-step`/`proof-trace` reference
// it, so they stay generated too. Embedded terms are ALREADY `logic::LogicalTerm`
// on both sides (logical-term IS remapped), so no term conversion is needed.

fn convert_proof_rule(r: &logic::ProofRule) -> export_logic::ProofRule {
    use export_logic as e;
    match r {
        logic::ProofRule::Conjunction => e::ProofRule::Conjunction,
        logic::ProofRule::DisjunctionCheck { detail } => {
            e::ProofRule::DisjunctionCheck(e::DisjunctionCheckRule {
                detail: detail.clone(),
            })
        }
        logic::ProofRule::DisjunctionIntro { side } => {
            e::ProofRule::DisjunctionIntro(e::DisjunctionIntroRule { side: side.clone() })
        }
        logic::ProofRule::Negation => e::ProofRule::Negation,
        logic::ProofRule::ModalPassthrough { kind } => {
            e::ProofRule::ModalPassthrough(e::ModalPassthroughRule { kind: kind.clone() })
        }
        logic::ProofRule::ExistsWitness { var, term } => {
            e::ProofRule::ExistsWitness(e::ExistsWitnessRule {
                var: var.clone(),
                term: term.clone(),
            })
        }
        logic::ProofRule::ExistsFailed => e::ProofRule::ExistsFailed,
        logic::ProofRule::ForallVacuous => e::ProofRule::ForallVacuous,
        logic::ProofRule::ForallVerified { entities } => {
            e::ProofRule::ForallVerified(e::ForallVerifiedRule {
                entities: entities.clone(),
            })
        }
        logic::ProofRule::ForallCounterexample { entity } => {
            e::ProofRule::ForallCounterexample(e::ForallCounterexampleRule {
                entity: entity.clone(),
            })
        }
        logic::ProofRule::CountResult { expected, actual } => {
            e::ProofRule::CountResult(e::CountResultRule {
                expected: *expected,
                actual: *actual,
            })
        }
        logic::ProofRule::PredicateCheck { method, detail } => {
            e::ProofRule::PredicateCheck(e::PredicateCheckRule {
                method: method.clone(),
                detail: detail.clone(),
            })
        }
        logic::ProofRule::ComputeCheck { method, detail } => {
            e::ProofRule::ComputeCheck(e::ComputeCheckRule {
                method: method.clone(),
                detail: detail.clone(),
            })
        }
        logic::ProofRule::Asserted { fact } => {
            e::ProofRule::Asserted(e::AssertedRule { fact: fact.clone() })
        }
        logic::ProofRule::Derived { label, fact } => e::ProofRule::Derived(e::DerivedRule {
            label: label.clone(),
            fact: fact.clone(),
        }),
        logic::ProofRule::ProofRef { fact } => {
            e::ProofRule::ProofRef(e::ProofRefRule { fact: fact.clone() })
        }
        logic::ProofRule::EqualitySubstitution {
            original,
            equality_facts,
            substituted,
        } => e::ProofRule::EqualitySubstitution(e::EqualitySubstitutionRule {
            original: original.clone(),
            equality_facts: equality_facts.clone(),
            substituted: substituted.clone(),
        }),
        logic::ProofRule::RuleAttemptFailed {
            rule_label,
            failed_condition,
        } => e::ProofRule::RuleAttemptFailed(e::RuleAttemptFailedRule {
            rule_label: rule_label.clone(),
            failed_condition: failed_condition.clone(),
        }),
        logic::ProofRule::PredicateNotFound { predicate } => {
            e::ProofRule::PredicateNotFound(e::PredicateNotFoundRule {
                predicate: predicate.clone(),
            })
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

// ─── Compute dispatch bridge (nibli-reason → nibli-pipeline WIT import) ───
// The compute-backend import speaks `logical-term`, which IS remapped, so the
// args pass straight through — no term conversion.

fn eval_via_host(rel: &str, args: &[logic::LogicalTerm]) -> Result<bool, String> {
    cb::evaluate(rel, args).map_err(|e| match e {
        pipeline_err::NibliError::Backend((_, m)) => m,
        other => format!("{:?}", other),
    })
}

fn batch_eval_via_host(requests: &[nibli_reason::ComputeRequest]) -> Vec<Result<bool, String>> {
    let wit_requests: Vec<cb::ComputeRequest> = requests
        .iter()
        .map(|r| cb::ComputeRequest {
            relation: r.relation.clone(),
            args: r.args.clone(),
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
    /// Emit the KR lint notes for an interactive text input (NIBLI_KR
    /// §12 L1–L9) to guest stdout as `[Note: …]` lines — the `[Skolem]`/`[Rule]`
    /// echo precedent: verbose-gated (NIBLI_QUIET suppresses), non-blocking
    /// (never affects the compile result). Buffer replay
    /// (`assert_buffer_with_id`) is mechanical, not authoring, so it never lints.
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
    /// event-decomposed to the surface shape, caller-chosen id for replay). The
    /// args and error ARE the canonical `nibli_types` types now (the boundary
    /// is `with`-remapped), so nothing is converted here.
    fn assert_fact_inner(
        &self,
        relation: String,
        args: Vec<logic::LogicalTerm>,
        id: Option<u64>,
    ) -> Result<u64, pipeline_err::NibliError> {
        self.core.borrow().assert_fact_direct(&relation, &args, id)
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
        // EXISTENTIAL IMPORT defaults ON (the v0.1 xorlo behavior). The host
        // forwards `NIBLI_EXISTENTIAL_IMPORT=0` into the WASI env to opt into
        // clean-core (`some` = plain ∃); the `:existential-import` REPL toggle
        // re-applies via `set-existential-import` after any post-trap rebuild.
        if std::env::var("NIBLI_EXISTENTIAL_IMPORT").ok().as_deref() == Some("0") {
            core.set_existential_import(false);
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

    fn set_existential_import(&self, enabled: bool) {
        self.core.borrow().set_existential_import(enabled);
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
    ) -> Result<Vec<(u64, logic::LogicBuffer)>, pipeline_err::NibliError> {
        self.emit_lints(&input);
        // The per-root (id, buffer) pairs ARE `(u64, logic::LogicBuffer)` — the
        // WIT return type now — so they pass straight through.
        self.core.borrow().assert_text(&input)
    }

    /// Recompile-free replay: assert an already-compiled buffer (as returned
    /// by `assert-text`) under a caller-chosen id.
    fn assert_buffer_with_id(
        &self,
        buffer: logic::LogicBuffer,
        label: String,
        id: u64,
    ) -> Result<(), pipeline_err::NibliError> {
        self.core
            .borrow()
            .kb()
            .assert_fact_with_id(buffer, label, id)
            .map_err(pipeline_err::NibliError::Reasoning)
    }

    fn query_text(&self, input: String) -> Result<logic::QueryResult, pipeline_err::NibliError> {
        self.emit_lints(&input);
        self.core.borrow().query_text(&input)
    }

    fn query_find_text(
        &self,
        input: String,
    ) -> Result<Vec<Vec<logic::WitnessBinding>>, pipeline_err::NibliError> {
        self.emit_lints(&input);
        self.core.borrow().query_find_text(&input)
    }

    fn query_text_with_proof(
        &self,
        input: String,
    ) -> Result<(logic::QueryResult, export_logic::ProofTrace), pipeline_err::NibliError> {
        self.emit_lints(&input);
        // query-result IS remapped; proof-trace is NOT (it embeds proof-rule),
        // so only the trace is bridged.
        let (result, trace) = self.core.borrow().query_text_with_proof(&input)?;
        Ok((result, convert_proof_trace(trace)))
    }

    fn compile_debug(&self, input: String) -> Result<logic::LogicBuffer, pipeline_err::NibliError> {
        self.core.borrow().compile_text(&input)
    }

    fn reset_kb(&self) -> Result<(), pipeline_err::NibliError> {
        self.linter.borrow_mut().reset();
        self.core.borrow().reset()
    }

    fn register_compute_predicate(&self, name: String) {
        self.core.borrow_mut().register_compute_predicate(name);
    }

    fn assert_fact(
        &self,
        relation: String,
        args: Vec<logic::LogicalTerm>,
    ) -> Result<u64, pipeline_err::NibliError> {
        self.assert_fact_inner(relation, args, None)
    }

    fn assert_fact_with_id(
        &self,
        relation: String,
        args: Vec<logic::LogicalTerm>,
        id: u64,
    ) -> Result<(), pipeline_err::NibliError> {
        self.assert_fact_inner(relation, args, Some(id)).map(|_| ())
    }

    fn retract_fact(&self, id: u64) -> Result<(), pipeline_err::NibliError> {
        self.core.borrow().retract_fact(id)
    }

    fn list_facts(&self) -> Result<Vec<logic::FactSummary>, pipeline_err::NibliError> {
        self.core.borrow().list_facts()
    }
}

bindings::export!(NibliPipeline with_types_in bindings);
