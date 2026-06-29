//! Lasna (fasten/orchestrator) WASM component: chains gerna → smuni → logji.
//!
//! Single WASM component that calls gerna/smuni/logji as internal Rust crate
//! dependencies. Provides a high-level [`Session`] resource via the `lasna` WIT
//! export interface.

#[allow(warnings)]
mod bindings;

// Lasna's own WIT export types (the boundary we serialize through)
use bindings::exports::lojban::nibli::lasna::{Guest, GuestSession};
use bindings::lojban::nibli::compute_backend as cb;
use bindings::lojban::nibli::error_types as export_err;
use bindings::lojban::nibli::logic_types as export_logic;

// Canonical pipeline types (shared across gerna/smuni/logji)
use nibli_types::ast as gerna_ast;
use nibli_types::error as pipeline_err;
use nibli_types::logic as logji_logic;

// `go'i` resolution now lives in the shared `gerna::goi` module (also used by
// nibli-engine), so native and WASM resolve the pro-bridi identically.
use gerna::goi::{BridiSnapshot, extract_bridi_snapshot, resolve_go_i_with_arity};

use std::cell::RefCell;
use std::collections::HashSet;

/// WIT component implementation for the `lasna` interface.
struct LasnaPipeline;

/// A user-facing session wrapping the full gerna → smuni → logji pipeline.
pub struct Session {
    kb: logji::KnowledgeBase,
    compute_predicates: RefCell<HashSet<String>>,
    last_relation: RefCell<Option<BridiSnapshot>>,
}

// ─── Type conversion: logji → lasna export boundary ───

fn convert_logical_term_to_export(t: &logji_logic::LogicalTerm) -> export_logic::LogicalTerm {
    match t {
        logji_logic::LogicalTerm::Variable(v) => export_logic::LogicalTerm::Variable(v.clone()),
        logji_logic::LogicalTerm::Constant(c) => export_logic::LogicalTerm::Constant(c.clone()),
        logji_logic::LogicalTerm::Description(d) => {
            export_logic::LogicalTerm::Description(d.clone())
        }
        logji_logic::LogicalTerm::Number(n) => export_logic::LogicalTerm::Number(*n),
        logji_logic::LogicalTerm::Unspecified => export_logic::LogicalTerm::Unspecified,
    }
}

/// Convert one logji `LogicNode` to the WIT export node (pure 1:1 — the WIT
/// `logic-node` variant mirrors `nibli_types::logic::LogicNode` exactly).
fn convert_logic_node_to_export(n: &logji_logic::LogicNode) -> export_logic::LogicNode {
    use export_logic::LogicNode as E;
    use logji_logic::LogicNode as L;
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

/// Convert the full logji `LogicBuffer` to the WIT export buffer (typed IR
/// crosses the boundary; the host renders it — no S-expression string).
fn convert_logic_buffer_to_export(buf: &logji_logic::LogicBuffer) -> export_logic::LogicBuffer {
    export_logic::LogicBuffer {
        nodes: buf.nodes.iter().map(convert_logic_node_to_export).collect(),
        roots: buf.roots.clone(),
    }
}

fn convert_logical_term_from_export(t: &export_logic::LogicalTerm) -> logji_logic::LogicalTerm {
    match t {
        export_logic::LogicalTerm::Variable(v) => logji_logic::LogicalTerm::Variable(v.clone()),
        export_logic::LogicalTerm::Constant(c) => logji_logic::LogicalTerm::Constant(c.clone()),
        export_logic::LogicalTerm::Description(d) => {
            logji_logic::LogicalTerm::Description(d.clone())
        }
        export_logic::LogicalTerm::Number(n) => logji_logic::LogicalTerm::Number(*n),
        export_logic::LogicalTerm::Unspecified => logji_logic::LogicalTerm::Unspecified,
    }
}

fn convert_query_result_to_export(result: &logji_logic::QueryResult) -> export_logic::QueryResult {
    match result {
        logji_logic::QueryResult::True => export_logic::QueryResult::True,
        logji_logic::QueryResult::False => export_logic::QueryResult::False,
        logji_logic::QueryResult::Unknown(logji_logic::UnknownReason::CycleCut) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::CycleCut)
        }
        logji_logic::QueryResult::Unknown(logji_logic::UnknownReason::IncompleteKnowledge) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::IncompleteKnowledge)
        }
        logji_logic::QueryResult::Unknown(logji_logic::UnknownReason::NafDependent) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::NafDependent)
        }
        logji_logic::QueryResult::Unknown(logji_logic::UnknownReason::BackendUnavailable) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::BackendUnavailable)
        }
        logji_logic::QueryResult::Unknown(logji_logic::UnknownReason::NonFinite) => {
            export_logic::QueryResult::Unknown(export_logic::UnknownReason::NonFinite)
        }
        logji_logic::QueryResult::ResourceExceeded(logji_logic::ResourceKind::Depth) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Depth)
        }
        logji_logic::QueryResult::ResourceExceeded(logji_logic::ResourceKind::Fuel) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Fuel)
        }
        logji_logic::QueryResult::ResourceExceeded(logji_logic::ResourceKind::Memory) => {
            export_logic::QueryResult::ResourceExceeded(export_logic::ResourceKind::Memory)
        }
    }
}

// logji's `ProofRule` is now the named-field canonical type; the WIT export type
// stays tuple-shaped (generated from world.wit), so this maps named fields → tuples.
fn convert_proof_rule(r: &logji_logic::ProofRule) -> export_logic::ProofRule {
    match r {
        logji_logic::ProofRule::Conjunction => export_logic::ProofRule::Conjunction,
        logji_logic::ProofRule::DisjunctionCheck { detail } => {
            export_logic::ProofRule::DisjunctionCheck(detail.clone())
        }
        logji_logic::ProofRule::DisjunctionIntro { side } => {
            export_logic::ProofRule::DisjunctionIntro(side.clone())
        }
        logji_logic::ProofRule::Negation => export_logic::ProofRule::Negation,
        logji_logic::ProofRule::ModalPassthrough { kind } => {
            export_logic::ProofRule::ModalPassthrough(kind.clone())
        }
        logji_logic::ProofRule::ExistsWitness { var, term } => {
            export_logic::ProofRule::ExistsWitness((
                var.clone(),
                convert_logical_term_to_export(term),
            ))
        }
        logji_logic::ProofRule::ExistsFailed => export_logic::ProofRule::ExistsFailed,
        logji_logic::ProofRule::ForallVacuous => export_logic::ProofRule::ForallVacuous,
        logji_logic::ProofRule::ForallVerified { entities } => {
            export_logic::ProofRule::ForallVerified(
                entities
                    .iter()
                    .map(convert_logical_term_to_export)
                    .collect(),
            )
        }
        logji_logic::ProofRule::ForallCounterexample { entity } => {
            export_logic::ProofRule::ForallCounterexample(convert_logical_term_to_export(entity))
        }
        logji_logic::ProofRule::CountResult { expected, actual } => {
            export_logic::ProofRule::CountResult((*expected, *actual))
        }
        logji_logic::ProofRule::PredicateCheck { method, detail } => {
            export_logic::ProofRule::PredicateCheck((method.clone(), detail.clone()))
        }
        logji_logic::ProofRule::ComputeCheck { method, detail } => {
            export_logic::ProofRule::ComputeCheck((method.clone(), detail.clone()))
        }
        logji_logic::ProofRule::Asserted { fact } => {
            export_logic::ProofRule::Asserted(fact.clone())
        }
        logji_logic::ProofRule::Derived { label, fact } => {
            export_logic::ProofRule::Derived((label.clone(), fact.clone()))
        }
        logji_logic::ProofRule::ProofRef { fact } => {
            export_logic::ProofRule::ProofRef(fact.clone())
        }
        logji_logic::ProofRule::EqualitySubstitution {
            original,
            du_facts,
            substituted,
        } => export_logic::ProofRule::EqualitySubstitution((
            original.clone(),
            du_facts.clone(),
            substituted.clone(),
        )),
        logji_logic::ProofRule::RuleAttemptFailed {
            rule_label,
            failed_condition,
        } => export_logic::ProofRule::RuleAttemptFailed((
            rule_label.clone(),
            failed_condition.clone(),
        )),
        logji_logic::ProofRule::PredicateNotFound { predicate } => {
            export_logic::ProofRule::PredicateNotFound(predicate.clone())
        }
    }
}

fn convert_proof_trace(t: logji_logic::ProofTrace) -> export_logic::ProofTrace {
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
        // logji's ProofTrace::has_naf_dependency).
        naf_dependent: t.has_naf_dependency(),
        // The dual CWA-FALSE flag needs the verdict (not recomputable from steps),
        // so it is read from the field logji already populated.
        cwa_false: t.cwa_false,
    }
}

fn convert_witness_bindings(
    wbs: Vec<Vec<logji_logic::WitnessBinding>>,
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

fn convert_fact_summaries(fs: Vec<logji_logic::FactSummary>) -> Vec<export_logic::FactSummary> {
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

// ─── Compute dispatch bridge (logji → lasna WIT import) ───

fn eval_via_host(rel: &str, args: &[logji_logic::LogicalTerm]) -> Result<bool, String> {
    let converted: Vec<export_logic::LogicalTerm> =
        args.iter().map(convert_logical_term_to_export).collect();
    cb::evaluate(rel, &converted).map_err(|e| match e {
        export_err::NibliError::Backend((_, m)) => m,
        other => format!("{:?}", other),
    })
}

fn batch_eval_via_host(requests: &[logji::ComputeRequest]) -> Vec<Result<bool, String>> {
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

// ─── go'i pro-bridi resolution ───

/// Synthesize positional `Sumti` nodes (and their head-term ids) from direct-API
/// `assert-fact` args for the go'i snapshot. `Constant`→`Name`, `Number`→`Number`
/// (both round-trip through smuni to the same shape `compile_injected_fact`
/// stored); `Description`/`Variable`/`Unspecified`→`Unspecified` (place-preserving
/// `zo'e` — a faithful node would need a selbri id / `da`-`de`-`di` we lack here).
fn synth_snapshot_terms(args: &[export_logic::LogicalTerm]) -> (Vec<gerna_ast::Sumti>, Vec<u32>) {
    let mut sumtis = Vec::with_capacity(args.len());
    let mut head_terms = Vec::with_capacity(args.len());
    for a in args {
        let id = sumtis.len() as u32;
        sumtis.push(match a {
            export_logic::LogicalTerm::Constant(c) => gerna_ast::Sumti::Name(c.clone()),
            export_logic::LogicalTerm::Number(n) => gerna_ast::Sumti::Number(*n),
            export_logic::LogicalTerm::Description(_)
            | export_logic::LogicalTerm::Variable(_)
            | export_logic::LogicalTerm::Unspecified => gerna_ast::Sumti::Unspecified,
        });
        head_terms.push(id);
    }
    (sumtis, head_terms)
}

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(
    text: &str,
    last_snapshot: &mut Option<BridiSnapshot>,
    compute_predicates: &HashSet<String>,
) -> Result<(logji_logic::LogicBuffer, Option<BridiSnapshot>), export_err::NibliError> {
    // Shared parse front-end (fail-closed on any parse error — assert AND query),
    // then the lasna-specific go'i resolution, then smuni compile + compute-node
    // marking.
    let mut ast = gerna::parse_checked(text).map_err(convert_pipeline_error)?;

    // Bound a partial go'i's FA places by the relation's arity (smuni's dictionary),
    // so a beyond-arity tag fails closed instead of being silently dropped post-merge.
    let last_bridi_sid = resolve_go_i_with_arity(&mut ast, last_snapshot, &|n| {
        smuni::dictionary::JbovlasteSchema::get_arity(n)
    })
    .map_err(export_err::NibliError::Semantic)?;
    let new_snapshot = last_bridi_sid.map(|sid| extract_bridi_snapshot(&ast, sid));

    let mut buf = smuni::compile_from_gerna_ast(ast).map_err(convert_pipeline_error)?;
    logji::transform_compute_nodes(&mut buf, compute_predicates);

    Ok((buf, new_snapshot))
}

// ─── WIT exports ───

impl Guest for LasnaPipeline {
    type Session = Session;
}

impl Session {
    /// Shared body for `assert_text` / `assert_text_with_id`. When `id` is
    /// `Some`, the fact is asserted with that CALLER-CHOSEN id (persistent
    /// restart-replay keeps the live KB's fact-id namespace equal to the durable
    /// store's); when `None`, the KB mints a fresh id. The `last_relation` go'i
    /// snapshot update applies on BOTH paths. (`compile_pipeline` fails closed on
    /// any parse error, so no per-caller warning check is needed.)
    fn assert_text_inner(
        &self,
        input: String,
        id: Option<u64>,
    ) -> Result<u64, export_err::NibliError> {
        let (buf, new_last) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        let fact_id = match id {
            Some(i) => {
                self.kb
                    .assert_fact_with_id(buf, input, i)
                    // The assert is the reasoning stage (buffer already past smuni);
                    // logji's `assert_fact_with_id` returns a String, so wrap as Reasoning.
                    .map_err(export_err::NibliError::Reasoning)?;
                i
            }
            None => self
                .kb
                .assert_fact(buf, input)
                .map_err(convert_pipeline_error)?,
        };
        *self.last_relation.borrow_mut() = new_last;
        Ok(fact_id)
    }

    /// Shared body for `assert_fact` / `assert_fact_with_id` (see
    /// `assert_text_inner` for the `id` semantics).
    fn assert_fact_inner(
        &self,
        relation: String,
        args: Vec<export_logic::LogicalTerm>,
        id: Option<u64>,
    ) -> Result<u64, export_err::NibliError> {
        // Sentence-rooted snapshot carrying the args as positional sumti, so a
        // following bare `? go'i` reproduces `relation(a, b, …)`. Ground
        // `Constant`/`Number` args round-trip; `Description`/`Variable` degrade to
        // a place-preserving `zo'e` (no selbri id / da-de-di binding available
        // here) — never a wrong constant. See `synth_snapshot_terms`.
        let (sumtis, head_terms) = synth_snapshot_terms(&args);
        *self.last_relation.borrow_mut() = Some(BridiSnapshot {
            selbris: vec![gerna_ast::Selbri::Root(relation.clone())],
            sumtis,
            sentences: vec![gerna_ast::Sentence::Simple(gerna_ast::Bridi {
                relation: 0,
                head_terms,
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            root: 0,
        });
        let logji_args: Vec<logji_logic::LogicalTerm> =
            args.iter().map(convert_logical_term_from_export).collect();
        let label = format!(":assert {}", relation);
        // Event-decompose to the SAME shape a surface assertion produces, so the
        // injected fact is matched by surface text queries (not just raw-FOL /
        // same-shape direct queries). `du` stays flat — see compile_injected_fact.
        let buf = smuni::compile_injected_fact(&relation, &logji_args);
        match id {
            Some(i) => {
                self.kb
                    .assert_fact_with_id(buf, label, i)
                    // The assert is the reasoning stage (buffer already past smuni);
                    // logji's `assert_fact_with_id` returns a String, so wrap as Reasoning.
                    .map_err(export_err::NibliError::Reasoning)?;
                Ok(i)
            }
            None => self
                .kb
                .assert_fact(buf, label)
                .map_err(convert_pipeline_error),
        }
    }
}

impl GuestSession for Session {
    fn new() -> Self {
        // Register compute dispatch PER-KB so logji can call the host's
        // compute-backend (was a thread-local global — now per-instance).
        let kb = logji::KnowledgeBase::new();
        kb.set_compute_dispatch(eval_via_host, batch_eval_via_host);
        // The gasnu REPL is interactive (and the book captures its `[Skolem]`/
        // `[Rule]` diagnostics), so the guest opts INTO verbose stdout — unlike the
        // native nibli-engine library, which stays quiet by default. A post-trap
        // rebuild re-runs this constructor, so replayed assertions stay verbose too.
        kb.set_verbose(true);
        Session {
            kb,
            compute_predicates: RefCell::new(logji::default_compute_predicates()),
            last_relation: RefCell::new(None),
        }
    }

    fn assert_text(&self, input: String) -> Result<u64, export_err::NibliError> {
        self.assert_text_inner(input, None)
    }

    fn assert_text_with_id(&self, input: String, id: u64) -> Result<(), export_err::NibliError> {
        self.assert_text_inner(input, Some(id)).map(|_| ())
    }

    fn query_text(
        &self,
        input: String,
    ) -> Result<export_logic::QueryResult, export_err::NibliError> {
        let (buf, new_last) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        // go'i tracks the last QUERIED bridi too, not just the last asserted one
        // (the pipeline-arg borrow is dropped before this write-back). The
        // snapshot is TRANSIENT: queries are not journaled, so a WASM-trap rebuild
        // (which replays asserts only) reconstructs it from the last assertion.
        *self.last_relation.borrow_mut() = new_last;
        self.kb
            .query_entailment(buf)
            .map(|result| convert_query_result_to_export(&result))
            .map_err(convert_pipeline_error)
    }

    fn query_find_text(
        &self,
        input: String,
    ) -> Result<Vec<Vec<export_logic::WitnessBinding>>, export_err::NibliError> {
        let (buf, new_last) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        // go'i tracks the last queried bridi (transient — see `query_text`).
        *self.last_relation.borrow_mut() = new_last;
        let result = self.kb.query_find(buf).map_err(convert_pipeline_error)?;
        Ok(convert_witness_bindings(result))
    }

    fn query_text_with_proof(
        &self,
        input: String,
    ) -> Result<(export_logic::QueryResult, export_logic::ProofTrace), export_err::NibliError> {
        let (buf, new_last) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        // go'i tracks the last queried bridi (transient — see `query_text`).
        *self.last_relation.borrow_mut() = new_last;
        let (result, trace) = self
            .kb
            .query_entailment_with_proof(buf)
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
        let (buf, _) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        Ok(convert_logic_buffer_to_export(&buf))
    }

    fn reset_kb(&self) -> Result<(), export_err::NibliError> {
        *self.last_relation.borrow_mut() = None;
        self.kb.reset().map_err(convert_pipeline_error)
    }

    fn register_compute_predicate(&self, name: String) {
        self.compute_predicates.borrow_mut().insert(name);
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
        self.kb.retract_fact(id).map_err(convert_pipeline_error)
    }

    fn list_facts(&self) -> Result<Vec<export_logic::FactSummary>, export_err::NibliError> {
        let facts = self.kb.list_facts().map_err(convert_pipeline_error)?;
        Ok(convert_fact_summaries(facts))
    }
}

// ─── Tests ───

#[cfg(test)]
mod tests {
    use super::*;
    // The no-bound entry: these unit tests exercise the merge mechanics directly,
    // without a dictionary, so they're unaffected by the beyond-arity bound.
    use gerna::goi::resolve_go_i;
    use gerna_ast::{Bridi, Conversion, Sumti};

    fn make_ast(
        selbris: Vec<gerna_ast::Selbri>,
        bridi_relation: u32,
        head_terms: Vec<u32>,
    ) -> gerna_ast::AstBuffer {
        let sumtis: Vec<Sumti> = head_terms
            .iter()
            .map(|_| Sumti::ProSumti("mi".to_string()))
            .collect();
        let bridi = Bridi {
            relation: bridi_relation,
            head_terms: head_terms,
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        };
        gerna_ast::AstBuffer {
            selbris,
            sumtis,
            sentences: vec![gerna_ast::Sentence::Simple(bridi)],
            roots: vec![0],
        }
    }

    /// The selbri at a snapshot's root bridi. The snapshot root is a SENTENCE id,
    /// so reach the selbri through `sentences[root]` → `Simple(b)` → `b.relation`.
    fn snapshot_root_selbri(snap: &BridiSnapshot) -> &gerna_ast::Selbri {
        match &snap.sentences[snap.root as usize] {
            gerna_ast::Sentence::Simple(b) => &snap.selbris[b.relation as usize],
            _ => panic!("expected Simple bridi at snapshot root"),
        }
    }

    fn make_two_sentence_ast(
        mut selbris: Vec<gerna_ast::Selbri>,
        first_relation: u32,
    ) -> gerna_ast::AstBuffer {
        let go_i_id = selbris.len() as u32;
        selbris.push(gerna_ast::Selbri::Root("go'i".to_string()));
        gerna_ast::AstBuffer {
            selbris,
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),
                Sumti::ProSumti("do".to_string()),
            ],
            sentences: vec![
                gerna_ast::Sentence::Simple(Bridi {
                    relation: first_relation,
                    head_terms: vec![0],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
                gerna_ast::Sentence::Simple(Bridi {
                    relation: go_i_id,
                    head_terms: vec![1],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
            ],
            roots: vec![0, 1],
        }
    }

    fn bridi_relation(ast: &gerna_ast::AstBuffer, sentence_idx: usize) -> u32 {
        match &ast.sentences[sentence_idx] {
            gerna_ast::Sentence::Simple(b) => b.relation,
            _ => panic!("expected Simple"),
        }
    }

    #[test]
    fn test_snapshot_root() {
        // make_ast builds ONE sentence (id 0); extract from the SENTENCE.
        let ast = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let snap = extract_bridi_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 1);
        assert_eq!(snap.root, 0);
        assert!(matches!(snapshot_root_selbri(&snap), gerna_ast::Selbri::Root(n) if n == "klama"));
    }

    #[test]
    fn test_snapshot_negated() {
        let ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Negated(0),
            ],
            1,
            vec![0],
        );
        let snap = extract_bridi_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 2);
        assert!(matches!(
            snapshot_root_selbri(&snap),
            gerna_ast::Selbri::Negated(_)
        ));
    }

    #[test]
    fn test_snapshot_converted() {
        let ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("prami".to_string()),
                gerna_ast::Selbri::Converted((Conversion::Se, 0)),
            ],
            1,
            vec![0],
        );
        let snap = extract_bridi_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 2);
        assert!(matches!(
            snapshot_root_selbri(&snap),
            gerna_ast::Selbri::Converted((Conversion::Se, _))
        ));
    }

    #[test]
    fn test_snapshot_negated_converted() {
        let ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Converted((Conversion::Se, 0)),
                gerna_ast::Selbri::Negated(1),
            ],
            2,
            vec![0],
        );
        let snap = extract_bridi_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 3);
        assert!(
            matches!(snapshot_root_selbri(&snap), gerna_ast::Selbri::Negated(inner) if {
                matches!(&snap.selbris[*inner as usize], gerna_ast::Selbri::Converted((Conversion::Se, inner2)) if {
                    matches!(&snap.selbris[*inner2 as usize], gerna_ast::Selbri::Root(n) if n == "klama")
                })
            })
        );
    }

    #[test]
    fn test_graft_rebase_indices() {
        // A sentence-rooted snapshot of `klama(mi)` grafted onto a non-empty
        // buffer: every selbri/sumti/sentence index shifts by the base lengths.
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![gerna_ast::Selbri::Root("existing".to_string())],
            sumtis: vec![Sumti::ProSumti("ti".to_string())],
            sentences: vec![gerna_ast::Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            roots: vec![0],
        };
        let mut snap = BridiSnapshot {
            selbris: vec![gerna_ast::Selbri::Root("klama".to_string())],
            sumtis: vec![Sumti::ProSumti("mi".to_string())],
            sentences: vec![gerna_ast::Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![0],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            root: 0,
        };
        // sb=1, ub=1, tb=1 → the grafted sentence lands at index 1.
        let grafted_root = gerna::goi::graft_snapshot(&mut ast, &mut snap);
        assert_eq!(grafted_root, 1);
        assert!(matches!(&ast.selbris[1], gerna_ast::Selbri::Root(n) if n == "klama"));
        assert!(matches!(&ast.sumtis[1], Sumti::ProSumti(n) if n == "mi"));
        match &ast.sentences[1] {
            gerna_ast::Sentence::Simple(b) => {
                assert_eq!(b.relation, 1, "relation rebased by sb");
                assert_eq!(b.head_terms, vec![1], "head_terms rebased by ub");
            }
            _ => panic!("expected Simple bridi"),
        }
    }

    #[test]
    fn test_resolve_go_i_basic_root() {
        let mut ast = make_two_sentence_ast(vec![gerna_ast::Selbri::Root("klama".to_string())], 0);
        let result = resolve_go_i(&mut ast, &mut None).unwrap();
        assert_eq!(bridi_relation(&ast, 1), 0);
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_negation() {
        let mut ast = make_two_sentence_ast(
            vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Negated(0),
            ],
            1,
        );
        let result = resolve_go_i(&mut ast, &mut None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 1);
        assert!(
            matches!(&ast.selbris[go_i_rel as usize], gerna_ast::Selbri::Negated(inner) if {
                matches!(&ast.selbris[*inner as usize], gerna_ast::Selbri::Root(n) if n == "klama")
            })
        );
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_conversion() {
        let mut ast = make_two_sentence_ast(
            vec![
                gerna_ast::Selbri::Root("prami".to_string()),
                gerna_ast::Selbri::Converted((Conversion::Se, 0)),
            ],
            1,
        );
        let result = resolve_go_i(&mut ast, &mut None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 1);
        assert!(matches!(
            &ast.selbris[go_i_rel as usize],
            gerna_ast::Selbri::Converted((Conversion::Se, _))
        ));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_negated_conversion() {
        let mut ast = make_two_sentence_ast(
            vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Converted((Conversion::Se, 0)),
                gerna_ast::Selbri::Negated(1),
            ],
            2,
        );
        let result = resolve_go_i(&mut ast, &mut None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 2);
        assert!(matches!(
            &ast.selbris[go_i_rel as usize],
            gerna_ast::Selbri::Negated(_)
        ));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_tanru() {
        let mut ast = make_two_sentence_ast(
            vec![
                gerna_ast::Selbri::Root("sutra".to_string()),
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Tanru((0, 1)),
            ],
            2,
        );
        let result = resolve_go_i(&mut ast, &mut None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 2);
        assert!(matches!(
            &ast.selbris[go_i_rel as usize],
            gerna_ast::Selbri::Tanru((0, 1))
        ));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_no_antecedent() {
        let mut ast = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let result = resolve_go_i(&mut ast, &mut None);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("no antecedent"));
    }

    #[test]
    fn test_resolve_go_i_cross_call_root() {
        // `mi go'i` (a PARTIAL go'i, head_terms=[mi]) against a `klama` snapshot:
        // repoint-only keeps `mi`, repoints the relation to klama.
        let snap = BridiSnapshot {
            selbris: vec![gerna_ast::Selbri::Root("klama".to_string())],
            sumtis: vec![],
            sentences: vec![gerna_ast::Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            root: 0,
        };
        let mut ast = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let result = resolve_go_i(&mut ast, &mut Some(snap)).unwrap();
        let go_i_rel = bridi_relation(&ast, 0);
        assert!(
            matches!(&ast.selbris[go_i_rel as usize], gerna_ast::Selbri::Root(n) if n == "klama")
        );
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_cross_call_negated() {
        let snap = BridiSnapshot {
            selbris: vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Negated(0),
            ],
            sumtis: vec![],
            sentences: vec![gerna_ast::Sentence::Simple(Bridi {
                relation: 1,
                head_terms: vec![],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            root: 0,
        };
        let mut ast = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let result = resolve_go_i(&mut ast, &mut Some(snap)).unwrap();
        let go_i_rel = bridi_relation(&ast, 0);
        assert!(matches!(
            &ast.selbris[go_i_rel as usize],
            gerna_ast::Selbri::Negated(_)
        ));
        assert!(result.is_some());
    }

    // ─── Session lifecycle: go'i snapshot must survive repeated resolution ───

    #[test]
    fn resolve_go_i_does_not_drain_snapshot() {
        // The stored snapshot must NOT be drained by a graft — graft_snapshot
        // appends (drains) its vecs, so it must operate on a clone.
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let snap = extract_bridi_snapshot(&src, 0);
        let mut last = Some(snap);
        let mut ast = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let res = resolve_go_i(&mut ast, &mut last).unwrap();
        assert!(res.is_some());
        let kept = last.expect("snapshot must survive the graft");
        assert!(
            !kept.selbris.is_empty(),
            "snapshot selbris were drained by the graft"
        );
        assert!(matches!(snapshot_root_selbri(&kept), gerna_ast::Selbri::Root(n) if n == "klama"));
    }

    #[test]
    fn go_i_bare_inherits_full_bridi_terms() {
        // `mi klama` (snapshot) then a BARE `? go'i` (no terms) repeats the WHOLE
        // bridi — the resolved go'i bridi inherits the antecedent's `mi` term.
        // RED before the full-bridi snapshot fix (head_terms stayed empty →
        // `klama(zo'e)` → FALSE).
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0], // head_terms = [mi]
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        // Bare `? go'i`: empty head/tail terms (the observative parse).
        let mut ast = make_ast(vec![gerna_ast::Selbri::Root("go'i".to_string())], 0, vec![]);
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[0] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!("expected Simple"),
        };
        assert!(
            !b.head_terms.is_empty(),
            "bare go'i did not inherit the antecedent's terms"
        );
        assert!(matches!(
            &ast.sumtis[b.head_terms[0] as usize],
            gerna_ast::Sumti::ProSumti(n) if n == "mi"
        ));
    }

    #[test]
    fn go_i_bare_inherits_tense() {
        // `mi pu klama` (past) then bare `? go'i` repeats the TENSE too — a win
        // the selbri-only snapshot could never produce (tense lives on the Bridi,
        // not the Selbri).
        let mut src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        if let gerna_ast::Sentence::Simple(b) = &mut src.sentences[0] {
            b.tense = Some(gerna_ast::Tense::Pu);
        }
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = make_ast(vec![gerna_ast::Selbri::Root("go'i".to_string())], 0, vec![]);
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[0] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!("expected Simple"),
        };
        assert!(
            matches!(b.tense, Some(gerna_ast::Tense::Pu)),
            "bare go'i did not inherit the antecedent's tense"
        );
    }

    #[test]
    fn repeated_go_i_resolves_in_bounds() {
        // `mi klama` then `? go'i` then `? go'i` — the second go'i must still
        // resolve to a valid IN-BOUNDS klama selbri. Pre-fix the snapshot was
        // drained, so the second graft appended empty vecs and the resolved
        // relation index pointed one past the end of `selbris` (the dangling
        // index that becomes the WASM component trap during compilation).
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));

        let mut ast1 = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        resolve_go_i(&mut ast1, &mut last).unwrap();

        let mut ast2 = make_ast(
            vec![gerna_ast::Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        resolve_go_i(&mut ast2, &mut last).unwrap();
        let rel = bridi_relation(&ast2, 0) as usize;
        assert!(
            rel < ast2.selbris.len(),
            "resolved relation index out of bounds (drained snapshot)"
        );
        assert!(matches!(&ast2.selbris[rel], gerna_ast::Selbri::Root(n) if n == "klama"));
    }

    #[test]
    fn tanru_go_i_resolves_to_antecedent_relation() {
        // `mi sutra go'i` after `mi klama` — the SELBRI-position go'i (the tanru's
        // head arm) resolves to the antecedent's relation selbri, giving
        // `mi sutra klama`.
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        // selbris: [0]=sutra, [1]=go'i, [2]=Tanru(0,1); root bridi.relation = 2.
        let mut ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("sutra".to_string()),
                gerna_ast::Selbri::Root("go'i".to_string()),
                gerna_ast::Selbri::Tanru((0, 1)),
            ],
            2,
            vec![0],
        );
        let res = resolve_go_i(&mut ast, &mut last);
        assert!(res.is_ok(), "tanru go'i must resolve, got {res:?}");
        // The go'i arm (selbri index 1) is now the antecedent relation `klama`.
        assert!(
            matches!(&ast.selbris[1], gerna_ast::Selbri::Root(n) if n == "klama"),
            "the go'i tanru arm resolves to the antecedent relation klama, got {:?}",
            ast.selbris[1]
        );
        // The tanru structure (sutra + resolved arm) is intact.
        assert!(matches!(&ast.selbris[2], gerna_ast::Selbri::Tanru((0, 1))));
    }

    #[test]
    fn tanru_go_i_complex_antecedent_relation() {
        // Antecedent relation is itself a tanru `barda klama`. `mi sutra go'i`
        // resolves the go'i arm to that whole tanru node (sharing its grafted
        // children) — no fresh subtree graft needed.
        let src = make_ast(
            vec![
                gerna_ast::Selbri::Root("barda".to_string()),
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Tanru((0, 1)),
            ],
            2,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("sutra".to_string()),
                gerna_ast::Selbri::Root("go'i".to_string()),
                gerna_ast::Selbri::Tanru((0, 1)),
            ],
            2,
            vec![0],
        );
        let res = resolve_go_i(&mut ast, &mut last);
        assert!(
            res.is_ok(),
            "complex-relation tanru go'i must resolve, got {res:?}"
        );
        // selbris[1] (the go'i arm) is now a Tanru whose arms are the grafted barda/klama.
        let gerna_ast::Selbri::Tanru((m, h)) = &ast.selbris[1] else {
            panic!(
                "go'i arm should resolve to the antecedent tanru, got {:?}",
                ast.selbris[1]
            );
        };
        assert!(matches!(&ast.selbris[*m as usize], gerna_ast::Selbri::Root(n) if n == "barda"));
        assert!(matches!(&ast.selbris[*h as usize], gerna_ast::Selbri::Root(n) if n == "klama"));
    }

    #[test]
    fn tanru_go_i_no_antecedent_rejected() {
        // `mi sutra go'i` with NO prior bridi → the go'i arm has no antecedent.
        let mut ast = make_ast(
            vec![
                gerna_ast::Selbri::Root("sutra".to_string()),
                gerna_ast::Selbri::Root("go'i".to_string()),
                gerna_ast::Selbri::Tanru((0, 1)),
            ],
            2,
            vec![0],
        );
        let res = resolve_go_i(&mut ast, &mut None);
        assert!(res.is_err(), "a tanru go'i with no antecedent must error");
        assert!(res.unwrap_err().contains("no antecedent"));
    }

    // ─── (a) partial go'i per-place merge ───

    #[test]
    fn test_partial_go_i_inherits_antecedent_place() {
        // `mi pu klama` then `? pu go'i`: a PARTIAL go'i (supplies a tense, no
        // terms) inherits the antecedent's x1 (`mi`) per place and keeps its own
        // tense. RED before the merge — the partial path kept the empty go'i terms
        // (`pu klama(zo'e)`).
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = make_ast(vec![gerna_ast::Selbri::Root("go'i".to_string())], 0, vec![]);
        if let gerna_ast::Sentence::Simple(b) = &mut ast.sentences[0] {
            b.tense = Some(gerna_ast::Tense::Pu);
        }
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[0] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert_eq!(b.head_terms.len(), 1, "partial go'i must inherit x1");
        assert!(
            matches!(&ast.sumtis[b.head_terms[0] as usize], gerna_ast::Sumti::ProSumti(n) if n == "mi")
        );
        assert!(
            matches!(b.tense, Some(gerna_ast::Tense::Pu)),
            "keeps its own tense"
        );
        assert!(
            matches!(&ast.selbris[b.relation as usize], gerna_ast::Selbri::Root(n) if n == "klama")
        );
    }

    #[test]
    fn test_partial_go_i_supplied_place_overrides() {
        // `mi klama .i do go'i`: the supplied x1 (`do`) overrides the antecedent's.
        let mut ast = make_two_sentence_ast(vec![gerna_ast::Selbri::Root("klama".to_string())], 0);
        let mut last: Option<BridiSnapshot> = None;
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[1] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert!(
            matches!(&ast.sumtis[b.head_terms[0] as usize], gerna_ast::Sumti::ProSumti(n) if n == "do"),
            "supplied place must override the antecedent's"
        );
        assert!(
            matches!(&ast.selbris[b.relation as usize], gerna_ast::Selbri::Root(n) if n == "klama")
        );
    }

    #[test]
    fn test_partial_go_i_na_negates() {
        // `mi klama` then `na go'i`: a partial go'i adds negation, inheriting x1.
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = make_ast(vec![gerna_ast::Selbri::Root("go'i".to_string())], 0, vec![]);
        if let gerna_ast::Sentence::Simple(b) = &mut ast.sentences[0] {
            b.negated = true;
        }
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[0] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert!(b.negated, "na go'i must negate");
        assert!(
            matches!(&ast.sumtis[b.head_terms[0] as usize], gerna_ast::Sumti::ProSumti(n) if n == "mi")
        );
    }

    #[test]
    fn test_partial_go_i_fe_tagged_place() {
        // `mi klama` then `fe do go'i`: the FA-tagged `do` fills x2, x1 inherits.
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![gerna_ast::Selbri::Root("go'i".to_string())],
            sumtis: vec![
                Sumti::ProSumti("do".to_string()),           // 0
                Sumti::Tagged((gerna_ast::PlaceTag::Fe, 0)), // 1: fe do
            ],
            sentences: vec![gerna_ast::Sentence::Simple(Bridi {
                relation: 0,
                head_terms: vec![1],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
            roots: vec![0],
        };
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[0] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert_eq!(b.head_terms.len(), 2, "x1 inherited + x2 from `fe do`");
        assert!(
            matches!(&ast.sumtis[b.head_terms[0] as usize], gerna_ast::Sumti::ProSumti(n) if n == "mi")
        );
        assert!(
            matches!(&ast.sumtis[b.head_terms[1] as usize], gerna_ast::Sumti::ProSumti(n) if n == "do")
        );
    }

    // ─── (d) direct-API assert_fact snapshot carries sumti ───

    #[test]
    fn assert_fact_snapshot_carries_args() {
        // Ground Constant/Number args become positional Name/Number sumti;
        // Variable/Description degrade to a place-preserving zo'e.
        let (sumtis, head) = synth_snapshot_terms(&[
            export_logic::LogicalTerm::Constant("adam".to_string()),
            export_logic::LogicalTerm::Number(42.0),
            export_logic::LogicalTerm::Variable("da".to_string()),
        ]);
        assert_eq!(head, vec![0, 1, 2]);
        assert!(matches!(&sumtis[0], gerna_ast::Sumti::Name(n) if n == "adam"));
        assert!(matches!(&sumtis[1], gerna_ast::Sumti::Number(n) if *n == 42.0));
        assert!(matches!(&sumtis[2], gerna_ast::Sumti::Unspecified));
    }

    // ─── (c1) nested SENTENCE-position go'i resolution ───

    #[test]
    fn nested_go_i_abstraction_body_bare() {
        // `mi nelci lo nu go'i` — a BARE go'i as the whole `nu` abstraction body
        // resolves to the antecedent bridi (`klama(mi)`). RED before c1 (rejected).
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![
                gerna_ast::Selbri::Root("nelci".to_string()), // 0
                gerna_ast::Selbri::Root("go'i".to_string()),  // 1 (nu body relation)
                gerna_ast::Selbri::Abstraction((gerna_ast::AbstractionKind::Nu, 1)), // 2
            ],
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),             // 0
                Sumti::Description((gerna_ast::Gadri::Lo, 2)), // 1: lo nu ...
            ],
            sentences: vec![
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 0,
                    head_terms: vec![0],
                    tail_terms: vec![1],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }), // 0: mi nelci [lo nu go'i]
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 1,
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }), // 1: go'i (nu body)
            ],
            roots: vec![0],
        };
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[1] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert!(
            matches!(&ast.selbris[b.relation as usize], gerna_ast::Selbri::Root(n) if n == "klama"),
            "nested go'i body must resolve to the klama antecedent"
        );
    }

    #[test]
    fn nested_go_i_relclause_body_bare() {
        // `mi prami do poi go'i` — a BARE go'i as a relative-clause body resolves.
        let src = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let mut last = Some(extract_bridi_snapshot(&src, 0));
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![
                gerna_ast::Selbri::Root("prami".to_string()), // 0
                gerna_ast::Selbri::Root("go'i".to_string()),  // 1 (rel-clause body relation)
            ],
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()), // 0
                Sumti::ProSumti("do".to_string()), // 1 (restricted inner)
                Sumti::Restricted((
                    1,
                    gerna_ast::RelClause {
                        kind: gerna_ast::RelClauseKind::Poi,
                        body_sentence: 1,
                    },
                )), // 2: do poi <sentence 1>
            ],
            sentences: vec![
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 0,
                    head_terms: vec![0],
                    tail_terms: vec![2],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }), // 0: mi prami [do poi go'i]
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 1,
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }), // 1: go'i
            ],
            roots: vec![0],
        };
        resolve_go_i(&mut ast, &mut last).unwrap();
        let b = match &ast.sentences[1] {
            gerna_ast::Sentence::Simple(b) => b.clone(),
            _ => panic!(),
        };
        assert!(
            matches!(&ast.selbris[b.relation as usize], gerna_ast::Selbri::Root(n) if n == "klama")
        );
    }

    #[test]
    fn nested_go_i_no_antecedent_errors() {
        // A nested go'i with NO antecedent (no prior bridi, no snapshot) errors.
        let mut last: Option<BridiSnapshot> = None;
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![
                gerna_ast::Selbri::Root("nelci".to_string()),
                gerna_ast::Selbri::Root("go'i".to_string()),
                gerna_ast::Selbri::Abstraction((gerna_ast::AbstractionKind::Nu, 1)),
            ],
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),
                Sumti::Description((gerna_ast::Gadri::Lo, 2)),
            ],
            sentences: vec![
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 0,
                    head_terms: vec![0],
                    tail_terms: vec![1],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
                gerna_ast::Sentence::Simple(Bridi {
                    relation: 1,
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
            ],
            roots: vec![0],
        };
        let res = resolve_go_i(&mut ast, &mut last);
        assert!(
            res.is_err(),
            "nested go'i with no antecedent must error, got {res:?}"
        );
        assert!(res.unwrap_err().contains("no antecedent"));
    }

    #[test]
    fn convert_proof_trace_carries_naf_dependent() {
        // A trace with a holds:true Negation step is NAF-dependent (the verdict
        // rests on the closed-world assumption). convert_proof_trace must carry
        // the flag across the WIT boundary so a host need not recompute it from
        // the steps (single source of truth: ProofTrace::has_naf_dependency).
        let naf_trace = logji_logic::ProofTrace {
            steps: vec![logji_logic::ProofStep {
                rule: logji_logic::ProofRule::Negation,
                holds: true,
                children: vec![],
            }],
            root: 0,
            naf_dependent: true,
            cwa_false: false,
        };
        assert!(
            convert_proof_trace(naf_trace).naf_dependent,
            "a holds:true Negation step must set naf_dependent on the WIT trace"
        );

        // A trace whose only step is a plain assertion is NOT NAF-dependent.
        let plain_trace = logji_logic::ProofTrace {
            steps: vec![logji_logic::ProofStep {
                rule: logji_logic::ProofRule::Asserted {
                    fact: "gerku(adam)".to_string(),
                },
                holds: true,
                children: vec![],
            }],
            root: 0,
            naf_dependent: false,
            cwa_false: false,
        };
        assert!(
            !convert_proof_trace(plain_trace).naf_dependent,
            "a non-negation trace must not be naf_dependent"
        );
    }
}

#[cfg(target_arch = "wasm32")]
bindings::export!(LasnaPipeline with_types_in bindings);
