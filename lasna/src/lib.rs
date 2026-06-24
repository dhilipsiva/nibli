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

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;

/// WIT component implementation for the `lasna` interface.
struct LasnaPipeline;

/// A user-facing session wrapping the full gerna → smuni → logji pipeline.
pub struct Session {
    kb: logji::KnowledgeBase,
    compute_predicates: RefCell<HashSet<String>>,
    last_relation: RefCell<Option<BridiSnapshot>>,
}

/// A self-contained clone of a full bridi (its sentence + selbri + sumti
/// subtrees), storable across calls. All indices are internal to the snapshot's
/// own vecs; `root` is a SENTENCE id (the antecedent bridi) so a bare `go'i`
/// can repeat the whole previous predication — relation AND sumti — not just the
/// selbri.
#[derive(Clone)]
struct BridiSnapshot {
    selbris: Vec<gerna_ast::Selbri>,
    sumtis: Vec<gerna_ast::Sumti>,
    sentences: Vec<gerna_ast::Sentence>,
    root: u32,
}

// ─── Default compute predicates ───

fn default_compute_predicates() -> HashSet<String> {
    let mut set = HashSet::new();
    set.insert("pilji".to_string());
    set.insert("sumji".to_string());
    set.insert("dilcu".to_string());
    set
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

// ─── Selbri snapshot: extract & graft subtrees for cross-call go'i ───

/// Extract the self-contained full-bridi subtree rooted at the SENTENCE
/// `sentence_id` from `ast` (relation + every head/tail term sumti, preserving
/// tense/negation/attitudinal). `visit_sentence` already deep-clones a `Simple`
/// bridi, so this is a thin wrapper over it.
fn extract_bridi_snapshot(ast: &gerna_ast::AstBuffer, sentence_id: u32) -> BridiSnapshot {
    let mut snap = BridiSnapshot {
        selbris: Vec::new(),
        sumtis: Vec::new(),
        sentences: Vec::new(),
        root: 0,
    };
    let mut sm = HashMap::new();
    let mut um = HashMap::new();
    let mut tm = HashMap::new();
    snap.root = visit_sentence(ast, sentence_id, &mut snap, &mut sm, &mut um, &mut tm);
    snap
}

fn visit_selbri(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = sm.get(&id) {
        return mapped;
    }
    let new_id = snap.selbris.len() as u32;
    sm.insert(id, new_id);
    snap.selbris.push(gerna_ast::Selbri::Root(String::new())); // placeholder
    let mapped = match &ast.selbris[id as usize] {
        gerna_ast::Selbri::Root(n) => gerna_ast::Selbri::Root(n.clone()),
        gerna_ast::Selbri::Compound(p) => gerna_ast::Selbri::Compound(p.clone()),
        gerna_ast::Selbri::Tanru((m, h)) => {
            let nm = visit_selbri(ast, *m, snap, sm, um, tm);
            let nh = visit_selbri(ast, *h, snap, sm, um, tm);
            gerna_ast::Selbri::Tanru((nm, nh))
        }
        gerna_ast::Selbri::Converted((c, i)) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Converted((*c, ni))
        }
        gerna_ast::Selbri::Negated(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Negated(ni)
        }
        gerna_ast::Selbri::Grouped(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            gerna_ast::Selbri::Grouped(ni)
        }
        gerna_ast::Selbri::WithArgs((core, args)) => {
            let nc = visit_selbri(ast, *core, snap, sm, um, tm);
            let na: Vec<u32> = args
                .iter()
                .map(|&a| visit_sumti(ast, a, snap, sm, um, tm))
                .collect();
            gerna_ast::Selbri::WithArgs((nc, na))
        }
        gerna_ast::Selbri::Connected((l, c, r)) => {
            let nl = visit_selbri(ast, *l, snap, sm, um, tm);
            let nr = visit_selbri(ast, *r, snap, sm, um, tm);
            gerna_ast::Selbri::Connected((nl, c.clone(), nr))
        }
        gerna_ast::Selbri::Abstraction((k, s)) => {
            let ns = visit_sentence(ast, *s, snap, sm, um, tm);
            gerna_ast::Selbri::Abstraction((*k, ns))
        }
    };
    snap.selbris[new_id as usize] = mapped;
    new_id
}

fn visit_sumti(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = um.get(&id) {
        return mapped;
    }
    let new_id = snap.sumtis.len() as u32;
    um.insert(id, new_id);
    snap.sumtis.push(gerna_ast::Sumti::Unspecified); // placeholder
    let mapped = match &ast.sumtis[id as usize] {
        gerna_ast::Sumti::ProSumti(s) => gerna_ast::Sumti::ProSumti(s.clone()),
        gerna_ast::Sumti::Description((g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            gerna_ast::Sumti::Description((*g, ns))
        }
        gerna_ast::Sumti::Name(s) => gerna_ast::Sumti::Name(s.clone()),
        gerna_ast::Sumti::QuotedLiteral(s) => gerna_ast::Sumti::QuotedLiteral(s.clone()),
        gerna_ast::Sumti::Unspecified => gerna_ast::Sumti::Unspecified,
        gerna_ast::Sumti::Tagged((t, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            gerna_ast::Sumti::Tagged((*t, ni))
        }
        gerna_ast::Sumti::ModalTagged((mt, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let nmt = match mt {
                gerna_ast::ModalTag::Fixed(b) => gerna_ast::ModalTag::Fixed(*b),
                gerna_ast::ModalTag::Fio(sid) => {
                    let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
                    gerna_ast::ModalTag::Fio(ns)
                }
            };
            gerna_ast::Sumti::ModalTagged((nmt, ni))
        }
        gerna_ast::Sumti::Restricted((inner, rc)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let ns = visit_sentence(ast, rc.body_sentence, snap, sm, um, tm);
            gerna_ast::Sumti::Restricted((
                ni,
                gerna_ast::RelClause {
                    kind: rc.kind,
                    body_sentence: ns,
                },
            ))
        }
        gerna_ast::Sumti::Number(n) => gerna_ast::Sumti::Number(*n),
        gerna_ast::Sumti::Connected((l, c, neg, r)) => {
            let nl = visit_sumti(ast, *l, snap, sm, um, tm);
            let nr = visit_sumti(ast, *r, snap, sm, um, tm);
            gerna_ast::Sumti::Connected((nl, c.clone(), *neg, nr))
        }
        gerna_ast::Sumti::QuantifiedDescription((count, g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            gerna_ast::Sumti::QuantifiedDescription((*count, *g, ns))
        }
    };
    snap.sumtis[new_id as usize] = mapped;
    new_id
}

fn visit_sentence(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut BridiSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = tm.get(&id) {
        return mapped;
    }
    let new_id = snap.sentences.len() as u32;
    tm.insert(id, new_id);
    // placeholder
    snap.sentences
        .push(gerna_ast::Sentence::Simple(gerna_ast::Bridi {
            relation: 0,
            head_terms: vec![],
            tail_terms: vec![],
            negated: false,
            tense: None,
            attitudinal: None,
        }));
    let mapped = match &ast.sentences[id as usize] {
        gerna_ast::Sentence::Simple(b) => {
            let nr = visit_selbri(ast, b.relation, snap, sm, um, tm);
            let nh: Vec<u32> = b
                .head_terms
                .iter()
                .map(|&s| visit_sumti(ast, s, snap, sm, um, tm))
                .collect();
            let nt: Vec<u32> = b
                .tail_terms
                .iter()
                .map(|&s| visit_sumti(ast, s, snap, sm, um, tm))
                .collect();
            gerna_ast::Sentence::Simple(gerna_ast::Bridi {
                relation: nr,
                head_terms: nh,
                tail_terms: nt,
                negated: b.negated,
                tense: b.tense,
                attitudinal: b.attitudinal,
            })
        }
        gerna_ast::Sentence::Connected((c, l, r)) => {
            let nl = visit_sentence(ast, *l, snap, sm, um, tm);
            let nr = visit_sentence(ast, *r, snap, sm, um, tm);
            gerna_ast::Sentence::Connected((c.clone(), nl, nr))
        }
        gerna_ast::Sentence::Prenex((vars, body)) => {
            let nb = visit_sentence(ast, *body, snap, sm, um, tm);
            gerna_ast::Sentence::Prenex((vars.clone(), nb))
        }
    };
    snap.sentences[new_id as usize] = mapped;
    new_id
}

/// Graft a snapshot into an existing AstBuffer, consuming it. Returns the new
/// SENTENCE (bridi) root index. Mutates indices in place then moves nodes via
/// `append` — zero cloning.
fn graft_snapshot(ast: &mut gerna_ast::AstBuffer, snap: &mut BridiSnapshot) -> u32 {
    let sb = ast.selbris.len() as u32;
    let ub = ast.sumtis.len() as u32;
    let tb = ast.sentences.len() as u32;
    for s in &mut snap.selbris {
        rebase_selbri_inplace(s, sb, ub, tb);
    }
    for s in &mut snap.sumtis {
        rebase_sumti_inplace(s, sb, ub, tb);
    }
    for s in &mut snap.sentences {
        rebase_sentence_inplace(s, sb, ub, tb);
    }
    // `root` is a SENTENCE id, so it rebases by the sentence base (`tb`).
    let root = snap.root + tb;
    ast.selbris.append(&mut snap.selbris);
    ast.sumtis.append(&mut snap.sumtis);
    ast.sentences.append(&mut snap.sentences);
    root
}

fn rebase_selbri_inplace(s: &mut gerna_ast::Selbri, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Selbri::Root(_) | gerna_ast::Selbri::Compound(_) => {}
        gerna_ast::Selbri::Tanru((m, h)) => {
            *m += sb;
            *h += sb;
        }
        gerna_ast::Selbri::Converted((_, i)) => {
            *i += sb;
        }
        gerna_ast::Selbri::Negated(i) | gerna_ast::Selbri::Grouped(i) => {
            *i += sb;
        }
        gerna_ast::Selbri::WithArgs((core, args)) => {
            *core += sb;
            for a in args.iter_mut() {
                *a += ub;
            }
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            *l += sb;
            *r += sb;
        }
        gerna_ast::Selbri::Abstraction((_, sent)) => {
            *sent += tb;
        }
    }
}

fn rebase_sumti_inplace(s: &mut gerna_ast::Sumti, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => {}
        gerna_ast::Sumti::Description((_, sid)) => {
            *sid += sb;
        }
        gerna_ast::Sumti::Tagged((_, i)) => {
            *i += ub;
        }
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            if let gerna_ast::ModalTag::Fio(sid) = mt {
                *sid += sb;
            }
            *i += ub;
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            *i += ub;
            rc.body_sentence += tb;
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            *l += ub;
            *r += ub;
        }
        gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            *sid += sb;
        }
    }
}

fn rebase_sentence_inplace(s: &mut gerna_ast::Sentence, sb: u32, ub: u32, tb: u32) {
    match s {
        gerna_ast::Sentence::Simple(b) => {
            b.relation += sb;
            for i in b.head_terms.iter_mut() {
                *i += ub;
            }
            for i in b.tail_terms.iter_mut() {
                *i += ub;
            }
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            *l += tb;
            *r += tb;
        }
        gerna_ast::Sentence::Prenex((_, body)) => {
            *body += tb;
        }
    }
}

/// Map a bridi's head+tail term ids to place positions (x1=0, x2=1, …) using the
/// SAME positional FA rule as smuni's `compile_bridi`: an untagged term fills the
/// next free place; a `Sumti::Tagged((tag, inner))` sets the place to
/// `tag.to_index()` and stores the INNER id (the tag is stripped — the merged
/// bridi is positional), resuming after it.
fn place_map(sumtis: &[gerna_ast::Sumti], head: &[u32], tail: &[u32]) -> Vec<Option<u32>> {
    let mut places: Vec<Option<u32>> = Vec::new();
    let mut next = 0usize;
    for &t in head.iter().chain(tail.iter()) {
        let (place, id) = match &sumtis[t as usize] {
            gerna_ast::Sumti::Tagged((tag, inner)) => (tag.to_index(), *inner),
            _ => {
                while next < places.len() && places[next].is_some() {
                    next += 1;
                }
                (next, t)
            }
        };
        if place >= places.len() {
            places.resize(place + 1, None);
        }
        places[place] = Some(id);
        next = place + 1;
    }
    places
}

/// Resolve a Simple bridi's go'i (when its relation selbri is `Root("go'i")`)
/// against the antecedent identified by `current`. BARE go'i (`go'i` / `? go'i`,
/// no own sumti/tense/negation/attitudinal) repeats the WHOLE antecedent bridi;
/// a PARTIAL go'i (`do go'i`, `na go'i`, `pu go'i`) merges per place — the go'i's
/// supplied places override, unsupplied places inherit from the antecedent, and
/// tense/negation/attitudinal are overridden only when the go'i supplies them.
/// The antecedent's term ids are already valid in `ast.sumtis` (grafted from a
/// snapshot or a live in-buffer sentence), so the merge is pure id-selection — no
/// rebasing. Does NOT touch `current` (the caller owns antecedent advancement);
/// no-op if the bridi is not a go'i.
fn resolve_simple_bridi_go_i(
    ast: &mut gerna_ast::AstBuffer,
    sentence_idx: usize,
    current: &Option<u32>,
) -> Result<(), String> {
    let gerna_ast::Sentence::Simple(mut bridi) = ast.sentences[sentence_idx].clone() else {
        return Ok(());
    };
    let is_go_i =
        matches!(&ast.selbris[bridi.relation as usize], gerna_ast::Selbri::Root(n) if n == "go'i");
    if !is_go_i {
        return Ok(());
    }
    let antecedent_sid =
        current.ok_or_else(|| "go'i has no antecedent (no previous assertion)".to_string())?;
    let antecedent = match &ast.sentences[antecedent_sid as usize] {
        gerna_ast::Sentence::Simple(b) => b.clone(),
        _ => return Err("go'i antecedent is not a simple bridi".to_string()),
    };

    let bare = bridi.head_terms.is_empty()
        && bridi.tail_terms.is_empty()
        && bridi.tense.is_none()
        && !bridi.negated
        && bridi.attitudinal.is_none();
    if bare {
        ast.sentences[sentence_idx] = gerna_ast::Sentence::Simple(antecedent);
        return Ok(());
    }

    // Per-place merge: overlay the go'i's supplied places over the antecedent's.
    let ant = place_map(&ast.sumtis, &antecedent.head_terms, &antecedent.tail_terms);
    let goi = place_map(&ast.sumtis, &bridi.head_terms, &bridi.tail_terms);
    let n = ant.len().max(goi.len());
    let mut head_terms = Vec::with_capacity(n);
    for i in 0..n {
        let id = goi
            .get(i)
            .copied()
            .flatten()
            .or_else(|| ant.get(i).copied().flatten())
            .unwrap_or_else(|| {
                // A place neither side supplies becomes a fresh `zo'e` so smuni's
                // positional counter stays aligned.
                let uid = ast.sumtis.len() as u32;
                ast.sumtis.push(gerna_ast::Sumti::Unspecified);
                uid
            });
        head_terms.push(id);
    }
    bridi.relation = antecedent.relation;
    bridi.head_terms = head_terms;
    bridi.tail_terms = vec![];
    bridi.negated = antecedent.negated || bridi.negated;
    bridi.tense = bridi.tense.or(antecedent.tense);
    bridi.attitudinal = bridi.attitudinal.or(antecedent.attitudinal);
    ast.sentences[sentence_idx] = gerna_ast::Sentence::Simple(bridi);
    Ok(())
}

/// Resolve go'i references in a single TOP-LEVEL sentence, advancing `current`.
fn resolve_sentence_go_i(
    ast: &mut gerna_ast::AstBuffer,
    sentence_idx: usize,
    current: &mut Option<u32>,
) -> Result<(), String> {
    match ast.sentences[sentence_idx].clone() {
        gerna_ast::Sentence::Simple(_) => {
            // Resolve this bridi's own top-level go'i (bare → whole antecedent;
            // partial → per-place merge).
            resolve_simple_bridi_go_i(ast, sentence_idx, &*current)?;
            // Descend into NESTED positions (abstraction / relative-clause bodies)
            // and resolve any go'i there, reading `current` as the PRIOR top-level
            // antecedent — so `mi klama .i mi nelci lo nu go'i` resolves the nested
            // go'i to `klama(mi)`, not to this sentence. Descend BEFORE advancing
            // `current`. A SELBRI-position go'i (`sutra go'i` in a tanru) is NOT
            // resolved here — the fail-closed net rejects it (deferred).
            let (relation, terms): (u32, Vec<u32>) = match &ast.sentences[sentence_idx] {
                gerna_ast::Sentence::Simple(b) => (
                    b.relation,
                    b.head_terms.iter().chain(&b.tail_terms).copied().collect(),
                ),
                _ => unreachable!(),
            };
            let mut seen = std::collections::HashSet::new();
            resolve_selbri_go_i(ast, relation, &*current, &mut seen)?;
            for t in terms {
                resolve_sumti_go_i(ast, t, &*current, &mut seen)?;
            }
            // The resolved bridi becomes the antecedent for the next go'i —
            // `mi klama .i do go'i .i go'i` chains the resolved `klama(do)`.
            *current = Some(sentence_idx as u32);
            Ok(())
        }
        gerna_ast::Sentence::Connected((_, left_idx, right_idx)) => {
            resolve_sentence_go_i(ast, left_idx as usize, current)?;
            resolve_sentence_go_i(ast, right_idx as usize, current)?;
            Ok(())
        }
        gerna_ast::Sentence::Prenex((_, body_idx)) => {
            resolve_sentence_go_i(ast, body_idx as usize, current)?;
            Ok(())
        }
    }
}

/// Mutating twin of `selbri_reaches_go_i`: descend a selbri and resolve any
/// nested SENTENCE-position go'i (an abstraction body, `lo nu go'i`). A
/// SELBRI-position go'i (a bare `Root("go'i")` in a tanru, `sutra go'i`) is left
/// unresolved for the fail-closed net (deferred). Reads `current` (never advances
/// it). Clone-then-recurse to dodge the `&mut ast[i]` borrow; `seen` cycle-guards.
fn resolve_selbri_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> Result<(), String> {
    if !seen.insert((1, id)) {
        return Ok(());
    }
    match ast.selbris[id as usize].clone() {
        gerna_ast::Selbri::Root(_) | gerna_ast::Selbri::Compound(_) => {}
        gerna_ast::Selbri::Tanru((m, h)) => {
            resolve_selbri_go_i(ast, m, current, seen)?;
            resolve_selbri_go_i(ast, h, current, seen)?;
        }
        gerna_ast::Selbri::Converted((_, i))
        | gerna_ast::Selbri::Negated(i)
        | gerna_ast::Selbri::Grouped(i) => resolve_selbri_go_i(ast, i, current, seen)?,
        gerna_ast::Selbri::WithArgs((core, args)) => {
            resolve_selbri_go_i(ast, core, current, seen)?;
            for a in args {
                resolve_sumti_go_i(ast, a, current, seen)?;
            }
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            resolve_selbri_go_i(ast, l, current, seen)?;
            resolve_selbri_go_i(ast, r, current, seen)?;
        }
        gerna_ast::Selbri::Abstraction((_, s)) => {
            resolve_nested_sentence_go_i(ast, s, current, seen)?;
        }
    }
    Ok(())
}

/// Mutating twin of `sumti_reaches_go_i`: descend a sumti and resolve any nested
/// SENTENCE-position go'i (a relative-clause body, `poi go'i`). Reads `current`.
fn resolve_sumti_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> Result<(), String> {
    if !seen.insert((2, id)) {
        return Ok(());
    }
    match ast.sumtis[id as usize].clone() {
        gerna_ast::Sumti::Description((_, sid))
        | gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            resolve_selbri_go_i(ast, sid, current, seen)?;
        }
        gerna_ast::Sumti::Tagged((_, i)) => resolve_sumti_go_i(ast, i, current, seen)?,
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            if let gerna_ast::ModalTag::Fio(sid) = mt {
                resolve_selbri_go_i(ast, sid, current, seen)?;
            }
            resolve_sumti_go_i(ast, i, current, seen)?;
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            resolve_sumti_go_i(ast, i, current, seen)?;
            resolve_nested_sentence_go_i(ast, rc.body_sentence, current, seen)?;
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            resolve_sumti_go_i(ast, l, current, seen)?;
            resolve_sumti_go_i(ast, r, current, seen)?;
        }
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => {}
    }
    Ok(())
}

/// Mutating twin of `sentence_reaches_go_i` for a NESTED sentence (abstraction /
/// relative-clause body): resolve its Simple bridi's go'i (reading `current`,
/// never advancing it) and recurse into its selbri + terms (handles
/// `lo nu lo nu go'i`).
fn resolve_nested_sentence_go_i(
    ast: &mut gerna_ast::AstBuffer,
    id: u32,
    current: &Option<u32>,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> Result<(), String> {
    if !seen.insert((0, id)) {
        return Ok(());
    }
    match ast.sentences[id as usize].clone() {
        gerna_ast::Sentence::Simple(_) => {
            resolve_simple_bridi_go_i(ast, id as usize, current)?;
            let (relation, terms): (u32, Vec<u32>) = match &ast.sentences[id as usize] {
                gerna_ast::Sentence::Simple(b) => (
                    b.relation,
                    b.head_terms.iter().chain(&b.tail_terms).copied().collect(),
                ),
                _ => unreachable!(),
            };
            resolve_selbri_go_i(ast, relation, current, seen)?;
            for t in terms {
                resolve_sumti_go_i(ast, t, current, seen)?;
            }
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            resolve_nested_sentence_go_i(ast, l, current, seen)?;
            resolve_nested_sentence_go_i(ast, r, current, seen)?;
        }
        gerna_ast::Sentence::Prenex((_, body)) => {
            resolve_nested_sentence_go_i(ast, body, current, seen)?;
        }
    }
    Ok(())
}

/// Walk all root sentences and resolve any go'i references.
/// Skips snapshot grafting entirely if no go'i is present in the parsed text.
fn resolve_go_i(
    ast: &mut gerna_ast::AstBuffer,
    last_snapshot: &mut Option<BridiSnapshot>,
) -> Result<Option<u32>, String> {
    let has_go_i = ast
        .selbris
        .iter()
        .any(|s| matches!(s, gerna_ast::Selbri::Root(n) if n == "go'i"));
    let mut current: Option<u32> = if has_go_i {
        // Graft from a CLONE: `graft_snapshot` rebases + drains its vecs via
        // `Vec::append`. Without the clone, a second `? go'i` would graft the
        // drained husk, producing an out-of-bounds index → a WASM component
        // trap. Cloning keeps the stored snapshot intact, so go'i is idempotent
        // across calls.
        last_snapshot
            .as_ref()
            .map(|snap| graft_snapshot(ast, &mut snap.clone()))
    } else {
        None
    };
    for i in 0..ast.roots.len() {
        let root_idx = ast.roots[i] as usize;
        resolve_sentence_go_i(ast, root_idx, &mut current)?;
    }
    // Fail-closed net: any go'i still REACHABLE after resolution sits in a
    // SELBRI position the resolver intentionally does not handle yet — a tanru /
    // selbri-position go'i (`sutra go'i`). Top-level, abstraction-body, and
    // relative-clause-body go'i are resolved above; a resolved go'i leaves only an
    // unreachable residual node. Compiling a remaining go'i as a literal predicate
    // is silently wrong, so reject.
    if has_go_i {
        let mut seen = HashSet::new();
        for &root in &ast.roots {
            if sentence_reaches_go_i(ast, root, &mut seen) {
                return Err(
                    "go'i in an unsupported position (a tanru / selbri-position go'i \
                            such as `sutra go'i`) — abstraction and relative-clause go'i \
                            are resolved, but selbri-position go'i is not yet supported"
                        .to_string(),
                );
            }
        }
    }
    Ok(current)
}

/// Read-only reachability walk: does any `Selbri::Root("go'i")` remain REACHABLE
/// from sentence `id`, following the exact edges the compiler will follow? Used
/// to fail closed on go'i the resolver does not descend into. The `(tag, id)`
/// key disambiguates the three index spaces and guards against rel-clause /
/// connective re-entry. Match arms mirror `rebase_*` (the nested-index ground
/// truth) exactly — no `_` wildcard, so a new AST variant forces a revisit.
fn sentence_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((0, id)) {
        return false;
    }
    match &ast.sentences[id as usize] {
        gerna_ast::Sentence::Simple(b) => {
            selbri_reaches_go_i(ast, b.relation, seen)
                || b.head_terms
                    .iter()
                    .chain(&b.tail_terms)
                    .any(|&s| sumti_reaches_go_i(ast, s, seen))
        }
        gerna_ast::Sentence::Connected((_, l, r)) => {
            sentence_reaches_go_i(ast, *l, seen) || sentence_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Sentence::Prenex((_, body)) => sentence_reaches_go_i(ast, *body, seen),
    }
}

fn selbri_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((1, id)) {
        return false;
    }
    match &ast.selbris[id as usize] {
        gerna_ast::Selbri::Root(n) => n == "go'i",
        gerna_ast::Selbri::Compound(_) => false,
        gerna_ast::Selbri::Tanru((m, h)) => {
            selbri_reaches_go_i(ast, *m, seen) || selbri_reaches_go_i(ast, *h, seen)
        }
        gerna_ast::Selbri::Converted((_, i))
        | gerna_ast::Selbri::Negated(i)
        | gerna_ast::Selbri::Grouped(i) => selbri_reaches_go_i(ast, *i, seen),
        gerna_ast::Selbri::WithArgs((core, args)) => {
            selbri_reaches_go_i(ast, *core, seen)
                || args.iter().any(|&a| sumti_reaches_go_i(ast, a, seen))
        }
        gerna_ast::Selbri::Connected((l, _, r)) => {
            selbri_reaches_go_i(ast, *l, seen) || selbri_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Selbri::Abstraction((_, s)) => sentence_reaches_go_i(ast, *s, seen),
    }
}

fn sumti_reaches_go_i(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    seen: &mut std::collections::HashSet<(u8, u32)>,
) -> bool {
    if !seen.insert((2, id)) {
        return false;
    }
    match &ast.sumtis[id as usize] {
        gerna_ast::Sumti::Description((_, sid))
        | gerna_ast::Sumti::QuantifiedDescription((_, _, sid)) => {
            selbri_reaches_go_i(ast, *sid, seen)
        }
        gerna_ast::Sumti::Tagged((_, i)) => sumti_reaches_go_i(ast, *i, seen),
        gerna_ast::Sumti::ModalTagged((mt, i)) => {
            let fio_hit =
                matches!(mt, gerna_ast::ModalTag::Fio(sid) if selbri_reaches_go_i(ast, *sid, seen));
            fio_hit || sumti_reaches_go_i(ast, *i, seen)
        }
        gerna_ast::Sumti::Restricted((i, rc)) => {
            sumti_reaches_go_i(ast, *i, seen) || sentence_reaches_go_i(ast, rc.body_sentence, seen)
        }
        gerna_ast::Sumti::Connected((l, _, _, r)) => {
            sumti_reaches_go_i(ast, *l, seen) || sumti_reaches_go_i(ast, *r, seen)
        }
        gerna_ast::Sumti::ProSumti(_)
        | gerna_ast::Sumti::Name(_)
        | gerna_ast::Sumti::QuotedLiteral(_)
        | gerna_ast::Sumti::Unspecified
        | gerna_ast::Sumti::Number(_) => false,
    }
}

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
) -> Result<(logji_logic::LogicBuffer, Option<BridiSnapshot>, Vec<String>), export_err::NibliError>
{
    let parse_result =
        gerna::parse_text_native(text.to_string()).map_err(convert_pipeline_error)?;

    let parse_warnings: Vec<String> = parse_result
        .errors
        .iter()
        .map(|e| e.message.clone())
        .collect();

    let mut ast = parse_result.buffer;

    if ast.roots.is_empty() && !parse_warnings.is_empty() {
        let first = &parse_result.errors[0];
        return Err(export_err::NibliError::Syntax(export_err::SyntaxDetail {
            message: parse_warnings.join("; "),
            line: first.line,
            column: first.column,
        }));
    }

    let last_bridi_sid =
        resolve_go_i(&mut ast, last_snapshot).map_err(|e| export_err::NibliError::Semantic(e))?;
    let new_snapshot = last_bridi_sid.map(|sid| extract_bridi_snapshot(&ast, sid));

    // Call smuni (converts gerna AST → logic buffer internally)
    let mut buf = smuni::compile_from_gerna_ast(ast).map_err(convert_pipeline_error)?;

    // Transform registered predicates to ComputeNode
    logji::transform_compute_nodes(&mut buf, compute_predicates);

    Ok((buf, new_snapshot, parse_warnings))
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
    /// snapshot update and the parse-warnings abort apply on BOTH paths.
    fn assert_text_inner(
        &self,
        input: String,
        id: Option<u64>,
    ) -> Result<u64, export_err::NibliError> {
        let (buf, new_last, warnings) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        if !warnings.is_empty() {
            return Err(export_err::NibliError::Syntax(export_err::SyntaxDetail {
                message: format!(
                    "Assertion aborted: {} sentence(s) failed to parse: {}",
                    warnings.len(),
                    warnings.join("; ")
                ),
                line: 0,
                column: 0,
            }));
        }
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
        Session {
            kb,
            compute_predicates: RefCell::new(default_compute_predicates()),
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
        let (buf, new_last, _warnings) = compile_pipeline(
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
        let (buf, new_last, _warnings) = compile_pipeline(
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
        let (buf, new_last, _warnings) = compile_pipeline(
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
        let (buf, _, _warnings) = compile_pipeline(
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
        let grafted_root = graft_snapshot(&mut ast, &mut snap);
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
    fn tanru_go_i_still_rejected() {
        // `mi sutra go'i` — a SELBRI-position go'i inside a tanru is the deferred
        // phase-2 case. The resolver does not graft a selbri-position go'i, so the
        // fail-closed net must still reject it (rather than compile a literal
        // `go'i` predicate). Phase-2 guard.
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
        assert!(res.is_err(), "tanru go'i must be rejected, got {res:?}");
        assert!(res.unwrap_err().contains("unsupported position"));
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
        };
        assert!(
            !convert_proof_trace(plain_trace).naf_dependent,
            "a non-negation trace must not be naf_dependent"
        );
    }
}

#[cfg(target_arch = "wasm32")]
bindings::export!(LasnaPipeline with_types_in bindings);
