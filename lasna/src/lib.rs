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
    last_relation: RefCell<Option<SelbriSnapshot>>,
}

/// A self-contained clone of a selbri subtree, storable across calls.
/// All indices are internal to the snapshot's own vecs.
#[derive(Clone)]
struct SelbriSnapshot {
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

fn convert_proof_rule(r: &logji_logic::ProofRule) -> export_logic::ProofRule {
    match r {
        logji_logic::ProofRule::Conjunction => export_logic::ProofRule::Conjunction,
        logji_logic::ProofRule::DisjunctionCheck(s) => {
            export_logic::ProofRule::DisjunctionCheck(s.clone())
        }
        logji_logic::ProofRule::DisjunctionIntro(s) => {
            export_logic::ProofRule::DisjunctionIntro(s.clone())
        }
        logji_logic::ProofRule::Negation => export_logic::ProofRule::Negation,
        logji_logic::ProofRule::ModalPassthrough(s) => {
            export_logic::ProofRule::ModalPassthrough(s.clone())
        }
        logji_logic::ProofRule::ExistsWitness((v, t)) => {
            export_logic::ProofRule::ExistsWitness((v.clone(), convert_logical_term_to_export(t)))
        }
        logji_logic::ProofRule::ExistsFailed => export_logic::ProofRule::ExistsFailed,
        logji_logic::ProofRule::ForallVacuous => export_logic::ProofRule::ForallVacuous,
        logji_logic::ProofRule::ForallVerified(terms) => export_logic::ProofRule::ForallVerified(
            terms.iter().map(convert_logical_term_to_export).collect(),
        ),
        logji_logic::ProofRule::ForallCounterexample(t) => {
            export_logic::ProofRule::ForallCounterexample(convert_logical_term_to_export(t))
        }
        logji_logic::ProofRule::CountResult((expected, actual)) => {
            export_logic::ProofRule::CountResult((*expected, *actual))
        }
        logji_logic::ProofRule::PredicateCheck((m, d)) => {
            export_logic::ProofRule::PredicateCheck((m.clone(), d.clone()))
        }
        logji_logic::ProofRule::ComputeCheck((m, d)) => {
            export_logic::ProofRule::ComputeCheck((m.clone(), d.clone()))
        }
        logji_logic::ProofRule::Asserted(f) => export_logic::ProofRule::Asserted(f.clone()),
        logji_logic::ProofRule::Derived((l, f)) => {
            export_logic::ProofRule::Derived((l.clone(), f.clone()))
        }
        logji_logic::ProofRule::ProofRef(f) => export_logic::ProofRule::ProofRef(f.clone()),
        logji_logic::ProofRule::EqualitySubstitution((o, d, s)) => {
            export_logic::ProofRule::EqualitySubstitution((o.clone(), d.clone(), s.clone()))
        }
        logji_logic::ProofRule::RuleAttemptFailed((l, c)) => {
            export_logic::ProofRule::RuleAttemptFailed((l.clone(), c.clone()))
        }
        logji_logic::ProofRule::PredicateNotFound(p) => {
            export_logic::ProofRule::PredicateNotFound(p.clone())
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

/// Extract the self-contained subtree rooted at `root_id` from `ast`.
fn extract_selbri_snapshot(ast: &gerna_ast::AstBuffer, root_id: u32) -> SelbriSnapshot {
    let mut snap = SelbriSnapshot {
        selbris: Vec::new(),
        sumtis: Vec::new(),
        sentences: Vec::new(),
        root: 0,
    };
    let mut sm = HashMap::new();
    let mut um = HashMap::new();
    let mut tm = HashMap::new();
    snap.root = visit_selbri(ast, root_id, &mut snap, &mut sm, &mut um, &mut tm);
    snap
}

fn visit_selbri(
    ast: &gerna_ast::AstBuffer,
    id: u32,
    snap: &mut SelbriSnapshot,
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
    snap: &mut SelbriSnapshot,
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
    snap: &mut SelbriSnapshot,
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
    };
    snap.sentences[new_id as usize] = mapped;
    new_id
}

/// Graft a snapshot into an existing AstBuffer, consuming it. Returns the new selbri root index.
/// Mutates indices in place then moves nodes via `append` — zero cloning.
fn graft_snapshot(ast: &mut gerna_ast::AstBuffer, snap: &mut SelbriSnapshot) -> u32 {
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
    let root = snap.root + sb;
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
    }
}

/// Resolve go'i references in a single sentence.
fn resolve_sentence_go_i(
    ast: &mut gerna_ast::AstBuffer,
    sentence_idx: usize,
    current: &mut Option<u32>,
) -> Result<(), String> {
    let sentence = ast.sentences[sentence_idx].clone();
    match sentence {
        gerna_ast::Sentence::Simple(mut bridi) => {
            let selbri_id = bridi.relation;
            match &ast.selbris[selbri_id as usize] {
                gerna_ast::Selbri::Root(name) if name == "go'i" => {
                    let resolved_id = current.ok_or_else(|| {
                        "go'i has no antecedent (no previous assertion)".to_string()
                    })?;
                    bridi.relation = resolved_id;
                    ast.sentences[sentence_idx] = gerna_ast::Sentence::Simple(bridi);
                }
                _ => {
                    *current = Some(selbri_id);
                }
            }
            Ok(())
        }
        gerna_ast::Sentence::Connected((_, left_idx, right_idx)) => {
            resolve_sentence_go_i(ast, left_idx as usize, current)?;
            resolve_sentence_go_i(ast, right_idx as usize, current)?;
            Ok(())
        }
    }
}

/// Walk all root sentences and resolve any go'i references.
/// Skips snapshot grafting entirely if no go'i is present in the parsed text.
fn resolve_go_i(
    ast: &mut gerna_ast::AstBuffer,
    last_snapshot: &mut Option<SelbriSnapshot>,
) -> Result<Option<u32>, String> {
    let has_go_i = ast
        .selbris
        .iter()
        .any(|s| matches!(s, gerna_ast::Selbri::Root(n) if n == "go'i"));
    let mut current: Option<u32> = if has_go_i {
        last_snapshot.as_mut().map(|snap| graft_snapshot(ast, snap))
    } else {
        None
    };
    for i in 0..ast.roots.len() {
        let root_idx = ast.roots[i] as usize;
        resolve_sentence_go_i(ast, root_idx, &mut current)?;
    }
    Ok(current)
}

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(
    text: &str,
    last_snapshot: &mut Option<SelbriSnapshot>,
    compute_predicates: &HashSet<String>,
) -> Result<
    (
        logji_logic::LogicBuffer,
        Option<SelbriSnapshot>,
        Vec<String>,
    ),
    export_err::NibliError,
> {
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

    let last_selbri_id =
        resolve_go_i(&mut ast, last_snapshot).map_err(|e| export_err::NibliError::Semantic(e))?;
    let new_snapshot = last_selbri_id.map(|id| extract_selbri_snapshot(&ast, id));

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

impl GuestSession for Session {
    fn new() -> Self {
        // Register compute dispatch so logji can call the host's compute-backend
        logji::register_compute_dispatch(eval_via_host, batch_eval_via_host);
        Session {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: RefCell::new(default_compute_predicates()),
            last_relation: RefCell::new(None),
        }
    }

    fn assert_text(&self, input: String) -> Result<u64, export_err::NibliError> {
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
        let fact_id = self.kb.assert_fact(buf, input).map_err(convert_pipeline_error)?;
        *self.last_relation.borrow_mut() = new_last;
        Ok(fact_id)
    }

    fn query_text(
        &self,
        input: String,
    ) -> Result<export_logic::QueryResult, export_err::NibliError> {
        let (buf, _, _warnings) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        self.kb
            .query_entailment(buf)
            .map(|result| convert_query_result_to_export(&result))
            .map_err(convert_pipeline_error)
    }

    fn query_find_text(
        &self,
        input: String,
    ) -> Result<Vec<Vec<export_logic::WitnessBinding>>, export_err::NibliError> {
        let (buf, _, _warnings) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        let result = self.kb.query_find(buf).map_err(convert_pipeline_error)?;
        Ok(convert_witness_bindings(result))
    }

    fn query_text_with_proof(
        &self,
        input: String,
    ) -> Result<(export_logic::QueryResult, export_logic::ProofTrace), export_err::NibliError> {
        let (buf, _, _warnings) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        let (result, trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(convert_pipeline_error)?;
        Ok((
            convert_query_result_to_export(&result),
            convert_proof_trace(trace),
        ))
    }

    fn compile_debug(&self, input: String) -> Result<String, export_err::NibliError> {
        let (buf, _, _warnings) = compile_pipeline(
            &input,
            &mut self.last_relation.borrow_mut(),
            &self.compute_predicates.borrow(),
        )?;
        Ok(logji::repr::debug_logic(&buf))
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
        *self.last_relation.borrow_mut() = Some(SelbriSnapshot {
            selbris: vec![gerna_ast::Selbri::Root(relation.clone())],
            sumtis: vec![],
            sentences: vec![],
            root: 0,
        });
        let logji_args: Vec<logji_logic::LogicalTerm> =
            args.iter().map(convert_logical_term_from_export).collect();
        let label = format!(":assert {}", relation);
        let nodes = vec![logji_logic::LogicNode::Predicate((relation, logji_args))];
        let buf = logji_logic::LogicBuffer {
            nodes,
            roots: vec![0],
        };
        self.kb.assert_fact(buf, label).map_err(convert_pipeline_error)
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
        let ast = make_ast(
            vec![gerna_ast::Selbri::Root("klama".to_string())],
            0,
            vec![0],
        );
        let snap = extract_selbri_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 1);
        assert_eq!(snap.root, 0);
        assert!(matches!(&snap.selbris[0], gerna_ast::Selbri::Root(n) if n == "klama"));
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
        let snap = extract_selbri_snapshot(&ast, 1);
        assert_eq!(snap.selbris.len(), 2);
        assert!(matches!(
            &snap.selbris[snap.root as usize],
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
        let snap = extract_selbri_snapshot(&ast, 1);
        assert_eq!(snap.selbris.len(), 2);
        assert!(matches!(
            &snap.selbris[snap.root as usize],
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
        let snap = extract_selbri_snapshot(&ast, 2);
        assert_eq!(snap.selbris.len(), 3);
        assert!(
            matches!(&snap.selbris[snap.root as usize], gerna_ast::Selbri::Negated(inner) if {
                matches!(&snap.selbris[*inner as usize], gerna_ast::Selbri::Converted((Conversion::Se, inner2)) if {
                    matches!(&snap.selbris[*inner2 as usize], gerna_ast::Selbri::Root(n) if n == "klama")
                })
            })
        );
    }

    #[test]
    fn test_graft_rebase_indices() {
        let mut ast = gerna_ast::AstBuffer {
            selbris: vec![gerna_ast::Selbri::Root("existing".to_string())],
            sumtis: vec![Sumti::ProSumti("mi".to_string())],
            sentences: vec![],
            roots: vec![],
        };
        let mut snap = SelbriSnapshot {
            selbris: vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Negated(0),
            ],
            sumtis: vec![],
            sentences: vec![],
            root: 1,
        };
        let grafted_root = graft_snapshot(&mut ast, &mut snap);
        assert_eq!(grafted_root, 2);
        assert_eq!(ast.selbris.len(), 3);
        assert!(matches!(&ast.selbris[1], gerna_ast::Selbri::Root(n) if n == "klama"));
        assert!(matches!(&ast.selbris[2], gerna_ast::Selbri::Negated(id) if *id == 1));
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
        let snap = SelbriSnapshot {
            selbris: vec![gerna_ast::Selbri::Root("klama".to_string())],
            sumtis: vec![],
            sentences: vec![],
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
        let snap = SelbriSnapshot {
            selbris: vec![
                gerna_ast::Selbri::Root("klama".to_string()),
                gerna_ast::Selbri::Negated(0),
            ],
            sumtis: vec![],
            sentences: vec![],
            root: 1,
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
}

#[cfg(target_arch = "wasm32")]
bindings::export!(LasnaPipeline with_types_in bindings);
