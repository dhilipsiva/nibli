#[allow(warnings)]
mod bindings;

use bindings::exports::lojban::nesy::engine::{Guest, GuestSession};
use bindings::lojban::nesy::ast_types::{
    AstBuffer, Bridi, ModalTag, RelClause, Selbri, Sentence, Sumti,
};
use bindings::lojban::nesy::error_types::{NibliError, SyntaxDetail};
use bindings::lojban::nesy::logic_types::{
    LogicBuffer, LogicNode, LogicalTerm, ProofTrace, WitnessBinding,
};
use bindings::lojban::nesy::{parser, semantics};
use bindings::lojban::nesy::reasoning::KnowledgeBase;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;

struct EnginePipeline;

pub struct Session {
    kb: KnowledgeBase,
    compute_predicates: RefCell<HashSet<String>>,
    last_relation: RefCell<Option<SelbriSnapshot>>,
}

/// A self-contained clone of a selbri subtree, storable across calls.
/// All indices are internal to the snapshot's own vecs.
#[derive(Clone)]
struct SelbriSnapshot {
    selbris: Vec<Selbri>,
    sumtis: Vec<Sumti>,
    sentences: Vec<Sentence>,
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

// ─── go'i pro-bridi resolution ───

/// Extract the head relation name from a selbri by recursive traversal.
/// Used for `assert_fact` name tracking (not for go'i resolution).
fn extract_head_relation(selbris: &[Selbri], id: usize) -> Option<String> {
    match &selbris[id] {
        Selbri::Root(name) => Some(name.clone()),
        Selbri::Tanru((_, head_id)) => extract_head_relation(selbris, *head_id as usize),
        Selbri::Converted((_, inner)) => extract_head_relation(selbris, *inner as usize),
        Selbri::Negated(inner) => extract_head_relation(selbris, *inner as usize),
        Selbri::Grouped(inner) => extract_head_relation(selbris, *inner as usize),
        Selbri::WithArgs((core, _)) => extract_head_relation(selbris, *core as usize),
        Selbri::Connected((left, _, _)) => extract_head_relation(selbris, *left as usize),
        Selbri::Compound(parts) => parts.last().cloned(),
        Selbri::Abstraction(_) => None,
    }
}

// ─── Selbri snapshot: extract & graft subtrees for cross-call go'i ───

/// Extract the self-contained subtree rooted at `root_id` from `ast`.
/// Walks the transitive closure of selbri → sumti → sentence references,
/// remapping all indices to be internal to the snapshot.
fn extract_selbri_snapshot(ast: &AstBuffer, root_id: u32) -> SelbriSnapshot {
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
    ast: &AstBuffer, id: u32,
    snap: &mut SelbriSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = sm.get(&id) { return mapped; }
    let new_id = snap.selbris.len() as u32;
    sm.insert(id, new_id);
    snap.selbris.push(Selbri::Root(String::new())); // placeholder
    let mapped = match &ast.selbris[id as usize] {
        Selbri::Root(n) => Selbri::Root(n.clone()),
        Selbri::Compound(p) => Selbri::Compound(p.clone()),
        Selbri::Tanru((m, h)) => {
            let nm = visit_selbri(ast, *m, snap, sm, um, tm);
            let nh = visit_selbri(ast, *h, snap, sm, um, tm);
            Selbri::Tanru((nm, nh))
        }
        Selbri::Converted((c, i)) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            Selbri::Converted((*c, ni))
        }
        Selbri::Negated(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            Selbri::Negated(ni)
        }
        Selbri::Grouped(i) => {
            let ni = visit_selbri(ast, *i, snap, sm, um, tm);
            Selbri::Grouped(ni)
        }
        Selbri::WithArgs((core, args)) => {
            let nc = visit_selbri(ast, *core, snap, sm, um, tm);
            let na: Vec<u32> = args.iter().map(|&a| visit_sumti(ast, a, snap, sm, um, tm)).collect();
            Selbri::WithArgs((nc, na))
        }
        Selbri::Connected((l, c, r)) => {
            let nl = visit_selbri(ast, *l, snap, sm, um, tm);
            let nr = visit_selbri(ast, *r, snap, sm, um, tm);
            Selbri::Connected((nl, c.clone(), nr))
        }
        Selbri::Abstraction((k, s)) => {
            let ns = visit_sentence(ast, *s, snap, sm, um, tm);
            Selbri::Abstraction((*k, ns))
        }
    };
    snap.selbris[new_id as usize] = mapped;
    new_id
}

fn visit_sumti(
    ast: &AstBuffer, id: u32,
    snap: &mut SelbriSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = um.get(&id) { return mapped; }
    let new_id = snap.sumtis.len() as u32;
    um.insert(id, new_id);
    snap.sumtis.push(Sumti::Unspecified); // placeholder
    let mapped = match &ast.sumtis[id as usize] {
        Sumti::ProSumti(s) => Sumti::ProSumti(s.clone()),
        Sumti::Description((g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            Sumti::Description((*g, ns))
        }
        Sumti::Name(s) => Sumti::Name(s.clone()),
        Sumti::QuotedLiteral(s) => Sumti::QuotedLiteral(s.clone()),
        Sumti::Unspecified => Sumti::Unspecified,
        Sumti::Tagged((t, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            Sumti::Tagged((*t, ni))
        }
        Sumti::ModalTagged((mt, inner)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let nmt = match mt {
                ModalTag::Fixed(b) => ModalTag::Fixed(*b),
                ModalTag::Fio(sid) => {
                    let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
                    ModalTag::Fio(ns)
                }
            };
            Sumti::ModalTagged((nmt, ni))
        }
        Sumti::Restricted((inner, rc)) => {
            let ni = visit_sumti(ast, *inner, snap, sm, um, tm);
            let ns = visit_sentence(ast, rc.body_sentence, snap, sm, um, tm);
            Sumti::Restricted((ni, RelClause { kind: rc.kind, body_sentence: ns }))
        }
        Sumti::Number(n) => Sumti::Number(*n),
        Sumti::Connected((l, c, neg, r)) => {
            let nl = visit_sumti(ast, *l, snap, sm, um, tm);
            let nr = visit_sumti(ast, *r, snap, sm, um, tm);
            Sumti::Connected((nl, c.clone(), *neg, nr))
        }
        Sumti::QuantifiedDescription((count, g, sid)) => {
            let ns = visit_selbri(ast, *sid, snap, sm, um, tm);
            Sumti::QuantifiedDescription((*count, *g, ns))
        }
    };
    snap.sumtis[new_id as usize] = mapped;
    new_id
}

fn visit_sentence(
    ast: &AstBuffer, id: u32,
    snap: &mut SelbriSnapshot,
    sm: &mut HashMap<u32, u32>,
    um: &mut HashMap<u32, u32>,
    tm: &mut HashMap<u32, u32>,
) -> u32 {
    if let Some(&mapped) = tm.get(&id) { return mapped; }
    let new_id = snap.sentences.len() as u32;
    tm.insert(id, new_id);
    // placeholder
    snap.sentences.push(Sentence::Simple(Bridi {
        relation: 0, head_terms: vec![], tail_terms: vec![],
        negated: false, tense: None, attitudinal: None,
    }));
    let mapped = match &ast.sentences[id as usize] {
        Sentence::Simple(b) => {
            let nr = visit_selbri(ast, b.relation, snap, sm, um, tm);
            let nh: Vec<u32> = b.head_terms.iter().map(|&s| visit_sumti(ast, s, snap, sm, um, tm)).collect();
            let nt: Vec<u32> = b.tail_terms.iter().map(|&s| visit_sumti(ast, s, snap, sm, um, tm)).collect();
            Sentence::Simple(Bridi {
                relation: nr, head_terms: nh, tail_terms: nt,
                negated: b.negated, tense: b.tense, attitudinal: b.attitudinal,
            })
        }
        Sentence::Connected((c, l, r)) => {
            let nl = visit_sentence(ast, *l, snap, sm, um, tm);
            let nr = visit_sentence(ast, *r, snap, sm, um, tm);
            Sentence::Connected((c.clone(), nl, nr))
        }
    };
    snap.sentences[new_id as usize] = mapped;
    new_id
}

/// Graft a snapshot into an existing AstBuffer. Returns the new selbri root index.
fn graft_snapshot(ast: &mut AstBuffer, snap: &SelbriSnapshot) -> u32 {
    let sb = ast.selbris.len() as u32;
    let ub = ast.sumtis.len() as u32;
    let tb = ast.sentences.len() as u32;
    for s in &snap.selbris {
        ast.selbris.push(rebase_selbri(s, sb, ub, tb));
    }
    for s in &snap.sumtis {
        ast.sumtis.push(rebase_sumti(s, sb, ub, tb));
    }
    for s in &snap.sentences {
        ast.sentences.push(rebase_sentence(s, sb, ub, tb));
    }
    snap.root + sb
}

fn rebase_selbri(s: &Selbri, sb: u32, ub: u32, tb: u32) -> Selbri {
    match s {
        Selbri::Root(n) => Selbri::Root(n.clone()),
        Selbri::Compound(p) => Selbri::Compound(p.clone()),
        Selbri::Tanru((m, h)) => Selbri::Tanru((m + sb, h + sb)),
        Selbri::Converted((c, i)) => Selbri::Converted((*c, i + sb)),
        Selbri::Negated(i) => Selbri::Negated(i + sb),
        Selbri::Grouped(i) => Selbri::Grouped(i + sb),
        Selbri::WithArgs((core, args)) => {
            Selbri::WithArgs((core + sb, args.iter().map(|a| a + ub).collect()))
        }
        Selbri::Connected((l, c, r)) => Selbri::Connected((l + sb, c.clone(), r + sb)),
        Selbri::Abstraction((k, sent)) => Selbri::Abstraction((*k, sent + tb)),
    }
}

fn rebase_sumti(s: &Sumti, sb: u32, ub: u32, tb: u32) -> Sumti {
    match s {
        Sumti::ProSumti(v) => Sumti::ProSumti(v.clone()),
        Sumti::Description((g, sid)) => Sumti::Description((*g, sid + sb)),
        Sumti::Name(v) => Sumti::Name(v.clone()),
        Sumti::QuotedLiteral(v) => Sumti::QuotedLiteral(v.clone()),
        Sumti::Unspecified => Sumti::Unspecified,
        Sumti::Tagged((t, i)) => Sumti::Tagged((*t, i + ub)),
        Sumti::ModalTagged((mt, i)) => {
            let nmt = match mt {
                ModalTag::Fixed(b) => ModalTag::Fixed(*b),
                ModalTag::Fio(sid) => ModalTag::Fio(sid + sb),
            };
            Sumti::ModalTagged((nmt, i + ub))
        }
        Sumti::Restricted((i, rc)) => {
            Sumti::Restricted((i + ub, RelClause { kind: rc.kind, body_sentence: rc.body_sentence + tb }))
        }
        Sumti::Number(n) => Sumti::Number(*n),
        Sumti::Connected((l, c, neg, r)) => Sumti::Connected((l + ub, c.clone(), *neg, r + ub)),
        Sumti::QuantifiedDescription((count, g, sid)) => Sumti::QuantifiedDescription((*count, *g, sid + sb)),
    }
}

fn rebase_sentence(s: &Sentence, sb: u32, ub: u32, tb: u32) -> Sentence {
    match s {
        Sentence::Simple(b) => Sentence::Simple(Bridi {
            relation: b.relation + sb,
            head_terms: b.head_terms.iter().map(|i| i + ub).collect(),
            tail_terms: b.tail_terms.iter().map(|i| i + ub).collect(),
            negated: b.negated, tense: b.tense, attitudinal: b.attitudinal,
        }),
        Sentence::Connected((c, l, r)) => Sentence::Connected((c.clone(), l + tb, r + tb)),
    }
}

/// Resolve go'i references in a single sentence.
/// `current` tracks the last selbri index within the current AstBuffer.
fn resolve_sentence_go_i(
    ast: &mut AstBuffer,
    sentence_idx: usize,
    current: &mut Option<u32>,
) -> Result<(), String> {
    let sentence = ast.sentences[sentence_idx].clone();
    match sentence {
        Sentence::Simple(mut bridi) => {
            let selbri_id = bridi.relation;
            match &ast.selbris[selbri_id as usize] {
                Selbri::Root(name) if name == "go'i" => {
                    let resolved_id = current
                        .ok_or_else(|| "go'i has no antecedent (no previous assertion)".to_string())?;
                    // Repoint bridi.relation to the full antecedent selbri
                    bridi.relation = resolved_id;
                    ast.sentences[sentence_idx] = Sentence::Simple(bridi);
                }
                _ => {
                    *current = Some(selbri_id);
                }
            }
            Ok(())
        }
        Sentence::Connected((_, left_idx, right_idx)) => {
            resolve_sentence_go_i(ast, left_idx as usize, current)?;
            resolve_sentence_go_i(ast, right_idx as usize, current)?;
            Ok(())
        }
    }
}

/// Walk all root sentences and resolve any go'i references.
/// Returns the selbri index of the last relation (for snapshot extraction).
fn resolve_go_i(
    ast: &mut AstBuffer,
    last_snapshot: &Option<SelbriSnapshot>,
) -> Result<Option<u32>, String> {
    // Graft cross-call snapshot into current buffer if present
    let mut current: Option<u32> = last_snapshot.as_ref().map(|snap| graft_snapshot(ast, snap));
    for i in 0..ast.roots.len() {
        let root_idx = ast.roots[i] as usize;
        resolve_sentence_go_i(ast, root_idx, &mut current)?;
    }
    Ok(current)
}

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(
    text: &str,
    last_snapshot: &Option<SelbriSnapshot>,
) -> Result<(LogicBuffer, Option<SelbriSnapshot>, Vec<String>), NibliError> {
    let parse_result = parser::parse_text(text)?;

    // Collect per-sentence parse errors as warning strings
    let parse_warnings: Vec<String> = parse_result
        .errors
        .iter()
        .map(|e| e.message.clone())
        .collect();

    let mut ast = parse_result.buffer;

    // If ALL sentences failed, report error with first error's location
    if ast.roots.is_empty() && !parse_warnings.is_empty() {
        let first = &parse_result.errors[0];
        return Err(NibliError::Syntax(SyntaxDetail {
            message: parse_warnings.join("; "),
            line: first.line,
            column: first.column,
        }));
    }

    let last_selbri_id = resolve_go_i(&mut ast, last_snapshot)
        .map_err(|e| NibliError::Semantic(e))?;
    let new_snapshot = last_selbri_id.map(|id| extract_selbri_snapshot(&ast, id));
    let buf = semantics::compile_buffer(&ast)?;
    Ok((buf, new_snapshot, parse_warnings))
}

/// Transform Predicate nodes into ComputeNode for registered compute predicates.
fn transform_compute_nodes(buf: &mut LogicBuffer, compute_preds: &HashSet<String>) {
    let nodes = std::mem::take(&mut buf.nodes);
    buf.nodes = nodes
        .into_iter()
        .map(|node| match &node {
            LogicNode::Predicate((rel, _)) if compute_preds.contains(rel.as_str()) => {
                let LogicNode::Predicate(inner) = node else {
                    unreachable!()
                };
                LogicNode::ComputeNode(inner)
            }
            _ => node,
        })
        .collect();
}

fn debug_sexp(buffer: &LogicBuffer) -> String {
    buffer
        .roots
        .iter()
        .map(|&id| reconstruct_sexp(buffer, id))
        .collect::<Vec<_>>()
        .join("\n")
}

// ─── WIT exports ───

impl Guest for EnginePipeline {
    type Session = Session;
}

impl GuestSession for Session {
    fn new() -> Self {
        Session {
            kb: KnowledgeBase::new(),
            compute_predicates: RefCell::new(default_compute_predicates()),
            last_relation: RefCell::new(None),
        }
    }

    fn assert_text(&self, input: String) -> Result<u32, NibliError> {
        let (mut buf, new_last, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb.assert_fact(&buf)?;
        *self.last_relation.borrow_mut() = new_last;
        Ok(buf.roots.len() as u32)
    }

    fn query_text(&self, input: String) -> Result<bool, NibliError> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb.query_entailment(&buf)
    }

    fn query_find_text(&self, input: String) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb.query_find(&buf)
    }

    fn query_text_with_proof(&self, input: String) -> Result<(bool, ProofTrace), NibliError> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb.query_entailment_with_proof(&buf)
    }

    fn compile_debug(&self, input: String) -> Result<String, NibliError> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        Ok(debug_sexp(&buf))
    }

    fn reset_kb(&self) -> Result<(), NibliError> {
        *self.last_relation.borrow_mut() = None;
        self.kb.reset()
    }

    fn register_compute_predicate(&self, name: String) {
        self.compute_predicates.borrow_mut().insert(name);
    }

    fn assert_fact(&self, relation: String, args: Vec<LogicalTerm>) -> Result<(), NibliError> {
        // Store a minimal snapshot for go'i: just a Root selbri
        *self.last_relation.borrow_mut() = Some(SelbriSnapshot {
            selbris: vec![Selbri::Root(relation.clone())],
            sumtis: vec![],
            sentences: vec![],
            root: 0,
        });
        let nodes = vec![LogicNode::Predicate((relation, args))];
        let buf = LogicBuffer {
            nodes,
            roots: vec![0],
        };
        self.kb.assert_fact(&buf)
    }
}

// ─── S-expression reconstruction ───

use std::fmt::Write;

fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    let mut out = String::with_capacity(256);
    write_sexp(&mut out, buffer, node_id);
    out
}

fn write_sexp(out: &mut String, buffer: &LogicBuffer, node_id: u32) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            out.push_str("(Pred \"");
            out.push_str(rel);
            out.push_str("\" ");
            write_term_list(out, args);
            out.push(')');
        }
        LogicNode::ComputeNode((rel, args)) => {
            out.push_str("(Compute \"");
            out.push_str(rel);
            out.push_str("\" ");
            write_term_list(out, args);
            out.push(')');
        }
        LogicNode::AndNode((l, r)) => {
            out.push_str("(And ");
            write_sexp(out, buffer, *l);
            out.push(' ');
            write_sexp(out, buffer, *r);
            out.push(')');
        }
        LogicNode::OrNode((l, r)) => {
            out.push_str("(Or ");
            write_sexp(out, buffer, *l);
            out.push(' ');
            write_sexp(out, buffer, *r);
            out.push(')');
        }
        LogicNode::NotNode(inner) => {
            out.push_str("(Not ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::ExistsNode((v, body)) => {
            out.push_str("(Exists \"");
            out.push_str(v);
            out.push_str("\" ");
            write_sexp(out, buffer, *body);
            out.push(')');
        }
        LogicNode::ForAllNode((v, body)) => {
            out.push_str("(ForAll \"");
            out.push_str(v);
            out.push_str("\" ");
            write_sexp(out, buffer, *body);
            out.push(')');
        }
        LogicNode::PastNode(inner) => {
            out.push_str("(Past ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::PresentNode(inner) => {
            out.push_str("(Present ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::FutureNode(inner) => {
            out.push_str("(Future ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::ObligatoryNode(inner) => {
            out.push_str("(Obligatory ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::PermittedNode(inner) => {
            out.push_str("(Permitted ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::CountNode((v, count, body)) => {
            out.push_str("(Count \"");
            out.push_str(v);
            out.push_str("\" ");
            let _ = write!(out, "{}", count);
            out.push(' ');
            write_sexp(out, buffer, *body);
            out.push(')');
        }
    }
}

fn write_term_list(out: &mut String, args: &[LogicalTerm]) {
    if args.is_empty() {
        out.push_str("(Nil)");
        return;
    }
    out.push_str("(Cons ");
    write_term(out, &args[0]);
    out.push(' ');
    write_term_list(out, &args[1..]);
    out.push(')');
}

fn write_term(out: &mut String, term: &LogicalTerm) {
    match term {
        LogicalTerm::Variable(v) => {
            out.push_str("(Var \"");
            out.push_str(v);
            out.push_str("\")");
        }
        LogicalTerm::Constant(c) => {
            out.push_str("(Const \"");
            out.push_str(c);
            out.push_str("\")");
        }
        LogicalTerm::Description(d) => {
            out.push_str("(Desc \"");
            out.push_str(d);
            out.push_str("\")");
        }
        LogicalTerm::Unspecified => out.push_str("(Zoe)"),
        LogicalTerm::Number(n) => {
            let _ = write!(out, "(Num {})", n);
        }
    }
}

// ─── Tests ───

#[cfg(test)]
mod tests {
    use super::*;
    use bindings::lojban::nesy::ast_types::{Bridi, Conversion, Sumti};

    // Helper: build a minimal AstBuffer with a single simple sentence
    fn make_ast(
        selbris: Vec<Selbri>,
        bridi_relation: u32,
        head_terms: Vec<u32>,
    ) -> AstBuffer {
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
        AstBuffer {
            selbris,
            sumtis,
            sentences: vec![Sentence::Simple(bridi)],
            roots: vec![0],
        }
    }

    /// Helper: build a two-sentence AstBuffer where sentence 1 has `selbris_1`
    /// and sentence 2 has go'i with the given head_terms.
    fn make_two_sentence_ast(
        mut selbris: Vec<Selbri>,
        first_relation: u32,
    ) -> AstBuffer {
        let go_i_id = selbris.len() as u32;
        selbris.push(Selbri::Root("go'i".to_string()));
        AstBuffer {
            selbris,
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),
                Sumti::ProSumti("do".to_string()),
            ],
            sentences: vec![
                Sentence::Simple(Bridi {
                    relation: first_relation,
                    head_terms: vec![0],
                    tail_terms: vec![],
                    negated: false, tense: None, attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    relation: go_i_id,
                    head_terms: vec![1],
                    tail_terms: vec![],
                    negated: false, tense: None, attitudinal: None,
                }),
            ],
            roots: vec![0, 1],
        }
    }

    /// Get the selbri id that a sentence's bridi.relation points to.
    fn bridi_relation(ast: &AstBuffer, sentence_idx: usize) -> u32 {
        match &ast.sentences[sentence_idx] {
            Sentence::Simple(b) => b.relation,
            _ => panic!("expected Simple"),
        }
    }

    // ─── extract_head_relation tests ───

    #[test]
    fn test_extract_head_relation_root() {
        let selbris = vec![Selbri::Root("klama".to_string())];
        assert_eq!(extract_head_relation(&selbris, 0), Some("klama".to_string()));
    }

    #[test]
    fn test_extract_head_relation_tanru() {
        let selbris = vec![
            Selbri::Root("barda".to_string()),
            Selbri::Root("klama".to_string()),
            Selbri::Tanru((0, 1)),
        ];
        assert_eq!(extract_head_relation(&selbris, 2), Some("klama".to_string()));
    }

    #[test]
    fn test_extract_head_relation_negated() {
        let selbris = vec![
            Selbri::Root("klama".to_string()),
            Selbri::Negated(0),
        ];
        assert_eq!(extract_head_relation(&selbris, 1), Some("klama".to_string()));
    }

    #[test]
    fn test_extract_head_relation_converted() {
        let selbris = vec![
            Selbri::Root("klama".to_string()),
            Selbri::Converted((Conversion::Se, 0)),
        ];
        assert_eq!(extract_head_relation(&selbris, 1), Some("klama".to_string()));
    }

    // ─── Snapshot extract & graft tests ───

    #[test]
    fn test_snapshot_root() {
        let ast = make_ast(vec![Selbri::Root("klama".to_string())], 0, vec![0]);
        let snap = extract_selbri_snapshot(&ast, 0);
        assert_eq!(snap.selbris.len(), 1);
        assert_eq!(snap.root, 0);
        assert!(matches!(&snap.selbris[0], Selbri::Root(n) if n == "klama"));
    }

    #[test]
    fn test_snapshot_negated() {
        let ast = make_ast(
            vec![Selbri::Root("klama".to_string()), Selbri::Negated(0)],
            1, vec![0],
        );
        let snap = extract_selbri_snapshot(&ast, 1);
        assert_eq!(snap.selbris.len(), 2);
        // Root should be Negated pointing to the inner Root
        assert!(matches!(&snap.selbris[snap.root as usize], Selbri::Negated(_)));
    }

    #[test]
    fn test_snapshot_converted() {
        let ast = make_ast(
            vec![Selbri::Root("prami".to_string()), Selbri::Converted((Conversion::Se, 0))],
            1, vec![0],
        );
        let snap = extract_selbri_snapshot(&ast, 1);
        assert_eq!(snap.selbris.len(), 2);
        assert!(matches!(&snap.selbris[snap.root as usize], Selbri::Converted((Conversion::Se, _))));
    }

    #[test]
    fn test_snapshot_negated_converted() {
        // na se klama → Negated(Converted(Se, Root("klama")))
        let ast = make_ast(
            vec![
                Selbri::Root("klama".to_string()),        // 0
                Selbri::Converted((Conversion::Se, 0)),   // 1
                Selbri::Negated(1),                        // 2
            ],
            2, vec![0],
        );
        let snap = extract_selbri_snapshot(&ast, 2);
        assert_eq!(snap.selbris.len(), 3);
        // Walk: root → Negated → Converted → Root
        assert!(matches!(&snap.selbris[snap.root as usize], Selbri::Negated(inner) if {
            matches!(&snap.selbris[*inner as usize], Selbri::Converted((Conversion::Se, inner2)) if {
                matches!(&snap.selbris[*inner2 as usize], Selbri::Root(n) if n == "klama")
            })
        }));
    }

    #[test]
    fn test_graft_rebase_indices() {
        // Create a buffer with existing entries
        let mut ast = AstBuffer {
            selbris: vec![Selbri::Root("existing".to_string())],
            sumtis: vec![Sumti::ProSumti("mi".to_string())],
            sentences: vec![],
            roots: vec![],
        };
        // Snapshot: Negated(Root("klama"))
        let snap = SelbriSnapshot {
            selbris: vec![Selbri::Root("klama".to_string()), Selbri::Negated(0)],
            sumtis: vec![],
            sentences: vec![],
            root: 1,
        };
        let grafted_root = graft_snapshot(&mut ast, &snap);
        // Base offset = 1 (one existing selbri)
        assert_eq!(grafted_root, 2); // snap.root(1) + base(1)
        assert_eq!(ast.selbris.len(), 3);
        assert!(matches!(&ast.selbris[1], Selbri::Root(n) if n == "klama"));
        assert!(matches!(&ast.selbris[2], Selbri::Negated(id) if *id == 1));
    }

    // ─── go'i resolution tests (within-call) ───

    #[test]
    fn test_resolve_go_i_basic_root() {
        // Sentence 1: klama, Sentence 2: go'i → repoints to klama
        let mut ast = make_two_sentence_ast(
            vec![Selbri::Root("klama".to_string())],
            0,
        );
        let result = resolve_go_i(&mut ast, &None).unwrap();
        // go'i sentence should now point to the klama selbri
        assert_eq!(bridi_relation(&ast, 1), 0);
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_negation() {
        // THE BUG FIX: "na klama" then "go'i" should preserve negation
        let mut ast = make_two_sentence_ast(
            vec![
                Selbri::Root("klama".to_string()),  // 0
                Selbri::Negated(0),                  // 1
            ],
            1, // first sentence uses Negated(Root("klama"))
        );
        let result = resolve_go_i(&mut ast, &None).unwrap();
        // go'i should point to the Negated selbri (index 1), NOT bare Root
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 1);
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Negated(inner) if {
            matches!(&ast.selbris[*inner as usize], Selbri::Root(n) if n == "klama")
        }));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_conversion() {
        // "se prami" then "go'i" → should preserve se-conversion
        let mut ast = make_two_sentence_ast(
            vec![
                Selbri::Root("prami".to_string()),          // 0
                Selbri::Converted((Conversion::Se, 0)),     // 1
            ],
            1,
        );
        let result = resolve_go_i(&mut ast, &None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 1);
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Converted((Conversion::Se, _))));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_negated_conversion() {
        // "na se klama" then "go'i" → Negated(Converted(Se, Root("klama")))
        let mut ast = make_two_sentence_ast(
            vec![
                Selbri::Root("klama".to_string()),        // 0
                Selbri::Converted((Conversion::Se, 0)),   // 1
                Selbri::Negated(1),                        // 2
            ],
            2,
        );
        let result = resolve_go_i(&mut ast, &None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 2);
        // Verify full chain: Negated → Converted(Se) → Root("klama")
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Negated(_)));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_preserves_tanru() {
        // "sutra klama" then "go'i" → Tanru(Root("sutra"), Root("klama"))
        let mut ast = make_two_sentence_ast(
            vec![
                Selbri::Root("sutra".to_string()),  // 0
                Selbri::Root("klama".to_string()),  // 1
                Selbri::Tanru((0, 1)),              // 2
            ],
            2,
        );
        let result = resolve_go_i(&mut ast, &None).unwrap();
        let go_i_rel = bridi_relation(&ast, 1);
        assert_eq!(go_i_rel, 2);
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Tanru((0, 1))));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_no_antecedent() {
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0, vec![0],
        );
        let result = resolve_go_i(&mut ast, &None);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("no antecedent"));
    }

    // ─── go'i resolution tests (cross-call via snapshot) ───

    #[test]
    fn test_resolve_go_i_cross_call_root() {
        // Previous call had "klama", new call has just "go'i"
        let snap = SelbriSnapshot {
            selbris: vec![Selbri::Root("klama".to_string())],
            sumtis: vec![], sentences: vec![], root: 0,
        };
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0, vec![0],
        );
        let result = resolve_go_i(&mut ast, &Some(snap)).unwrap();
        // go'i should have been repointed to the grafted "klama"
        let go_i_rel = bridi_relation(&ast, 0);
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Root(n) if n == "klama"));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_cross_call_negated() {
        // Previous call had "na klama" → snapshot preserves Negated
        let snap = SelbriSnapshot {
            selbris: vec![Selbri::Root("klama".to_string()), Selbri::Negated(0)],
            sumtis: vec![], sentences: vec![], root: 1,
        };
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0, vec![0],
        );
        let result = resolve_go_i(&mut ast, &Some(snap)).unwrap();
        let go_i_rel = bridi_relation(&ast, 0);
        // Should be Negated, not bare Root
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Negated(inner) if {
            matches!(&ast.selbris[*inner as usize], Selbri::Root(n) if n == "klama")
        }));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_cross_call_se_converted() {
        // Previous call had "se prami"
        let snap = SelbriSnapshot {
            selbris: vec![
                Selbri::Root("prami".to_string()),
                Selbri::Converted((Conversion::Se, 0)),
            ],
            sumtis: vec![], sentences: vec![], root: 1,
        };
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0, vec![0],
        );
        let result = resolve_go_i(&mut ast, &Some(snap)).unwrap();
        let go_i_rel = bridi_relation(&ast, 0);
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Converted((Conversion::Se, inner)) if {
            matches!(&ast.selbris[*inner as usize], Selbri::Root(n) if n == "prami")
        }));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_cross_call_na_se() {
        // Previous call had "na se klama"
        let snap = SelbriSnapshot {
            selbris: vec![
                Selbri::Root("klama".to_string()),
                Selbri::Converted((Conversion::Se, 0)),
                Selbri::Negated(1),
            ],
            sumtis: vec![], sentences: vec![], root: 2,
        };
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0, vec![0],
        );
        let result = resolve_go_i(&mut ast, &Some(snap)).unwrap();
        let go_i_rel = bridi_relation(&ast, 0);
        // Full chain: Negated → Converted(Se) → Root("klama")
        assert!(matches!(&ast.selbris[go_i_rel as usize], Selbri::Negated(_)));
        assert!(result.is_some());
    }

    #[test]
    fn test_resolve_go_i_multi_sentence_within_call() {
        // Three sentences: klama, go'i, prami — go'i resolves to klama,
        // then prami becomes the new last relation
        let mut ast = AstBuffer {
            selbris: vec![
                Selbri::Root("klama".to_string()),  // 0
                Selbri::Root("go'i".to_string()),   // 1
                Selbri::Root("prami".to_string()),  // 2
            ],
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),
                Sumti::ProSumti("do".to_string()),
                Sumti::ProSumti("ko'a".to_string()),
            ],
            sentences: vec![
                Sentence::Simple(Bridi {
                    relation: 0, head_terms: vec![0], tail_terms: vec![],
                    negated: false, tense: None, attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    relation: 1, head_terms: vec![1], tail_terms: vec![],
                    negated: false, tense: None, attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    relation: 2, head_terms: vec![2], tail_terms: vec![],
                    negated: false, tense: None, attitudinal: None,
                }),
            ],
            roots: vec![0, 1, 2],
        };
        let result = resolve_go_i(&mut ast, &None).unwrap();
        // go'i (sentence 1) should point to klama (selbri 0)
        assert_eq!(bridi_relation(&ast, 1), 0);
        // Last relation should be prami (selbri 2)
        assert_eq!(result, Some(2));
    }

    #[test]
    fn test_snapshot_roundtrip_extract_graft() {
        // Extract from one buffer, graft into another, verify structure
        let src = make_ast(
            vec![
                Selbri::Root("klama".to_string()),        // 0
                Selbri::Converted((Conversion::Se, 0)),   // 1
                Selbri::Negated(1),                        // 2
            ],
            2, vec![0],
        );
        let snap = extract_selbri_snapshot(&src, 2);

        // Graft into a fresh buffer with some pre-existing entries
        let mut dst = AstBuffer {
            selbris: vec![Selbri::Root("other".to_string())],
            sumtis: vec![],
            sentences: vec![],
            roots: vec![],
        };
        let new_root = graft_snapshot(&mut dst, &snap);
        // dst.selbris: [Root("other"), Root("klama"), Converted(Se, 1), Negated(2)]
        assert_eq!(dst.selbris.len(), 4);
        assert!(matches!(&dst.selbris[new_root as usize], Selbri::Negated(inner) if {
            matches!(&dst.selbris[*inner as usize], Selbri::Converted((Conversion::Se, inner2)) if {
                matches!(&dst.selbris[*inner2 as usize], Selbri::Root(n) if n == "klama")
            })
        }));
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
