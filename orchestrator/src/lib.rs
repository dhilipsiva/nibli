#[allow(warnings)]
mod bindings;

use bindings::exports::lojban::nesy::engine::{Guest, GuestSession};
use bindings::lojban::nesy::ast_types::{AstBuffer, Selbri, Sentence};
use bindings::lojban::nesy::logic_types::{
    LogicBuffer, LogicNode, LogicalTerm, ProofTrace, WitnessBinding,
};
use bindings::lojban::nesy::{parser, semantics};
use bindings::lojban::nesy::reasoning::KnowledgeBase;

use std::cell::RefCell;
use std::collections::HashSet;

struct EnginePipeline;

pub struct Session {
    kb: KnowledgeBase,
    compute_predicates: RefCell<HashSet<String>>,
    last_relation: RefCell<Option<String>>,
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

/// Resolve go'i references in a single sentence (recursive for connected sentences).
fn resolve_sentence_go_i(
    ast: &mut AstBuffer,
    sentence_idx: usize,
    current: &mut Option<String>,
) -> Result<(), String> {
    // Clone the sentence to avoid borrow conflicts during mutation.
    let sentence = ast.sentences[sentence_idx].clone();
    match sentence {
        Sentence::Simple(bridi) => {
            let selbri_id = bridi.relation as usize;
            match &ast.selbris[selbri_id] {
                Selbri::Root(name) if name == "go'i" => {
                    let resolved = current
                        .as_ref()
                        .ok_or_else(|| "go'i has no antecedent (no previous assertion)".to_string())?;
                    ast.selbris[selbri_id] = Selbri::Root(resolved.clone());
                }
                _ => {
                    if let Some(rel) = extract_head_relation(&ast.selbris, selbri_id) {
                        *current = Some(rel);
                    }
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
/// Returns the updated last relation for cross-call tracking.
fn resolve_go_i(
    ast: &mut AstBuffer,
    last_relation: &Option<String>,
) -> Result<Option<String>, String> {
    let mut current = last_relation.clone();
    for i in 0..ast.roots.len() {
        let root_idx = ast.roots[i] as usize;
        resolve_sentence_go_i(ast, root_idx, &mut current)?;
    }
    Ok(current)
}

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(
    text: &str,
    last_relation: &Option<String>,
) -> Result<(LogicBuffer, Option<String>, Vec<String>), String> {
    let parse_result = parser::parse_text(text).map_err(|e| format!("Parse: {}", e))?;

    // Collect per-sentence parse errors as warning strings
    let parse_warnings: Vec<String> = parse_result
        .errors
        .iter()
        .map(|e| e.message.clone())
        .collect();

    let mut ast = parse_result.buffer;

    // If ALL sentences failed, report error
    if ast.roots.is_empty() && !parse_warnings.is_empty() {
        return Err(parse_warnings.join("; "));
    }

    let new_last = resolve_go_i(&mut ast, last_relation)
        .map_err(|e| format!("Resolution: {}", e))?;
    let buf = semantics::compile_buffer(&ast).map_err(|e| format!("Semantics: {}", e))?;
    Ok((buf, new_last, parse_warnings))
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

    fn assert_text(&self, input: String) -> Result<u32, String> {
        let (mut buf, new_last, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .assert_fact(&buf)
            .map_err(|e| format!("Reasoning: {}", e))?;
        // Update last_relation after successful assertion
        *self.last_relation.borrow_mut() = new_last;
        Ok(buf.roots.len() as u32)
    }

    fn query_text(&self, input: String) -> Result<bool, String> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        // Don't update last_relation for queries (read-only)
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .query_entailment(&buf)
            .map_err(|e| format!("Reasoning: {}", e))
    }

    fn query_find_text(&self, input: String) -> Result<Vec<Vec<WitnessBinding>>, String> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        // Don't update last_relation for queries (read-only)
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .query_find(&buf)
            .map_err(|e| format!("Reasoning: {}", e))
    }

    fn query_text_with_proof(&self, input: String) -> Result<(bool, ProofTrace), String> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        // Don't update last_relation for queries (read-only)
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .query_entailment_with_proof(&buf)
            .map_err(|e| format!("Reasoning: {}", e))
    }

    fn compile_debug(&self, input: String) -> Result<String, String> {
        let (mut buf, _, _warnings) =
            compile_pipeline(&input, &self.last_relation.borrow())?;
        // Don't update last_relation for debug (read-only)
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        Ok(debug_sexp(&buf))
    }

    fn reset_kb(&self) -> Result<(), String> {
        *self.last_relation.borrow_mut() = None;
        self.kb.reset().map_err(|e| format!("Reset: {}", e))
    }

    fn register_compute_predicate(&self, name: String) {
        self.compute_predicates.borrow_mut().insert(name);
    }

    fn assert_fact(&self, relation: String, args: Vec<LogicalTerm>) -> Result<(), String> {
        // Direct fact assertion: update last_relation to the asserted relation
        *self.last_relation.borrow_mut() = Some(relation.clone());
        let nodes = vec![LogicNode::Predicate((relation, args))];
        let buf = LogicBuffer {
            nodes,
            roots: vec![0],
        };
        self.kb
            .assert_fact(&buf)
            .map_err(|e| format!("Reasoning: {}", e))
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

    // Helper: build a minimal AstBuffer with a single simple sentence
    fn make_ast(
        selbris: Vec<Selbri>,
        bridi_relation: u32,
        head_terms: Vec<u32>,
    ) -> AstBuffer {
        use bindings::lojban::nesy::ast_types::{Bridi, Sumti};
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

    #[test]
    fn test_extract_head_relation_root() {
        let selbris = vec![Selbri::Root("klama".to_string())];
        assert_eq!(
            extract_head_relation(&selbris, 0),
            Some("klama".to_string())
        );
    }

    #[test]
    fn test_extract_head_relation_tanru() {
        let selbris = vec![
            Selbri::Root("barda".to_string()),
            Selbri::Root("klama".to_string()),
            Selbri::Tanru((0, 1)),
        ];
        // Tanru head is the second element (index 1) → "klama"
        assert_eq!(
            extract_head_relation(&selbris, 2),
            Some("klama".to_string())
        );
    }

    #[test]
    fn test_resolve_go_i_basic() {
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let last = Some("klama".to_string());
        let result = resolve_go_i(&mut ast, &last).unwrap();
        // go'i should be resolved to "klama"
        match &ast.selbris[0] {
            Selbri::Root(name) => assert_eq!(name, "klama"),
            _ => panic!("expected Root(\"klama\")"),
        }
        // last_relation should remain "klama" (go'i doesn't update it further)
        assert_eq!(result, Some("klama".to_string()));
    }

    #[test]
    fn test_resolve_go_i_no_antecedent() {
        let mut ast = make_ast(
            vec![Selbri::Root("go'i".to_string())],
            0,
            vec![0],
        );
        let result = resolve_go_i(&mut ast, &None);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("no antecedent"));
    }

    #[test]
    fn test_resolve_go_i_multi_sentence() {
        use bindings::lojban::nesy::ast_types::{Bridi, Sumti};
        let mut ast = AstBuffer {
            selbris: vec![
                Selbri::Root("klama".to_string()),
                Selbri::Root("go'i".to_string()),
            ],
            sumtis: vec![
                Sumti::ProSumti("mi".to_string()),
                Sumti::ProSumti("do".to_string()),
            ],
            sentences: vec![
                Sentence::Simple(Bridi {
                    relation: 0,
                    head_terms: vec![0],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    relation: 1,
                    head_terms: vec![1],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
            ],
            roots: vec![0, 1],
        };
        let result = resolve_go_i(&mut ast, &None).unwrap();
        // Second sentence's go'i should be resolved to "klama" from first
        match &ast.selbris[1] {
            Selbri::Root(name) => assert_eq!(name, "klama"),
            _ => panic!("expected Root(\"klama\")"),
        }
        assert_eq!(result, Some("klama".to_string()));
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
