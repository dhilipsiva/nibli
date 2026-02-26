#[allow(warnings)]
mod bindings;

use bindings::exports::lojban::nesy::engine::{Guest, GuestSession};
use bindings::lojban::nesy::logic_types::{LogicBuffer, LogicNode, LogicalTerm};
use bindings::lojban::nesy::{parser, semantics};
use bindings::lojban::nesy::reasoning::KnowledgeBase;

use std::cell::RefCell;
use std::collections::HashSet;

struct EnginePipeline;

pub struct Session {
    kb: KnowledgeBase,
    compute_predicates: RefCell<HashSet<String>>,
}

// ─── Default compute predicates ───

fn default_compute_predicates() -> HashSet<String> {
    let mut set = HashSet::new();
    set.insert("pilji".to_string());
    set.insert("sumji".to_string());
    set.insert("dilcu".to_string());
    set
}

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(text: &str) -> Result<LogicBuffer, String> {
    let ast = parser::parse_text(text).map_err(|e| format!("Parse: {}", e))?;
    semantics::compile_buffer(&ast).map_err(|e| format!("Semantics: {}", e))
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
        }
    }

    fn assert_text(&self, input: String) -> Result<u32, String> {
        let mut buf = compile_pipeline(&input)?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .assert_fact(&buf)
            .map_err(|e| format!("Reasoning: {}", e))?;
        Ok(buf.roots.len() as u32)
    }

    fn query_text(&self, input: String) -> Result<bool, String> {
        let mut buf = compile_pipeline(&input)?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        self.kb
            .query_entailment(&buf)
            .map_err(|e| format!("Reasoning: {}", e))
    }

    fn compile_debug(&self, input: String) -> Result<String, String> {
        let mut buf = compile_pipeline(&input)?;
        transform_compute_nodes(&mut buf, &self.compute_predicates.borrow());
        Ok(debug_sexp(&buf))
    }

    fn reset_kb(&self) -> Result<(), String> {
        self.kb.reset().map_err(|e| format!("Reset: {}", e))
    }

    fn register_compute_predicate(&self, name: String) {
        self.compute_predicates.borrow_mut().insert(name);
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

bindings::export!(EnginePipeline with_types_in bindings);
