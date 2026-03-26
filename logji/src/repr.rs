//! S-expression reconstruction for logic buffers.
//!
//! Renders a `LogicBuffer` as human-readable S-expressions for debugging.
//! Used by the `:compile` REPL command and `compile_debug` API method.

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};
use std::fmt::Write;

/// Reconstruct a single root node as an S-expression string.
pub fn reconstruct_repr(buffer: &LogicBuffer, node_id: u32) -> String {
    let mut out = String::with_capacity(256);
    write_repr(&mut out, buffer, node_id);
    out
}

/// Reconstruct all root nodes as newline-separated S-expressions.
pub fn debug_logic(buffer: &LogicBuffer) -> String {
    buffer
        .roots
        .iter()
        .map(|&id| reconstruct_repr(buffer, id))
        .collect::<Vec<_>>()
        .join("\n")
}

fn write_repr(out: &mut String, buffer: &LogicBuffer, node_id: u32) {
    let Some(node) = buffer.nodes.get(node_id as usize) else {
        out.push_str(&format!("[invalid node {}]", node_id));
        return;
    };
    match node {
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
            write_repr(out, buffer, *l);
            out.push(' ');
            write_repr(out, buffer, *r);
            out.push(')');
        }
        LogicNode::OrNode((l, r)) => {
            out.push_str("(Or ");
            write_repr(out, buffer, *l);
            out.push(' ');
            write_repr(out, buffer, *r);
            out.push(')');
        }
        LogicNode::NotNode(inner) => {
            out.push_str("(Not ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::ExistsNode((v, body)) => {
            out.push_str("(Exists \"");
            out.push_str(v);
            out.push_str("\" ");
            write_repr(out, buffer, *body);
            out.push(')');
        }
        LogicNode::ForAllNode((v, body)) => {
            out.push_str("(ForAll \"");
            out.push_str(v);
            out.push_str("\" ");
            write_repr(out, buffer, *body);
            out.push(')');
        }
        LogicNode::PastNode(inner) => {
            out.push_str("(Past ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::PresentNode(inner) => {
            out.push_str("(Present ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::FutureNode(inner) => {
            out.push_str("(Future ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::ObligatoryNode(inner) => {
            out.push_str("(Obligatory ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::PermittedNode(inner) => {
            out.push_str("(Permitted ");
            write_repr(out, buffer, *inner);
            out.push(')');
        }
        LogicNode::CountNode((v, count, body)) => {
            out.push_str("(Count \"");
            out.push_str(v);
            out.push_str("\" ");
            let _ = write!(out, "{}", count);
            out.push(' ');
            write_repr(out, buffer, *body);
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
