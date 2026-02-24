#[allow(warnings)]
mod bindings;

use bindings::Guest;
use bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};
use bindings::lojban::nesy::{parser, reasoning, semantics};

struct EnginePipeline;

// ─── Shared pipeline: text → AST → LogicBuffer ───

fn compile_pipeline(text: &str) -> Result<LogicBuffer, String> {
    let ast = parser::parse_text(text).map_err(|e| format!("Parse: {}", e))?;
    semantics::compile_buffer(&ast).map_err(|e| format!("Semantics: {}", e))
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
    fn assert_text(input: String) -> Result<u32, String> {
        let buf = compile_pipeline(&input)?;
        reasoning::assert_fact(&buf).map_err(|e| format!("Reasoning: {}", e))?;
        Ok(buf.roots.len() as u32)
    }

    fn query_text(input: String) -> Result<bool, String> {
        let buf = compile_pipeline(&input)?;
        reasoning::query_entailment(&buf).map_err(|e| format!("Reasoning: {}", e))
    }

    fn compile_debug(input: String) -> Result<String, String> {
        let buf = compile_pipeline(&input)?;
        Ok(debug_sexp(&buf))
    }

    fn reset_kb() -> Result<(), String> {
        reasoning::reset_state().map_err(|e| format!("Reset: {}", e))
    }
}

// ─── S-expression reconstruction ───

fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => format!("(Var \"{}\")", v),
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", n),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_sexp(buffer, *l),
                reconstruct_sexp(buffer, *r)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_sexp(buffer, *l),
                reconstruct_sexp(buffer, *r)
            )
        }
        LogicNode::NotNode(inner) => {
            format!("(Not {})", reconstruct_sexp(buffer, *inner))
        }
        LogicNode::ExistsNode((v, body)) => {
            format!("(Exists \"{}\" {})", v, reconstruct_sexp(buffer, *body))
        }
        LogicNode::ForAllNode((v, body)) => {
            format!("(ForAll \"{}\" {})", v, reconstruct_sexp(buffer, *body))
        }
        LogicNode::PastNode(inner) => format!("(Past {})", reconstruct_sexp(buffer, *inner)),
        LogicNode::PresentNode(inner) => format!("(Present {})", reconstruct_sexp(buffer, *inner)),
        LogicNode::FutureNode(inner) => format!("(Future {})", reconstruct_sexp(buffer, *inner)),
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
