#[allow(warnings)]
mod bindings;

use bindings::Guest;
use bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};
use bindings::lojban::nesy::{parser, reasoning, semantics};

struct EnginePipeline;

impl Guest for EnginePipeline {
    fn execute(input: String) -> bool {
        let is_query = input.starts_with("?");
        let text = if is_query { input[1..].trim() } else { &input };

        let ast = match parser::parse_text(text) {
            Ok(ast) => ast,
            Err(e) => {
                println!("[WASM] Parser Error: {}", e);
                return false;
            }
        };

        let logic_buffer = match semantics::compile_buffer(&ast) {
            Ok(buf) => buf,
            Err(e) => {
                println!("[WASM] Semantics Error: {}", e);
                return false;
            }
        };

        // --- DEBUG: View the Shattered Arity Wall ---
        for &root_id in &logic_buffer.roots {
            let debug_sexp = reconstruct_debug_sexp(&logic_buffer, root_id);
            println!("[WASM] Logic Tree: {}", debug_sexp);
        }

        if is_query {
            match reasoning::query_entailment(&logic_buffer) {
                Ok(result) => {
                    println!(
                        "[WASM] Query Entailment: {}",
                        if result { "TRUE" } else { "FALSE" }
                    );
                    return result;
                }
                Err(e) => {
                    println!("[WASM] Query Error: {}", e);
                    return false;
                }
            }
        } else {
            if let Err(e) = reasoning::assert_fact(&logic_buffer) {
                println!("[WASM] Assert Error: {}", e);
                return false;
            }
            println!(
                "[WASM] {} facts inserted natively.",
                logic_buffer.roots.len()
            );
            return true;
        }
    }
}

/// Utility for Orchestrator visibility into the LogicBuffer
fn reconstruct_debug_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => format!("(Var \"{}\")", v),
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_debug_sexp(buffer, *l),
                reconstruct_debug_sexp(buffer, *r)
            )
        }
        LogicNode::ExistsNode((v, body)) => {
            format!(
                "(Exists \"{}\" {})",
                v,
                reconstruct_debug_sexp(buffer, *body)
            )
        }
        LogicNode::ForAllNode((v, body)) => {
            format!(
                "(ForAll \"{}\" {})",
                v,
                reconstruct_debug_sexp(buffer, *body)
            )
        }
    }
}

bindings::export!(EnginePipeline with_types_in bindings);
