#[allow(warnings)]
mod bindings;

use crate::bindings::exports::lojban::nesy::reasoning::Guest;
use crate::bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};
use egglog::EGraph;
use std::sync::{Mutex, OnceLock};

static EGRAPH: OnceLock<Mutex<EGraph>> = OnceLock::new();

fn get_egraph() -> &'static Mutex<EGraph> {
    EGRAPH.get_or_init(|| {
        let mut egraph = EGraph::default();

        let schema_str = r#"
            ;; Atomic Terms
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe)
            )

            ;; Variadic Argument List (Linked List)
            (datatype TermList
                (Nil)
                (Cons Term TermList)
            )

            ;; Well-Formed Formulas
            (datatype Formula
                ;; A single variadic predicate replaces Pred1 through Pred5
                (Pred String TermList)
                
                (And Formula Formula)
                (Or Formula Formula)
                (Not Formula)
                (Implies Formula Formula)
                (Exists String Formula)
                (ForAll String Formula)
            )

            ;; The Knowledge Base
            (relation IsTrue (Formula))

            ;; Equality Saturation Rules
            (rewrite (And A B) (And B A))
            (rewrite (Not (Not A)) A)
        "#;

        egraph
            .parse_and_run_program(None, schema_str)
            .expect("Failed to load variadic FOL schema");

        Mutex::new(egraph)
    })
}

struct ReasoningComponent;

impl Guest for ReasoningComponent {
    fn assert_fact(logic: LogicBuffer) -> Result<(), String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        for &root_id in &logic.roots {
            let sexp = reconstruct_sexp(&logic, root_id);
            // FIX (I8): Removed (run 10) from assertion to speed up data ingestion
            let command = format!("(IsTrue {})", sexp);
            if let Err(e) = egraph.parse_and_run_program(None, &command) {
                return Err(format!("Failed to assert fact: {}", e));
            }
        }
        Ok(())
    }

    fn query_entailment(logic: LogicBuffer) -> Result<bool, String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        // FIX (I8): Saturate the E-Graph once before checking all roots
        if let Err(e) = egraph.parse_and_run_program(None, "(run 10)") {
            return Err(format!("Saturation error: {}", e));
        }

        let mut all_true = true;
        for &root_id in &logic.roots {
            let sexp = reconstruct_sexp(&logic, root_id);
            let command = format!("(check (IsTrue {}))", sexp);
            match egraph.parse_and_run_program(None, &command) {
                Ok(_) => {}
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("Check failed") {
                        all_true = false;
                    } else {
                        return Err(format!("Reasoning error: {}", msg));
                    }
                }
            }
        }
        Ok(all_true)
    }
}

/// Localized translator operating purely on the zero-copy logic arena.
/// Automatically folds N-arity arguments into a Lisp-style Cons list.
fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            // Fold the variadic array into a nested (Cons ... (Cons ... (Nil)))
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
                reconstruct_sexp(buffer, *l),
                reconstruct_sexp(buffer, *r)
            )
        }
        LogicNode::ExistsNode((v, body)) => {
            format!("(Exists \"{}\" {})", v, reconstruct_sexp(buffer, *body))
        }
        LogicNode::ForAllNode((v, body)) => {
            format!("(ForAll \"{}\" {})", v, reconstruct_sexp(buffer, *body))
        }
    }
}

bindings::export!(ReasoningComponent with_types_in bindings);
