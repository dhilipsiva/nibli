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
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe)
            )

            (datatype Formula
                (Pred1 String Term)
                (Pred2 String Term Term)
                (Pred3 String Term Term Term)
                (Pred4 String Term Term Term Term)
                (Pred5 String Term Term Term Term Term)
                (And Formula Formula)
                (Or Formula Formula)
                (Not Formula)
                (Implies Formula Formula)
                (Exists String Formula)
                (ForAll String Formula)
            )

            (relation IsTrue (Formula))
            (rewrite (And A B) (And B A))
            (rewrite (Not (Not A)) A)
        "#;

        egraph
            .parse_and_run_program(None, schema_str)
            .expect("Failed to load static FOL schema");

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
            let command = format!("(IsTrue {})\n(run 10)", sexp);
            if let Err(e) = egraph.parse_and_run_program(None, &command) {
                return Err(format!("Failed to assert fact: {}", e));
            }
        }
        Ok(())
    }

    fn query_entailment(logic: LogicBuffer) -> Result<bool, String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

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

/// A localized, high-speed translator operating purely on the zero-copy logic arena
fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            let args_str: Vec<String> = args
                .iter()
                .map(|arg| match arg {
                    LogicalTerm::Variable(v) => format!("(Var \"{}\")", v),
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                })
                .collect();
            let arity = args.len().clamp(1, 5);
            format!("(Pred{} \"{}\" {})", arity, rel, args_str.join(" "))
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
