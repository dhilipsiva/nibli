#[allow(warnings)]
mod bindings;

use bindings::exports::lojban::nesy::reasoning::Guest;
use egglog::EGraph;
use std::sync::{Mutex, OnceLock};

static EGRAPH: OnceLock<Mutex<EGraph>> = OnceLock::new();

fn get_egraph() -> &'static Mutex<EGraph> {
    EGRAPH.get_or_init(|| {
        let mut egraph = EGraph::default();

        // A strictly static, mathematical FOL schema. Zero dynamic Lojban injection required.
        let schema_str = r#"
            ;; Data types
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe) ;; zo'e - unspecified
            )

            (datatype Formula
                ;; Generic Predicates replacing 9,300+ dynamic Lojban types
                (Pred1 String Term)
                (Pred2 String Term Term)
                (Pred3 String Term Term Term)
                (Pred4 String Term Term Term Term)
                (Pred5 String Term Term Term Term Term)

                (And Formula Formula)
                (Or Formula Formula)
                (Not Formula)
                (Implies Formula Formula)
            )

            ;; The Truth Relation (The Knowledge Base)
            (relation IsTrue (Formula))

            ;; Equality Saturation Rules
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
    fn assert_fact(sexp: String) {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        let command = format!("(let f1 {})\n(IsTrue f1)\n(run 10)", sexp);
        egraph
            .parse_and_run_program(None, &command)
            .expect("Failed to assert fact");
    }

    fn query_entailment(sexp: String) -> bool {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        let command = format!("(check (IsTrue {}))", sexp);
        match egraph.parse_and_run_program(None, &command) {
            Ok(_) => {
                println!("[WASM Reasoning Core] Query TRUE: Graph entails {}", sexp);
                true
            }
            Err(e) => {
                println!("[WASM Reasoning Core] Query FALSE/UNKNOWN: {}", e);
                false
            }
        }
    }
}

bindings::export!(ReasoningComponent with_types_in bindings);
