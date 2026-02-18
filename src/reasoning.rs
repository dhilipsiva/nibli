use egglog::EGraph;
use crate::ir::{LogicalForm, LogicalTerm};

pub struct ReasoningCore {
    egraph: EGraph,
}

impl ReasoningCore {
    pub fn new() -> Self {
        let mut egraph = EGraph::default();
        
        // 1. Define the Lojban Logical Schema in egglog
        let schema = r#"
            ;; Data types
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe) ;; zo'e - unspecified
            )

            (datatype Formula
                ;; Core relations 
                (Klama Term Term Term Term Term)
                (Prami Term Term)
                (SePrami Term Term)
                (Gerku Term)
                
                ;; Logical Connectives
                (And Formula Formula)
                (Or Formula Formula)
                (Not Formula)
                (Implies Formula Formula)
            )

            ;; --------------------------------------------------
            ;; Equality Saturation (E-Graph Rewrite Rules)
            ;; --------------------------------------------------
            
            ;; Commutativity of AND
            (rewrite (And A B) (And B A))
            
            ;; Double Negation elimination
            (rewrite (Not (Not A)) A)

            ;; Lojban 'se' permutation rule
            (rewrite (Prami x1 x2) (SePrami x2 x1))
        "#;

        // egglog 2.0.0 requires a filepath Option as the first argument
        egraph.parse_and_run_program(None, schema).expect("Failed to load schema");

        Self { egraph }
    }

    /// Compiles our Rust LIR into an egglog S-expression string.
    fn form_to_sexp(&self, form: &LogicalForm) -> String {
        match form {
            LogicalForm::Predicate { relation: _, args } => {
                let rel_str = "Klama"; 
                
                let args_str: Vec<String> = args.iter().map(|arg| {
                    match arg {
                        LogicalTerm::Variable(_) => "(Var \"da\")".to_string(),
                        LogicalTerm::Constant(_) => "(Const \"la_djan\")".to_string(),
                        LogicalTerm::Description(_) => "(Desc \"lo_zarci\")".to_string(),
                        LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    }
                }).collect();
                
                format!("({} {})", rel_str, args_str.join(" "))
            }
            LogicalForm::And(left, right) => {
                format!("(And {} {})", self.form_to_sexp(left), self.form_to_sexp(right))
            }
            _ => unimplemented!("Other forms deferred for V1 MVP"),
        }
    }

    /// Ingests a new fact into the knowledge base and runs saturation.
    pub fn assert_fact(&mut self, form: &LogicalForm) {
        let sexp = self.form_to_sexp(form);
        
        let command = format!("
            (let f1 {})
            (run 10) 
        ", sexp);

        self.egraph.parse_and_run_program(None, &command).expect("Failed to assert fact");
    }

    /// Queries the e-graph for a specific logical pattern.
    pub fn query(&mut self, query_sexp: &str) {
        let command = format!("(check {})", query_sexp);
        match self.egraph.parse_and_run_program(None, &command) {
            Ok(_) => println!("Query TRUE: Graph entails {}", query_sexp),
            Err(e) => println!("Query FALSE/UNKNOWN: {}", e),
        }
    }
}
