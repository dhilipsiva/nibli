use crate::dictionary::JbovlasteSchema;
use egglog::EGraph;

pub struct ReasoningCore {
    egraph: EGraph,
}

impl ReasoningCore {
    pub fn new(schema: &JbovlasteSchema) -> Self {
        let mut egraph = EGraph::default();

        let mut schema_str = String::from(
            r#"
            ;; Data types
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe) ;; zo'e - unspecified
            )

            (datatype Formula
        "#,
        );

        // Dynamically inject all 9,300+ predicates from the XML!
        for word in schema.arities.keys() {
            let actual_arity = schema.get_arity(word);
            let cap = crate::semantic::SemanticCompiler::sanitize_name(word);
            let terms = vec!["Term"; actual_arity].join(" ");
            schema_str.push_str(&format!("                ({} {})\n", cap, terms));
        }

        schema_str.push_str(
            r#"
                (And Formula Formula)
                (Or Formula Formula)
                (Not Formula)
                (Implies Formula Formula)
            )

            ;; The Truth Relation (The Knowledge Base)
            (relation IsTrue (Formula))

            ;; --------------------------------------------------
            ;; Equality Saturation (E-Graph Rewrite Rules)
            ;; --------------------------------------------------
            (rewrite (And A B) (And B A))
            (rewrite (Not (Not A)) A)
        "#,
        );

        egraph
            .parse_and_run_program(None, &schema_str)
            .expect("Failed to load dynamic schema");
        Self { egraph }
    }

    /// Ingests a dynamically compiled S-Expression into the active truth database.
    pub fn assert_fact(&mut self, sexp: &str) {
        let command = format!(
            "
            (let f1 {})
            (IsTrue f1) ;; Simply state the relation to assert it
            (run 10) 
        ",
            sexp
        );

        self.egraph
            .parse_and_run_program(None, &command)
            .expect("Failed to assert fact");
    }

    /// Queries the e-graph for entailment.
    pub fn query(&mut self, query_sexp: &str) {
        // We verify if the knowledge base entails that the formula is true.
        let command = format!("(check (IsTrue {}))", query_sexp);
        match self.egraph.parse_and_run_program(None, &command) {
            Ok(_) => println!("Query TRUE: Graph entails {}", query_sexp),
            Err(e) => println!("Query FALSE/UNKNOWN: \n{}", e),
        }
    }
}
