#[allow(warnings)]
mod bindings;

// Zero-copy code sharing: pull the dictionary logic directly from the semantics crate
#[path = "../../semantics/src/dictionary.rs"]
mod dictionary;

use bindings::exports::lojban::nesy::reasoning::Guest;
use dictionary::JbovlasteSchema;
use egglog::EGraph;
use std::sync::{Mutex, OnceLock};

static SCHEMA: OnceLock<JbovlasteSchema> = OnceLock::new();
static EGRAPH: OnceLock<Mutex<EGraph>> = OnceLock::new();

fn get_schema() -> &'static JbovlasteSchema {
    SCHEMA.get_or_init(|| {
        let xml = include_str!("../../jbovlaste-en.xml");
        JbovlasteSchema::load_from_xml(xml)
    })
}

fn get_egraph() -> &'static Mutex<EGraph> {
    EGRAPH.get_or_init(|| {
        let schema = get_schema();
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
            let cap = sanitize_name(word);
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

        Mutex::new(egraph)
    })
}

fn sanitize_name(word: &str) -> String {
    let mut s = word.replace('\'', "_").replace('.', "");
    if let Some(r) = s.get_mut(0..1) {
        r.make_ascii_uppercase();
    }
    s
}

struct ReasoningComponent;

impl Guest for ReasoningComponent {
    fn assert_fact(sexp: String) {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        let command = format!(
            "
            (let f1 {})
            (IsTrue f1)
            (run 10) 
        ",
            sexp
        );

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

// Bind to WASM exports
bindings::export!(ReasoningComponent with_types_in bindings);
