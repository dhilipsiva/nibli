#[allow(warnings)]
mod bindings;
mod dictionary;

use bindings::exports::lojban::nesy::semantics::Guest;
use bindings::lojban::nesy::ast_types::{AstBuffer, Bridi, Selbri, Sumti};
use dictionary::JbovlasteSchema;
use std::sync::OnceLock;

// Ensure the schema is parsed exactly once and held in WASM linear memory
static SCHEMA: OnceLock<JbovlasteSchema> = OnceLock::new();

fn get_schema() -> &'static JbovlasteSchema {
    SCHEMA.get_or_init(|| {
        // Embeds the dictionary directly into the compiled binary
        let xml = include_str!("../../jbovlaste-en.xml");
        JbovlasteSchema::load_from_xml(xml)
    })
}

struct SemanticsComponent;

impl Guest for SemanticsComponent {
    fn compile_buffer(ast: AstBuffer) -> Vec<String> {
        let schema = get_schema();
        let mut results = Vec::with_capacity(ast.sentences.len());

        for sentence in ast.sentences {
            let sexp = compile_sentence(&sentence, &ast.selbris, &ast.sumtis, schema);
            results.push(sexp);
        }

        results
    }
}

/// Dereferences the flat ID arrays and constructs the First-Order Logic S-Expression
fn compile_sentence(
    bridi: &Bridi,
    selbris: &[Selbri],
    sumtis: &[Sumti],
    schema: &JbovlasteSchema,
) -> String {
    // 1. Resolve Selbri
    let relation_node = &selbris[bridi.relation as usize];
    let (rel_str, target_arity) = match relation_node {
        Selbri::Root(r) => (r.as_str(), schema.get_arity(r)),
        Selbri::Compound(parts) => (parts.last().map(|s| s.as_str()).unwrap_or("unknown"), 2),
        Selbri::Tanru((_modifier_id, head_id)) => {
            let head_node = &selbris[*head_id as usize];
            let head_str = match head_node {
                Selbri::Root(r) => r.as_str(),
                _ => "unknown",
            };
            (head_str, schema.get_arity(head_str))
        }
    };

    // 2. Resolve Sumti & Pad
    let mut args = Vec::with_capacity(target_arity);

    for &term_id in &bridi.terms {
        let sumti_node = &sumtis[term_id as usize];
        let formatted_arg = match sumti_node {
            Sumti::ProSumti(p) => {
                if p == "da" || p == "de" || p == "di" {
                    format!("(Var \"{}\")", p)
                } else {
                    format!("(Const \"{}\")", p)
                }
            }
            Sumti::Name(n) => format!("(Const \"{}\")", n),
            Sumti::Description(s_id) => {
                let s_node = &selbris[*s_id as usize];
                let s_str = match s_node {
                    Selbri::Root(r) => r.as_str(),
                    _ => "entity",
                };
                format!("(Desc \"{}\")", s_str)
            }
            Sumti::QuotedLiteral(_) => "(Zoe)".to_string(),
        };
        args.push(formatted_arg);
    }

    // Mathematical padding for unification
    while args.len() < target_arity {
        args.push("(Zoe)".to_string());
    }
    if args.len() > target_arity {
        args.truncate(target_arity);
    }

    let safe_rel = sanitize_name(rel_str);
    format!("({} {})", safe_rel, args.join(" "))
}

fn sanitize_name(word: &str) -> String {
    let mut s = word.replace('\'', "_").replace('.', "");
    if let Some(r) = s.get_mut(0..1) {
        r.make_ascii_uppercase();
    }
    s
}

// Bind to WASM exports
bindings::export!(SemanticsComponent with_types_in bindings);
