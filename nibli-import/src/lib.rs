//! Knowledge base import/export for standard formats.
//!
//! Provides RDF Turtle import, OWL class hierarchy import, and fact export.
//! Uses `nibli-engine` to inject facts via `assert_fact_direct`.

pub mod export;
pub mod owl;
pub mod rdf;

use nibli_engine::NibliEngine;

/// Import RDF Turtle triples into the engine's KB.
/// Parses the Turtle text, then for each triple:
/// - `rdfs:subClassOf` → `declare_subsort`
/// - `rdf:type` → `declare_entity_sort`
/// - Other → `assert_fact_direct(predicate, [subject, object])`
///
/// Returns the number of facts/declarations imported.
pub fn import_turtle(engine: &NibliEngine, turtle_text: &str) -> Result<usize, String> {
    let triples = rdf::parse_turtle(turtle_text)?;
    owl::import_owl_classes(engine, &triples)
}

/// Import raw RDF triples (without OWL class handling) into the KB.
/// Every triple becomes a 2-argument fact: `predicate(subject, object)`.
///
/// Returns the number of facts asserted.
pub fn import_triples_raw(engine: &NibliEngine, turtle_text: &str) -> Result<usize, String> {
    let triples = rdf::parse_turtle(turtle_text)?;
    let mut count = 0;
    for triple in &triples {
        let rel = triple.predicate.local_name().to_string();
        let args = vec![
            term_to_logical(&triple.subject),
            term_to_logical(&triple.object),
        ];
        engine
            .assert_fact_direct(rel, args)
            .map_err(|e| e.to_string())?;
        count += 1;
    }
    Ok(count)
}

/// Export all active KB facts as labeled lines.
pub fn export_facts(engine: &NibliEngine) -> Result<String, String> {
    export::export_fact_labels(engine)
}

fn term_to_logical(term: &rdf::Term) -> nibli_engine::EngineLogicalTerm {
    match term {
        rdf::Term::Iri(_) => {
            nibli_engine::EngineLogicalTerm::Constant(term.local_name().to_string())
        }
        rdf::Term::StringLiteral(s) => nibli_engine::EngineLogicalTerm::Constant(s.clone()),
        rdf::Term::NumericLiteral(n) => nibli_engine::EngineLogicalTerm::Number(*n),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_import_simple_triple() {
        let engine = NibliEngine::new();
        let turtle = r#"<http://example.org/adam> <http://example.org/likes> <http://example.org/bob> ."#;
        let count = import_triples_raw(&engine, turtle).unwrap();
        assert_eq!(count, 1);
        let facts = engine.list_facts().unwrap();
        assert!(!facts.is_empty());
    }

    #[test]
    fn test_import_owl_class_hierarchy() {
        let engine = NibliEngine::new();
        let turtle = r#"
<http://example.org/Dog> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.org/Animal> .
<http://example.org/adam> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.org/Dog> .
"#;
        let count = import_turtle(&engine, turtle).unwrap();
        assert_eq!(count, 2); // 1 subsort + 1 entity sort
    }

    #[test]
    fn test_import_numeric_literal() {
        let engine = NibliEngine::new();
        let turtle = r#"<http://example.org/adam> <http://example.org/age> "42"^^<http://www.w3.org/2001/XMLSchema#integer> ."#;
        let count = import_triples_raw(&engine, turtle).unwrap();
        assert_eq!(count, 1);
    }

    #[test]
    fn test_import_with_prefix() {
        let engine = NibliEngine::new();
        let turtle = r#"
@prefix ex: <http://example.org/> .
ex:adam ex:likes ex:bob .
"#;
        let count = import_triples_raw(&engine, turtle).unwrap();
        assert_eq!(count, 1);
    }

    #[test]
    fn test_export_roundtrip() {
        let engine = NibliEngine::new();
        engine
            .assert_fact_direct(
                "likes".to_string(),
                vec![
                    nibli_engine::EngineLogicalTerm::Constant("adam".to_string()),
                    nibli_engine::EngineLogicalTerm::Constant("bob".to_string()),
                ],
            )
            .unwrap();
        let exported = export_facts(&engine).unwrap();
        assert!(exported.contains("likes"));
    }
}
