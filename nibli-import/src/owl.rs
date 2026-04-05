//! OWL class hierarchy extraction from RDF triples.
//!
//! Maps `rdfs:subClassOf` → `declare_subsort` and
//! `rdf:type` → `declare_entity_sort`.

use crate::rdf::{Term, Triple};
use nibli_engine::NibliEngine;

const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const RDFS_SUBCLASS_OF: &str = "http://www.w3.org/2000/01/rdf-schema#subClassOf";

/// Import OWL class hierarchy from parsed RDF triples.
/// - `rdfs:subClassOf` triples → `declare_subsort(child, parent)`
/// - `rdf:type` triples → `declare_entity_sort(entity, class)`
/// - Other triples → asserted as facts via `assert_fact_direct`
///
/// Returns the number of sort declarations + fact assertions made.
pub fn import_owl_classes(engine: &NibliEngine, triples: &[Triple]) -> Result<usize, String> {
    let mut count = 0;

    for triple in triples {
        let pred_iri = match &triple.predicate {
            Term::Iri(iri) => iri.as_str(),
            _ => continue,
        };

        match pred_iri {
            s if s == RDFS_SUBCLASS_OF || s.ends_with("subClassOf") => {
                let child = triple.subject.local_name();
                let parent = triple.object.local_name();
                if !child.is_empty() && !parent.is_empty() {
                    engine.kb().declare_subsort(child, parent);
                    count += 1;
                }
            }
            s if s == RDF_TYPE || s.ends_with("#type") => {
                let entity = triple.subject.local_name();
                let class = triple.object.local_name();
                if !entity.is_empty() && !class.is_empty() {
                    engine.kb().declare_entity_sort(entity, class);
                    count += 1;
                }
            }
            _ => {
                // Regular triple → assert as fact.
                let rel = triple.predicate.local_name().to_string();
                let args = vec![
                    term_to_logical(&triple.subject),
                    term_to_logical(&triple.object),
                ];
                engine.assert_fact_direct(rel, args).map_err(|e| e.to_string())?;
                count += 1;
            }
        }
    }

    Ok(count)
}

fn term_to_logical(term: &Term) -> nibli_engine::EngineLogicalTerm {
    match term {
        Term::Iri(iri) => {
            let local = term.local_name();
            nibli_engine::EngineLogicalTerm::Constant(local.to_string())
        }
        Term::StringLiteral(s) => nibli_engine::EngineLogicalTerm::Constant(s.clone()),
        Term::NumericLiteral(n) => nibli_engine::EngineLogicalTerm::Number(*n),
    }
}
