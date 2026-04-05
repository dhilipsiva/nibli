//! N-Triples export: serialize KB fact summaries to RDF-like format.

use nibli_engine::NibliEngine;

/// Export all active facts in the KB as a human-readable list.
/// Each line is: `<fact_id> <label>` — the Lojban source or `:assert` form.
///
/// For full N-Triples export from StoredFacts, a deeper KB accessor would
/// be needed. This v1 exports the fact registry labels which contain the
/// original Lojban text (the canonical source of truth for the KB).
pub fn export_fact_labels(engine: &NibliEngine) -> Result<String, String> {
    let facts = engine.list_facts()?;
    let mut output = String::new();
    for fact in &facts {
        output.push_str(&format!("# fact:{} {}\n", fact.id, fact.label));
    }
    Ok(output)
}
