//! The shipped case-study corpora, embedded so the differential gate can check their mappable
//! sub-slice. These are the same repo-root files the `gdpr_*` / `ddi_*` nibli-engine tests
//! `include_str!`, so the gate tracks exactly what ships.

/// EU GDPR compliance knowledge base (`gdpr.lojban`).
pub const GDPR: &str = include_str!("../../gdpr.lojban");

/// Drug-drug interaction safety knowledge base (`drug-interactions.lojban`).
pub const DDI: &str = include_str!("../../drug-interactions.lojban");

/// The repository README examples corpus (`readme.lojban`) — also the source of the
/// Transparency Triad UI presets. Used by the parse-differential (every line gerna
/// accepts must be camxes-parseable); not oracle-mapped as a verdict corpus.
pub const README: &str = include_str!("../../readme.lojban");

/// The non-comment (`#`), non-blank, trimmed lines of a corpus.
pub fn lines(corpus: &str) -> Vec<&str> {
    corpus
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn corpora_load_and_strip_comments() {
        // Non-trivial content, and no comment/blank lines survive.
        for corpus in [GDPR, DDI] {
            let ls = lines(corpus);
            assert!(ls.len() > 5, "corpus too small: {}", ls.len());
            assert!(ls.iter().all(|l| !l.is_empty() && !l.starts_with('#')));
        }
    }
}
