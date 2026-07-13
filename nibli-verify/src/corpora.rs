//! The shipped case-study corpora, embedded so the differential gate can check their mappable
//! sub-slice. These are the same repo-root files the `gdpr_*` / `ddi_*` nibli-engine tests
//! `include_str!`, so the gate tracks exactly what ships. KR corpora since THE DROP (the
//! former `.lojban` sources retired with the Lojban front-end; per-line equality of the
//! twins was CI-pinned by the corpora-twins gate up to the switchover).

/// EU GDPR compliance knowledge base (`gdpr.klaro`).
pub const GDPR: &str = include_str!("../../gdpr.klaro");

/// Drug-drug interaction safety knowledge base (`drug-interactions.klaro`).
pub const DDI: &str = include_str!("../../drug-interactions.klaro");

/// The repository README examples corpus (`readme.klaro`) — also the source of the
/// Transparency Triad UI presets. Not oracle-mapped as a verdict corpus.
pub const README: &str = include_str!("../../readme.klaro");

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
