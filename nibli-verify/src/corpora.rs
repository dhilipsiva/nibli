//! Shipped scoped corpora and isolated historical controls for independent
//! verification of their supported classical sub-slices. The corrected defaults
//! also have native scenario matrices; legacy inputs retain their original pins.

/// Scoped GDPR prerequisite teaching model (`gdpr.nibli`).
#[cfg(feature = "repo-corpora")]
pub const GDPR: &str = include_str!("../../gdpr.nibli");

/// Patient-and-episode interaction-review teaching model (`drug-interactions.nibli`).
#[cfg(feature = "repo-corpora")]
pub const DDI: &str = include_str!("../../drug-interactions.nibli");

/// Utopia constitutional provocation (`utopia.nibli`) — deontic floor + NAF audit /
/// confinement rules. Vampire sees the classical Horn sub-slice; clingo sees the
/// stratified-NAF + abstraction-opaque ASP-mappable whole.
#[cfg(feature = "repo-corpora")]
pub const UTOPIA: &str = include_str!("../../utopia.nibli");

/// The repository README examples corpus (`readme.nibli`) — also the source of the
/// Transparency Triad UI presets. Not oracle-mapped as a verdict corpus.
#[cfg(feature = "repo-corpora")]
pub const README: &str = include_str!("../../readme.nibli");

/// The non-comment (`#`), non-blank, trimmed lines of a corpus.
pub fn lines(corpus: &str) -> Vec<&str> {
    corpus
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect()
}

#[cfg(all(test, feature = "repo-corpora"))]
mod tests {
    use super::*;

    #[test]
    fn corpora_load_and_strip_comments() {
        // Non-trivial content, and no comment/blank lines survive.
        for corpus in [GDPR, DDI, UTOPIA] {
            let ls = lines(corpus);
            assert!(ls.len() > 5, "corpus too small: {}", ls.len());
            assert!(ls.iter().all(|l| !l.is_empty() && !l.starts_with('#')));
        }
    }
}

/// Historical defect controls remain separately available to oracle regressions.
#[cfg(feature = "repo-corpora")]
pub const LEGACY_GDPR: &str = include_str!("../../examples/case-studies/legacy/gdpr-proxy.nibli");
#[cfg(feature = "repo-corpora")]
pub const LEGACY_DDI: &str = include_str!("../../examples/case-studies/legacy/drug-proxy.nibli");
