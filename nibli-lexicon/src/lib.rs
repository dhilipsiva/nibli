//! nibli-lexicon — the COMMITTED English corpus (the dictionary IS Rust source;
//! see [`corpus`] and the Dictionary Data section of CLAUDE.md).
//!
//! Since the committed-corpus milestone there is exactly ONE build mode: the
//! strongly-typed tables in `src/corpus/` are committed, const-validated at
//! compile time, and identical in local, CI, and deployed builds. The old
//! build-time parse of `dictionary-en.json` (and its FULL/FALLBACK dual mode)
//! is gone — the JSON is now only the INPUT of the `tools/lexigen` regeneration
//! tool (`just regen-lexicon`).
//!
//! The public surface is functions-only (no pub statics), so the internals can
//! evolve without consumer churn:
//! - [`alias`] / [`compound`] — KR-input resolution (English names / `a+b`
//!   compound spellings; gismu do NOT resolve — see the compat note below).
//! - [`get_arity`] / [`get_gloss`] / [`get_template`] — IR-relation lookups.
//! - [`canonical_alias`] / [`by_provenance`] — the gismu→English provenance
//!   bridge (Predilex gates, render overlays, lexigen drift reports).
//! - [`corpus::corpus_entries`] / [`corpus::corpus_compounds`] — iteration.
//!
//! TEMPORARY (dies at the gismu-input-death commit of the corpus series): the
//! `get_*` lookups also accept a raw gismu via the provenance bridge, so the
//! identity-passthrough input path keeps working mid-series.

pub mod arity;
pub mod corpus;
pub mod label;
pub mod reserved;

pub use corpus::{CompoundEntry, CorpusTier, PredicateEntry, Swap};

use std::collections::BTreeMap;
use std::sync::LazyLock;

/// Look up an English predicate name (the only resolvable atomic spelling).
/// `None` means the name is unknown — nibli-kr's resolver FAILS CLOSED (no
/// arity-2 default; NIBLI_KR §13).
pub fn alias(name: &str) -> Option<&'static PredicateEntry> {
    corpus::corpus_predicate(name)
}

/// Look up a compound predicate by its `a+b` KR spelling.
pub fn compound(spelling: &str) -> Option<&'static CompoundEntry> {
    corpus::corpus_compound(spelling)
}

/// The provenance bridge: gismu → its CANONICAL (unswapped) corpus entry.
/// Permanent API — the Predilex gates key their Lojban-lemma bounds through it,
/// and future ontology-row import uses the same mapping.
pub fn by_provenance(gismu: &str) -> Option<&'static PredicateEntry> {
    static BY_PROVENANCE: LazyLock<BTreeMap<&'static str, &'static PredicateEntry>> =
        LazyLock::new(|| {
            corpus::corpus_entries()
                .filter(|e| e.swap.is_none())
                .map(|e| (e.source_gismu, e))
                .collect()
        });
    BY_PROVENANCE.get(gismu).copied()
}

/// The canonical (plain, unswapped) English name for a gismu — the render
/// direction. Converted entries are never canonical.
pub fn canonical_alias(gismu: &str) -> Option<&'static str> {
    by_provenance(gismu).map(|e| e.name)
}

/// TEMPORARY gismu-input compat (removed at gismu-input death): an English
/// name resolves directly; a raw gismu resolves through the provenance bridge.
fn compat(word: &str) -> Option<&'static PredicateEntry> {
    alias(word).or_else(|| by_provenance(word))
}

/// Arity of a predicate word (English name; TEMPORARILY also a raw gismu).
pub fn get_arity(word: &str) -> Option<usize> {
    compat(word).map(|e| e.arity() as usize)
}

/// Primary English gloss of a predicate word.
pub fn get_gloss(word: &str) -> Option<&'static str> {
    compat(word).map(|e| e.gloss)
}

/// Curated English place-frame template (`{x1}`..`{x5}` placeholders), e.g.
/// `get_template("dog")` -> `Some("{x1} is a dog")`. `None` = no curated frame;
/// callers build a generic frame from [`get_gloss`] + [`get_arity`].
pub fn get_template(word: &str) -> Option<&'static str> {
    compat(word).and_then(|e| e.template)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn english_lookups() {
        let goes = alias("goes").expect("goes");
        assert_eq!(goes.arity(), 5);
        assert_eq!(goes.source_gismu, "klama");
        assert_eq!(get_arity("goes"), Some(5));
        assert_eq!(get_arity("dog"), Some(2));
        assert_eq!(get_gloss("dog"), Some("dog"));
        assert_eq!(get_template("dog"), Some("{x1} is a dog"));
        assert_eq!(get_arity("quantity"), Some(3));
    }

    #[test]
    fn converted_entries_carry_their_base() {
        let owned = alias("owned").expect("owned");
        let swap = owned.swap.expect("owned is converted");
        assert_eq!(swap.with, 2);
        assert_eq!(swap.base, "owns");
        assert_eq!(owned.source_gismu, "ponse");
        // Canonical direction never returns a converted entry.
        assert_eq!(canonical_alias("ponse"), Some("owns"));
    }

    #[test]
    fn provenance_bridge() {
        assert_eq!(by_provenance("klama").map(|e| e.name), Some("goes"));
        assert_eq!(by_provenance("gerku").map(|e| e.name), Some("dog"));
        assert!(by_provenance("nosuchword").is_none());
    }

    #[test]
    fn gismu_compat_still_resolves_mid_series() {
        // TEMPORARY: flips to None pins at the gismu-input-death commit.
        assert_eq!(get_arity("klama"), Some(5));
        assert_eq!(get_template("gerku"), Some("{x1} is a dog"));
    }

    #[test]
    fn compounds_resolve_by_plus_spelling_only() {
        let cu = compound("computer+user").expect("seed compound");
        assert_eq!(cu.relation, "computer_user");
        assert_eq!(cu.arity(), 3);
        assert!(
            compound("dog+cat").is_none(),
            "undefined compounds fail closed"
        );
        assert!(
            alias("computer_user").is_none(),
            "the relation ident is not an input spelling"
        );
    }

    #[test]
    fn no_shipped_name_is_reserved() {
        for e in corpus::corpus_entries() {
            assert!(
                !reserved::is_reserved(e.name),
                "corpus name {:?} collides with a nibli KR keyword",
                e.name
            );
        }
    }

    #[test]
    fn every_place_is_named() {
        // The type makes this structural; assert the shipped data anyway.
        for e in corpus::corpus_entries() {
            assert!(!e.places.is_empty() && e.places.len() <= 5, "{:?}", e.name);
            for p in e.places {
                assert!(!p.is_empty(), "{:?} has an unnamed place", e.name);
            }
        }
    }
}
