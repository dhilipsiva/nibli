//! The nibli KR lookup module — the single vocabulary seam between the
//! surface syntax and the committed English corpus (nibli-lexicon).
//!
//! Since the single-resolution merge (2026-07-17) the dictionary-driven
//! static checks live in [`crate::emit`] — THE validating walk, where each
//! word resolves exactly once at the site that emits it (the old standalone
//! resolve pass re-resolved everything a second time). This module keeps the
//! shared resolution primitives: [`lookup`] (atomic corpus names — English
//! only; gismu never resolve, they survive as provenance), [`lookup_compound`]
//! (committed `a+b` compound entries — uncurated compounds FAIL CLOSED,
//! NIBLI_KR §5), and [`label_index`] (named-argument labels → 0-based SURFACE
//! place indices). Consumers: the emit walk and the §12 lint pass.

/// The corpus entry behind a resolved predicate: an atomic name, or a
/// compound's committed entry (the `a+b` spelling — NIBLI_KR §5).
pub(crate) enum ResolvedEntry {
    Atomic(&'static nibli_lexicon::PredicateEntry),
    Compound(&'static nibli_lexicon::CompoundEntry),
}

impl ResolvedEntry {
    fn place_index(&self, label: &str) -> Option<usize> {
        match self {
            ResolvedEntry::Atomic(e) => e.place_index(label),
            ResolvedEntry::Compound(c) => c.place_index(label),
        }
    }
}

/// A resolved predicate: its corpus entry (the ONLY resolution source since
/// gismu-input death — no identity passthrough, no arity guess).
pub(crate) struct PredInfo {
    pub(crate) surface: String,
    pub(crate) arity: u8,
    pub(crate) entry: ResolvedEntry,
}

pub(crate) fn lookup(word: &str) -> Result<PredInfo, String> {
    if let Some(entry) = nibli_lexicon::alias(word) {
        return Ok(PredInfo {
            surface: word.to_owned(),
            arity: entry.arity(),
            entry: ResolvedEntry::Atomic(entry),
        });
    }
    Err(format!(
        "unknown predicate {word:?}: not a corpus name — \
         unknown names are a compile error, never an arity-2 guess (NIBLI_KR §13)"
    ))
}

/// Resolve a multi-part `a+b` spelling: ONLY a committed compound entry —
/// place structures are conventional, never derivable from the parts, so an
/// uncurated compound FAILS CLOSED (NIBLI_KR §5).
pub(crate) fn lookup_compound(parts: &[String]) -> Result<PredInfo, String> {
    let spelling = parts.join("+");
    if let Some(entry) = nibli_lexicon::compound(&spelling) {
        return Ok(PredInfo {
            surface: spelling,
            arity: entry.arity(),
            entry: ResolvedEntry::Compound(entry),
        });
    }
    Err(format!(
        "unknown compound predicate {spelling:?}: compounds resolve only via a \
         committed corpus entry (place structures are conventional, never \
         derivable) — curate one in nibli-lexicon/src/corpus/compounds.rs or \
         use juxtaposition (NIBLI_KR §5)"
    ))
}

/// Resolve a named-argument label to a 0-based SURFACE place index.
pub(crate) fn label_index(info: &PredInfo, label: &str) -> Option<usize> {
    info.entry.place_index(label)
}
