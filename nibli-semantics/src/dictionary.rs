//! Jbovlaste predicate arities — a thin facade over the SINGLE arity source.
//!
//! Arity comes from `nibli_lexicon`'s jbovlaste dictionary (the one PHF map
//! built from the XML export, also used for back-translation + logji's
//! `SignatureSource`). smuni delegates here rather than generating its own
//! parallel arity map, so the compiler arity (`get_arity_or_default`, driving
//! `fit_args`/`event_decompose`) and the dictionary arity are the SAME value by
//! construction and cannot diverge. O(1) lookup.

/// Interface to the jbovlaste arity dictionary (delegates to `nibli_lexicon`).
pub struct LexiconSchema;

impl LexiconSchema {
    /// Retrieves the arity of a predicate. The canonical relation names in the
    /// IR are ENGLISH corpus names; `nibli_lexicon::get_arity` resolves them
    /// directly (and, TEMPORARILY, a raw gismu via the provenance compat —
    /// dies at the gismu-input-death commit). Returns None for unknown words.
    pub fn get_arity(word: &str) -> Option<usize> {
        nibli_lexicon::get_arity(word)
    }

    /// Retrieves the arity, defaulting to 2 for unknown words.
    /// Use this only when a fallback is acceptable (e.g., lujvo not in dictionary).
    pub fn get_arity_or_default(word: &str) -> usize {
        Self::get_arity(word).unwrap_or(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ─── get_arity tests ─────────────────────────────────────────

    #[test]
    fn test_get_arity_known_alias_goes() {
        // goes (klama) is the canonical 5-place motion predicate
        let arity = LexiconSchema::get_arity("goes");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 5);
    }

    #[test]
    fn test_get_arity_known_alias_dog() {
        // dog (gerku) is a standard 2-place class predicate
        let arity = LexiconSchema::get_arity("dog");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 2);
    }

    #[test]
    fn test_get_arity_known_alias_loves() {
        // loves (prami) is a standard 2-place predicate
        let arity = LexiconSchema::get_arity("loves");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 2);
    }

    #[test]
    fn test_get_arity_known_alias_talks() {
        // talks (tavla) has 4 places
        let arity = LexiconSchema::get_arity("talks");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 4);
    }

    #[test]
    fn test_gismu_identity_passthrough_still_resolves() {
        // The RAW gismu spelling still resolves via the forward dictionary —
        // the identity-passthrough path. This test FLIPS to a None pin at the
        // committed-corpus milestone (gismu-input death): English-only lookups.
        assert_eq!(LexiconSchema::get_arity("klama"), Some(5));
    }

    #[test]
    fn test_get_arity_unknown_word_returns_none() {
        assert_eq!(LexiconSchema::get_arity("zzzzz"), None);
    }

    #[test]
    fn test_get_arity_empty_string_returns_none() {
        assert_eq!(LexiconSchema::get_arity(""), None);
    }

    #[test]
    fn test_get_arity_cmavo_not_in_dict() {
        // cmavo are not predicates — should not be in the dictionary
        assert_eq!(LexiconSchema::get_arity("lo"), None);
        assert_eq!(LexiconSchema::get_arity("cu"), None);
    }

    // ─── get_arity_or_default tests ──────────────────────────────

    #[test]
    fn test_get_arity_or_default_known_alias() {
        assert_eq!(LexiconSchema::get_arity_or_default("goes"), 5);
    }

    #[test]
    fn test_get_arity_or_default_unknown_returns_two() {
        assert_eq!(LexiconSchema::get_arity_or_default("xyzzy"), 2);
    }

    #[test]
    fn test_get_arity_or_default_empty_returns_two() {
        assert_eq!(LexiconSchema::get_arity_or_default(""), 2);
    }

    #[test]
    fn test_get_arity_english_alias() {
        // Since the predicate-name flip, the canonical relation is the English
        // alias; arity must resolve through the alias map too (goes = klama, 5).
        assert_eq!(LexiconSchema::get_arity("goes"), Some(5));
        assert_eq!(LexiconSchema::get_arity("dog"), Some(2));
        assert_eq!(LexiconSchema::get_arity_or_default("goes"), 5);
    }

    // ─── Dictionary coverage spot-checks ─────────────────────────

    #[test]
    fn test_various_alias_arities() {
        // Spot-check a range of common curated aliases with different arities
        let checks = vec![
            ("cat", 2),      // mlatu: x1 is a cat of species x2
            ("big", 3),      // barda: x1 is big in property x2 by standard x3
            ("fast", 2),     // sutra: x1 is fast at x2
            ("person", 1),   // prenu: x1 is a person
            ("name", 3),     // cmene: x1 is a name of x2 used by x3
            ("gives", 3),    // dunda: x1 gives x2 to x3
            ("product", 3),  // pilji: x1 is product of x2 and x3
            ("sum", 3),      // sumji: x1 is sum of x2 and x3
            ("quantity", 3), // klani: x1 measures x2 on scale x3
        ];
        for (word, expected) in checks {
            let actual = LexiconSchema::get_arity(word);
            assert!(actual.is_some(), "expected {} to resolve", word);
            assert_eq!(
                actual.unwrap(),
                expected,
                "{} should have arity {}, got {}",
                word,
                expected,
                actual.unwrap()
            );
        }
    }

    #[test]
    fn test_lujvo_in_dictionary() {
        // Some lujvo should be in jbovlaste
        let arity = LexiconSchema::get_arity("brivla");
        // brivla may or may not be in the PHF dict — just verify it doesn't panic
        let _ = arity;
    }

    #[test]
    fn test_get_arity_consistent_with_default() {
        // For known words, both methods should agree
        let word = "goes";
        let arity = LexiconSchema::get_arity(word).unwrap();
        let default_arity = LexiconSchema::get_arity_or_default(word);
        assert_eq!(arity, default_arity);
    }
}
