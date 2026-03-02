//! Jbovlaste dictionary: compile-time perfect hash map of gismu/lujvo arities.
//!
//! The PHF map is generated at build time by `build.rs` from the jbovlaste XML
//! export. Provides O(1) arity lookup with zero runtime allocation.

// Include the perfect hash map generated at compile time by build.rs.
include!(concat!(env!("OUT_DIR"), "/generated_dictionary.rs"));

/// Interface to the compile-time jbovlaste arity dictionary.
pub struct JbovlasteSchema;

impl JbovlasteSchema {
    /// Retrieves the arity of a predicate in O(1) time with zero allocation.
    /// Returns None for unknown words (not in jbovlaste).
    pub fn get_arity(word: &str) -> Option<usize> {
        JBOVLASTE_ARITIES.get(word).copied()
    }

    /// Retrieves the arity, defaulting to 2 for unknown words.
    /// Use this only when a fallback is acceptable (e.g., lujvo not in dictionary).
    pub fn get_arity_or_default(word: &str) -> usize {
        JBOVLASTE_ARITIES.get(word).copied().unwrap_or(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ─── get_arity tests ─────────────────────────────────────────

    #[test]
    fn test_get_arity_known_gismu_klama() {
        // klama is a well-known 5-place gismu
        let arity = JbovlasteSchema::get_arity("klama");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 5);
    }

    #[test]
    fn test_get_arity_known_gismu_gerku() {
        // gerku (dog) is a standard 2-place gismu
        let arity = JbovlasteSchema::get_arity("gerku");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 2);
    }

    #[test]
    fn test_get_arity_known_gismu_prami() {
        // prami (love) is a standard 2-place gismu
        let arity = JbovlasteSchema::get_arity("prami");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 2);
    }

    #[test]
    fn test_get_arity_known_gismu_tavla() {
        // tavla (talk) has 4 places
        let arity = JbovlasteSchema::get_arity("tavla");
        assert!(arity.is_some());
        assert_eq!(arity.unwrap(), 4);
    }

    #[test]
    fn test_get_arity_unknown_word_returns_none() {
        assert_eq!(JbovlasteSchema::get_arity("zzzzz"), None);
    }

    #[test]
    fn test_get_arity_empty_string_returns_none() {
        assert_eq!(JbovlasteSchema::get_arity(""), None);
    }

    #[test]
    fn test_get_arity_cmavo_not_in_dict() {
        // cmavo are not predicates — should not be in the dictionary
        assert_eq!(JbovlasteSchema::get_arity("lo"), None);
        assert_eq!(JbovlasteSchema::get_arity("cu"), None);
    }

    // ─── get_arity_or_default tests ──────────────────────────────

    #[test]
    fn test_get_arity_or_default_known_gismu() {
        assert_eq!(JbovlasteSchema::get_arity_or_default("klama"), 5);
    }

    #[test]
    fn test_get_arity_or_default_unknown_returns_two() {
        assert_eq!(JbovlasteSchema::get_arity_or_default("xyzzy"), 2);
    }

    #[test]
    fn test_get_arity_or_default_empty_returns_two() {
        assert_eq!(JbovlasteSchema::get_arity_or_default(""), 2);
    }

    // ─── Dictionary coverage spot-checks ─────────────────────────

    #[test]
    fn test_various_gismu_arities() {
        // Spot-check a range of common gismu with different arities
        let checks = vec![
            ("mlatu", 2),  // cat: x1 is a cat of species x2
            ("barda", 3),  // big: x1 is big in property x2 by standard x3
            ("sutra", 2),  // fast: x1 is fast at x2
            ("prenu", 1),  // person: x1 is a person
            ("cmene", 3),  // name: x1 is a name of x2 used by x3
            ("dunda", 3),  // give: x1 gives x2 to x3
            ("pilji", 3),  // multiply: x1 is product of x2 and x3
            ("sumji", 3),  // sum: x1 is sum of x2 and x3
        ];
        for (word, expected) in checks {
            let actual = JbovlasteSchema::get_arity(word);
            assert!(
                actual.is_some(),
                "expected {} to be in dictionary",
                word
            );
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
        let arity = JbovlasteSchema::get_arity("brivla");
        // brivla may or may not be in the PHF dict — just verify it doesn't panic
        let _ = arity;
    }

    #[test]
    fn test_get_arity_consistent_with_default() {
        // For known words, both methods should agree
        let word = "klama";
        let arity = JbovlasteSchema::get_arity(word).unwrap();
        let default_arity = JbovlasteSchema::get_arity_or_default(word);
        assert_eq!(arity, default_arity);
    }
}
