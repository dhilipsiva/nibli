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
