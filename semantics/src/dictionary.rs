// Include the perfect hash map generated at compile time
include!(concat!(env!("OUT_DIR"), "/generated_dictionary.rs"));

pub struct JbovlasteSchema;

impl JbovlasteSchema {
    /// Retrieves the arity of a predicate in O(1) time with zero allocation.
    pub fn get_arity(word: &str) -> usize {
        // Hardcoded fast-path for core routing verb
        if word == "klama" {
            return 5;
        }

        // Perfect hash lookup against the .rodata segment
        *JBOVLASTE_ARITIES.get(word).unwrap_or(&2)
    }
}
