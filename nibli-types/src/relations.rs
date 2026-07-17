//! Reserved/special relation names — the SINGLE SOURCE.
//!
//! These names carry engine-special semantics keyed on the relation STRING:
//! the identity relation feeds nibli-reason's union-find instead of event
//! decomposition, the built-in arithmetic set evaluates locally (the shared
//! tolerant-equality evaluator in [`crate::arithmetic`]), and the numeric
//! comparisons evaluate exactly. Every crate that special-cases one of these
//! names MUST consult this module — string-matching a literal elsewhere is
//! how the pre-audit engine ended up with the same name in eight places.
//!
//! The per-name EVALUATORS (what `product` computes) stay where behavior
//! lives (`arithmetic.rs`, nibli-reason's `compare_numeric`); conformance
//! tests there pin that each evaluator handles exactly these sets. The
//! Python reference backend mirrors the names — pinned by
//! `python_backend_mirrors_the_compute_names` below.

/// The flat identity relation (`a = b`, union-find ingested — never
/// event-decomposed; binary by grammar).
pub const IDENTITY: &str = "equals";

/// Built-in arithmetic relations evaluated locally by every runtime
/// (tolerant isclose equality — see README "Compute Backend").
pub const BUILTIN_ARITHMETIC: &[&str] = &["product", "sum", "quotient"];

/// Exact numeric comparison relations (never tolerant).
pub const NUMERIC_COMPARISONS: &[&str] = &["greater", "less", "num_equal"];

/// External compute predicates the REFERENCE backend serves
/// (`python/nibli_backend.py` HANDLERS — the mirror test below pins this).
/// The dispatch mechanism itself is open: any unknown compute predicate
/// forwards to whatever backend is configured.
pub const REFERENCE_EXTERNAL_COMPUTE: &[&str] = &["exponential", "logarithm"];

/// Is `rel` the flat identity relation?
pub fn is_identity(rel: &str) -> bool {
    rel == IDENTITY
}

/// Is `rel` a locally-evaluated built-in arithmetic relation?
pub fn is_builtin_arithmetic(rel: &str) -> bool {
    BUILTIN_ARITHMETIC.contains(&rel)
}

/// Is `rel` an exact numeric comparison?
pub fn is_numeric_comparison(rel: &str) -> bool {
    NUMERIC_COMPARISONS.contains(&rel)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn helper_membership() {
        assert!(is_identity("equals"));
        assert!(!is_identity("greater"));
        for r in BUILTIN_ARITHMETIC {
            assert!(is_builtin_arithmetic(r));
            assert!(!is_numeric_comparison(r));
        }
        for r in NUMERIC_COMPARISONS {
            assert!(is_numeric_comparison(r));
            assert!(!is_builtin_arithmetic(r));
        }
    }

    #[test]
    fn python_backend_mirrors_the_compute_names() {
        // The Python reference backend cannot share Rust code; pin its
        // HANDLERS against the const sets by reading the committed source.
        let src = std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../python/nibli_backend.py"
        ))
        .expect("python/nibli_backend.py is committed");
        for name in BUILTIN_ARITHMETIC.iter().chain(REFERENCE_EXTERNAL_COMPUTE) {
            assert!(
                src.contains(&format!("\"{name}\"")) || src.contains(&format!("'{name}'")),
                "python backend HANDLERS must serve {name:?} (the reference \
                 mirror of the compute-name sets)"
            );
        }
    }
}
