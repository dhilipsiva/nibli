//! nibli-lexigen library target — the pure string heuristics the regeneration
//! binary uses (moved here from nibli-lexicon at the pipeline audit: they are
//! tool-side code, not library surface). The lib target exists so the module
//! tests ride the workspace `cargo test --lib` sweep.

pub mod arity;
pub mod label;
