//! Differential/property conformance for the **gerna→smuni compiler seam** — the front-end of the
//! pipeline (`source Lojban text → parse → semantic compile → FOL LogicBuffer`).
//!
//! The six Lean proofs + the Vampire/clingo oracle gates all verify the REASONER (logji) against
//! smuni's already-compiled IR. Nothing else verifies that gerna→smuni compiles the *source text* to
//! the intended IR — and the isolated smuni unit tests hand-build ASTs (`compile_one`), bypassing
//! gerna. A bug in the front-end would yield a `LogicBuffer` that doesn't match the source's meaning,
//! and the reasoner would soundly derive a confident, formally-valid proof of the wrong statement.
//!
//! This module compiles from a `&str` end-to-end (via `nibli_engine::compile_debug`) and supports two
//! check families (driven by the `gerna_smuni_seam_conformance` gate):
//!   - **structural golden** — the compiled FOL *shape* matches hand-verified expectations for each
//!     core construct (event decomposition, conversion, negation, connectives, quantifiers); this is
//!     the ground-truth check that catches a systematic miscompilation;
//!   - **metamorphic** — two different surface forms that must compile to the SAME FOL (e.g. `E se P F`
//!     ≡ `F P E`); oracle-free, resilient, catches transformation bugs.
//!
//! Honest scope: a corpus/property gate, not a proof. Systematic bugs are caught only where a golden
//! FOL is hand-verified; a full external-grammar (camxes) differential remains a future extension.

use std::collections::HashMap;

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

/// Compile source Lojban to its FOL `LogicBuffer` through the full front-end (gerna parse + `go'i`
/// resolution + smuni compile + compute-marking), via the native engine.
pub fn compile(text: &str) -> Result<LogicBuffer, String> {
    let engine = nibli_engine::NibliEngine::new();
    engine
        .compile_debug(text)
        .map_err(|e| format!("compile '{text}': {e}"))
}

/// Canonicalize a buffer for structural comparison: rewrite every distinct variable name to a
/// positional `V<n>` in first-occurrence (node-array) order — deterministic, since the flattener
/// emits children before parents. Two shape-identical buffers compiled at different fresh-variable-
/// counter states therefore compare equal. Constants / `Unspecified` / `__abs_<hash>` markers are
/// content-stable and left untouched. (Not a full normal form: And/Or associativity+commutativity are
/// NOT normalized, so this supports shape-identical metamorphic relations only.)
pub fn canonicalize(buf: &LogicBuffer) -> LogicBuffer {
    // Assign a positional `V<n>` on first sight of each variable name (node-array order).
    fn intern(map: &mut HashMap<String, String>, name: &str) -> String {
        if let Some(v) = map.get(name) {
            return v.clone();
        }
        let v = format!("V{}", map.len());
        map.insert(name.to_string(), v.clone());
        v
    }
    fn rt(map: &mut HashMap<String, String>, t: &LogicalTerm) -> LogicalTerm {
        match t {
            LogicalTerm::Variable(v) => LogicalTerm::Variable(intern(map, v)),
            other => other.clone(),
        }
    }
    fn rt_all(map: &mut HashMap<String, String>, args: &[LogicalTerm]) -> Vec<LogicalTerm> {
        args.iter().map(|t| rt(map, t)).collect()
    }

    let mut map: HashMap<String, String> = HashMap::new();
    let mut nodes = Vec::with_capacity(buf.nodes.len());
    for n in &buf.nodes {
        let cn = match n {
            LogicNode::Predicate((rel, args)) => {
                LogicNode::Predicate((rel.clone(), rt_all(&mut map, args)))
            }
            LogicNode::ComputeNode((rel, args)) => {
                LogicNode::ComputeNode((rel.clone(), rt_all(&mut map, args)))
            }
            LogicNode::ExistsNode((v, b)) => LogicNode::ExistsNode((intern(&mut map, v), *b)),
            LogicNode::ForAllNode((v, b)) => LogicNode::ForAllNode((intern(&mut map, v), *b)),
            LogicNode::CountNode((v, n, b)) => LogicNode::CountNode((intern(&mut map, v), *n, *b)),
            other => other.clone(),
        };
        nodes.push(cn);
    }
    LogicBuffer {
        nodes,
        roots: buf.roots.clone(),
    }
}

/// The buffer's (first) root node.
pub fn root(buf: &LogicBuffer) -> &LogicNode {
    &buf.nodes[buf.roots[0] as usize]
}

/// The node at index `id`.
pub fn node(buf: &LogicBuffer, id: u32) -> &LogicNode {
    &buf.nodes[id as usize]
}

/// The argument terms of the first `Predicate` with relation `rel`, if any.
pub fn pred_args(buf: &LogicBuffer, rel: &str) -> Option<Vec<LogicalTerm>> {
    buf.nodes.iter().find_map(|n| match n {
        LogicNode::Predicate((r, args)) if r == rel => Some(args.clone()),
        _ => None,
    })
}

/// Whether a role argument (`rel`'s 2nd arg) is the constant `c`.
pub fn role_is_const(buf: &LogicBuffer, rel: &str, c: &str) -> bool {
    matches!(
        pred_args(buf, rel).as_deref(),
        Some([_, LogicalTerm::Constant(k)]) if k == c
    )
}

// ── Metamorphic conversion-pair generator ─────────────────────────────────────────────────

/// Two-or-more-place gismu, all in the in-tree FALLBACK dictionary (so pairs compile identically
/// with or without the data file — CI has no data file). `se` swaps x1↔x2; any higher places stay
/// `zo'e` in both surface forms, so `E se P F` ≡ `F P E` for every one of these.
const CONV_PREDS: &[&str] = &[
    "prami", "citka", "nelci", "cusku", "viska", "djuno", "tavla", "pilno",
];

/// Pro-sumti fillers (parser-level cmavo — no dictionary entry needed).
const CONV_ENTS: &[&str] = &["mi", "do", "ti", "ta"];

/// Small deterministic LCG (mirrors [`crate::generator`]) — CI must be reproducible, no rng crate.
fn lcg(seed: u64) -> u64 {
    seed.wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407)
}

/// The `seed`-th `se`-conversion metamorphic pair: `(E se P F, F P E)` — two different surface
/// forms that must compile to the SAME FOL. Deterministic in `seed`.
pub fn conversion_pair(seed: u64) -> (String, String) {
    let mut s = lcg(seed);
    let mut pick = |xs: &[&str]| -> String {
        s = lcg(s);
        xs[((s >> 33) as usize) % xs.len()].to_string()
    };
    let p = pick(CONV_PREDS);
    let e = pick(CONV_ENTS);
    let f = pick(CONV_ENTS);
    (format!("{e} se {p} {f}"), format!("{f} {p} {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> LogicalTerm {
        LogicalTerm::Variable(s.into())
    }

    #[test]
    fn canonicalize_renames_positionally() {
        // `∃_ev5. p(_ev5)` → `∃V0. p(V0)`.
        let b = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("p".into(), vec![v("_ev5")])),
                LogicNode::ExistsNode(("_ev5".into(), 0)),
            ],
            roots: vec![1],
        };
        let c = canonicalize(&b);
        assert_eq!(
            c.nodes[0],
            LogicNode::Predicate(("p".into(), vec![v("V0")]))
        );
        assert_eq!(c.nodes[1], LogicNode::ExistsNode(("V0".into(), 0)));
    }

    #[test]
    fn canonicalize_equates_alpha_variants() {
        // Same shape, different fresh names → equal after canonicalization.
        let mk = |ev: &str, w: &str| LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("gerku".into(), vec![v(ev)])),
                LogicNode::Predicate(("gerku_x1".into(), vec![v(ev), v(w)])),
                LogicNode::AndNode((0, 1)),
                LogicNode::ExistsNode((ev.into(), 2)),
                LogicNode::ForAllNode((w.into(), 3)),
            ],
            roots: vec![4],
        };
        assert_ne!(mk("_ev0", "_v0"), mk("_ev9", "_v3"));
        assert_eq!(
            canonicalize(&mk("_ev0", "_v0")),
            canonicalize(&mk("_ev9", "_v3"))
        );
    }

    #[test]
    fn canonicalize_distinguishes_different_shapes() {
        // A genuine structural difference must survive canonicalization.
        let a = LogicBuffer {
            nodes: vec![LogicNode::Predicate(("gerku".into(), vec![v("_e")]))],
            roots: vec![0],
        };
        let b = LogicBuffer {
            nodes: vec![LogicNode::Predicate(("mlatu".into(), vec![v("_e")]))],
            roots: vec![0],
        };
        assert_ne!(canonicalize(&a), canonicalize(&b));
    }

    #[test]
    fn conversion_pair_deterministic_and_well_formed() {
        let (a1, b1) = conversion_pair(3);
        let (a2, b2) = conversion_pair(3);
        assert_eq!((a1.clone(), b1.clone()), (a2, b2));
        // `E se P F` / `F P E` over the conversion vocab.
        assert!(a1.contains(" se "), "left form uses `se`: {a1}");
        assert!(!b1.contains(" se "), "right form is plain: {b1}");
        assert_ne!(conversion_pair(1), conversion_pair(2));
    }
}
