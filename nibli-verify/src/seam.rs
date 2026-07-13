//! Shared `LogicBuffer` structural-probe helpers for the front-end
//! conformance gates: `canonicalize` (positional variable renaming for
//! shape-equality comparison) plus the small node/argument probes the
//! structural-golden checks are written in. The gerna-era compile seam that
//! used to live here retired at THE DROP; the surviving KR front-end oracle
//! is `tests/kr_seam_gate.rs` (via `klaro_battery::kompile`), which consumes
//! these helpers.

use std::collections::HashMap;

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

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
}
