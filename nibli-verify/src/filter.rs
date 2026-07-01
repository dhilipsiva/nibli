//! Conservative fragment filter: is a `(KB, query)` case inside the cleanly-mappable
//! Horn / NAF-free classical fragment?
//!
//! Over-skipping is safe (it only lowers coverage); under-skipping would judge a
//! non-classical case against a classical oracle and raise a false alarm, so every
//! check here errs toward SKIP. Two layers:
//!   1. a SOURCE token scan for genuine negation — a universal rule's implication
//!      arrow also compiles to `Not` (`Or(Not(A),B)`), indistinguishable from a real
//!      `na` once flattened, so genuine negation must be caught before translation;
//!   2. a buffer scan for the non-classical node kinds (compute / tense / deontic /
//!      exact-count / abstraction).

use nibli_types::logic::{LogicBuffer, LogicNode};

/// Lojban logical-negation cmavo. These introduce classical-breaking negation (read
/// as negation-as-failure under the CWA); scalar contraries (`na'e`, `to'e`, `no'e`)
/// change the predicate, not the logic, and are left to the buffer scan.
const NEGATION_CMAVO: &[&str] = &["na", "naku", "na'i"];

/// True if a source line contains a genuine-negation cmavo as a whitespace token.
/// Lojban cmavo are space-delimited, so token equality is exact (a gismu like `nanmu`
/// is one token and never matches `na`).
pub fn source_has_negation(line: &str) -> bool {
    line.split_whitespace()
        .any(|tok| NEGATION_CMAVO.contains(&tok))
}

/// `Some(reason)` if the buffer contains a node outside the classical FOL fragment.
pub fn buffer_non_classical(buf: &LogicBuffer) -> Option<&'static str> {
    for node in &buf.nodes {
        let reason = match node {
            LogicNode::ComputeNode(_) => "compute predicate",
            LogicNode::PastNode(_) | LogicNode::PresentNode(_) | LogicNode::FutureNode(_) => {
                "tense"
            }
            LogicNode::ObligatoryNode(_) | LogicNode::PermittedNode(_) => "deontic",
            LogicNode::CountNode(_) => "exact-count quantifier",
            LogicNode::Predicate((rel, _)) if rel.starts_with("__abs_") => "abstraction",
            _ => continue,
        };
        return Some(reason);
    }
    None
}

/// `Some(reason)` if the buffer is outside the **ASP-mappable** (stratified-NAF +
/// closed-world) fragment. Two differences from `buffer_non_classical`: negation-as-failure
/// (`NotNode`) is ACCEPTED (the whole point of the clingo oracle), and `__abs_` ABSTRACTIONS
/// (`lo nu`/`lo du'u`/…) are ACCEPTED — the translator models an abstraction as an opaque constant
/// keyed by its content hash (`asp::abs_const_of`), so a deontic-NAF rule like GDPR's
/// `ro lo prenu poi na zanru cu se bilga lo nu se vimcu` maps. The other non-classical node kinds
/// (compute / tense / deontic modal / exact-count) are still rejected, plus `du` equality (not
/// event-decomposed; would need explicit congruence rules).
///
/// (`se bilga` / `se curmi` compile to the PLAIN gismu `bilga`/`curmi`, not a deontic modal node,
/// so the deontic reading rides for free once the abstraction in the head is mapped.)
pub fn buffer_asp_mappable(buf: &LogicBuffer) -> Option<&'static str> {
    for node in &buf.nodes {
        let reason = match node {
            LogicNode::ComputeNode(_) => "compute predicate",
            LogicNode::PastNode(_) | LogicNode::PresentNode(_) | LogicNode::FutureNode(_) => {
                "tense"
            }
            LogicNode::ObligatoryNode(_) | LogicNode::PermittedNode(_) => "deontic",
            LogicNode::CountNode(_) => "exact-count quantifier",
            LogicNode::Predicate((rel, _)) if rel == "du" => "equality",
            _ => continue,
        };
        return Some(reason);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_types::logic::LogicalTerm;

    #[test]
    fn detects_negation_tokens() {
        assert!(source_has_negation("ro lo prenu poi na zanru cu se bilga"));
        assert!(source_has_negation("naku la .adam. cu gerku"));
        assert!(!source_has_negation("ro lo gerku cu danlu"));
        // `nanmu` must not trip the `na` check.
        assert!(!source_has_negation("la .adam. cu nanmu"));
    }

    #[test]
    fn flags_non_classical_nodes() {
        let compute = LogicBuffer {
            nodes: vec![LogicNode::ComputeNode(("pilji".into(), vec![]))],
            roots: vec![0],
        };
        assert_eq!(buffer_non_classical(&compute), Some("compute predicate"));

        let abs = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "__abs_ab12".into(),
                vec![LogicalTerm::Constant("x".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(buffer_non_classical(&abs), Some("abstraction"));

        let plain = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "gerku".into(),
                vec![LogicalTerm::Constant("adam".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(buffer_non_classical(&plain), None);
    }

    #[test]
    fn asp_mappable_accepts_naf_rejects_du_and_non_classical() {
        // NAF (NotNode) is accepted by the ASP filter (unlike the classical one).
        let naf = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("gerku".into(), vec![LogicalTerm::Variable("x".into())])),
                LogicNode::NotNode(0),
            ],
            roots: vec![1],
        };
        assert_eq!(buffer_asp_mappable(&naf), None);

        // `du` equality is rejected (needs congruence rules — out of scope).
        let du = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "du".into(),
                vec![
                    LogicalTerm::Constant("adam".into()),
                    LogicalTerm::Constant("bel".into()),
                ],
            ))],
            roots: vec![0],
        };
        assert_eq!(buffer_asp_mappable(&du), Some("equality"));

        // The non-classical reject list still applies (compute / deontic / …).
        let compute = LogicBuffer {
            nodes: vec![LogicNode::ComputeNode(("pilji".into(), vec![]))],
            roots: vec![0],
        };
        assert_eq!(buffer_asp_mappable(&compute), Some("compute predicate"));

        // Abstractions (`lo nu` → `__abs_`) are ACCEPTED by the ASP filter (modeled as opaque
        // constants) though still rejected by the classical one.
        let abs = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "__abs_ab12".into(),
                vec![LogicalTerm::Variable("v".into())],
            ))],
            roots: vec![0],
        };
        assert_eq!(buffer_non_classical(&abs), Some("abstraction"));
        assert_eq!(buffer_asp_mappable(&abs), None);
    }
}
