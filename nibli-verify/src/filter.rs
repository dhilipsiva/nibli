//! Conservative fragment filter: is a `(KB, query)` case inside the cleanly-mappable
//! Horn / NAF-free classical fragment?
//!
//! Over-skipping is safe (it only lowers coverage); under-skipping would judge a
//! non-classical case against a classical oracle and raise a false alarm, so every
//! check here errs toward SKIP. Two layers:
//!   1. a SOURCE token scan for genuine negation — a universal rule's implication
//!      arrow also compiles to `Not` (`Or(Not(A),B)`), indistinguishable from a real
//!      `na` once flattened, so genuine negation must be caught before translation;
//!   2. a buffer scan for the non-classical node kinds (compute / deontic /
//!      exact-count / abstraction), plus the `du` shape gate below. Tense nodes are
//!      NOT rejected here: they are handled downstream by `tense::flavorize`, which
//!      rewrites the verified tense shapes to flavor-suffixed predicates and skips
//!      the unsupported ones (tense×NAF, tense×abstraction, nested wrappers).

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

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

/// Ground `du` in the ONE verified shape both oracles can judge: the buffer's sole root,
/// with exactly two `Constant` args — i.e. a bare `la .X. cu du la .Y.` fact or query
/// (`du` is never event-decomposed, so this is precisely how smuni compiles it). The
/// Vampire path maps it to TPTP native `=` (congruence closure over a definite theory
/// derives exactly the union-find's reflexive/symmetric/transitive/substitutive
/// consequences, in both directions); the ASP path canonicalizes the equivalence classes
/// away before regrouping (`asp::DuClasses`). Everything else — `du` under a rule or
/// negation, `du` with variable/number/description args — is skipped conservatively:
/// nibli's semantics there (contradiction records for `na du`, tensed inertness, exact
/// numeric `dunli` vs `du`) is not what either oracle would judge.
fn du_mappable(buf: &LogicBuffer, idx: usize, args: &[LogicalTerm]) -> bool {
    buf.roots.as_slice() == [idx as u32]
        && args.len() == 2
        && args.iter().all(|a| matches!(a, LogicalTerm::Constant(_)))
}

/// `Some(reason)` if the buffer contains a node outside the classical FOL fragment.
/// (Tense nodes pass — `tense::flavorize` is the tense gate.)
pub fn buffer_non_classical(buf: &LogicBuffer) -> Option<&'static str> {
    for (idx, node) in buf.nodes.iter().enumerate() {
        let reason = match node {
            LogicNode::ComputeNode(_) => "compute predicate",
            LogicNode::ObligatoryNode(_) | LogicNode::PermittedNode(_) => "deontic",
            LogicNode::CountNode(_) => "exact-count quantifier",
            LogicNode::Predicate((rel, _)) if rel.starts_with("__abs_") => "abstraction",
            LogicNode::Predicate((rel, args)) if rel == "du" && !du_mappable(buf, idx, args) => {
                "equality (nested or non-ground)"
            }
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
/// (compute / deontic modal / exact-count) are still rejected; tense nodes pass through to
/// `tense::flavorize`, which rewrites the verified shapes and skips tense×NAF (audit U1)
/// rather than mis-judging it. Ground sole-root `du` equality is ACCEPTED (see
/// [`du_mappable`]; the translator canonicalizes the classes away); any other `du` shape is
/// skipped.
///
/// (`se bilga` / `se curmi` compile to the PLAIN gismu `bilga`/`curmi`, not a deontic modal node,
/// so the deontic reading rides for free once the abstraction in the head is mapped.)
pub fn buffer_asp_mappable(buf: &LogicBuffer) -> Option<&'static str> {
    for (idx, node) in buf.nodes.iter().enumerate() {
        let reason = match node {
            LogicNode::ComputeNode(_) => "compute predicate",
            LogicNode::ObligatoryNode(_) | LogicNode::PermittedNode(_) => "deontic",
            LogicNode::CountNode(_) => "exact-count quantifier",
            LogicNode::Predicate((rel, args)) if rel == "du" && !du_mappable(buf, idx, args) => {
                "equality (nested or non-ground)"
            }
            _ => continue,
        };
        return Some(reason);
    }
    None
}

/// The ASP filter for the QUERY buffer: like [`buffer_asp_mappable`], but a sole-root
/// exact-count query (`Count(v, n, body)` — `re lo gerku cu danlu`) is ACCEPTED: the
/// translator maps it to a clingo `#count` aggregate. Count nodes anywhere else (a
/// count ASSERTION, or a count nested under other structure) stay skipped.
pub fn buffer_asp_mappable_query(buf: &LogicBuffer) -> Option<&'static str> {
    for (idx, node) in buf.nodes.iter().enumerate() {
        let reason = match node {
            LogicNode::ComputeNode(_) => "compute predicate",
            LogicNode::ObligatoryNode(_) | LogicNode::PermittedNode(_) => "deontic",
            LogicNode::CountNode(_) if buf.roots.as_slice() != [idx as u32] => {
                "exact-count quantifier (nested / non-root)"
            }
            LogicNode::Predicate((rel, args)) if rel == "du" && !du_mappable(buf, idx, args) => {
                "equality (nested or non-ground)"
            }
            _ => continue,
        };
        return Some(reason);
    }
    None
}

/// Case-level guard for an exact-count QUERY. Both former skip conditions were
/// CANONIZED by the 2026-07-02 count-semantics decision (GUARANTEES
/// §Aggregation), so nothing is skipped today:
/// - **KBs with rules**: the engine now EXCLUDES the xorlo presupposition
///   witness from counting (it still satisfies ∃/∀), and the ASP program never
///   had one — both sides count the real, derivable entities.
/// - **KBs with `du`**: the engine now counts one representative per
///   du-equivalence class, matching the translator's canonicalization.
///
/// The guard is retained as the documented seam for any FUTURE count shape
/// that needs a conservative skip.
pub fn count_case_guard(_kb: &[LogicBuffer], _query: &LogicBuffer) -> Option<&'static str> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

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

    /// The one accepted `du` shape: sole root, two constants — a bare fact/query.
    fn ground_du() -> LogicBuffer {
        LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "du".into(),
                vec![
                    LogicalTerm::Constant("adam".into()),
                    LogicalTerm::Constant("bel".into()),
                ],
            ))],
            roots: vec![0],
        }
    }

    #[test]
    fn ground_sole_root_du_is_mappable_in_both_fragments() {
        // `la .X. cu du la .Y.` — Vampire judges it as native `=`; the ASP translator
        // canonicalizes the equivalence class away. Accepted by BOTH filters.
        assert_eq!(buffer_non_classical(&ground_du()), None);
        assert_eq!(buffer_asp_mappable(&ground_du()), None);
    }

    #[test]
    fn nested_or_non_ground_du_is_skipped_in_both_fragments() {
        // `du` with a variable arg (e.g. inside a rule) — not the verified shape.
        let non_ground = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "du".into(),
                vec![
                    LogicalTerm::Variable("x".into()),
                    LogicalTerm::Constant("bel".into()),
                ],
            ))],
            roots: vec![0],
        };
        assert_eq!(
            buffer_non_classical(&non_ground),
            Some("equality (nested or non-ground)")
        );
        assert_eq!(
            buffer_asp_mappable(&non_ground),
            Some("equality (nested or non-ground)")
        );

        // Ground `du` that is NOT the sole root (e.g. wrapped in `na du` — a negative-fact
        // /contradiction record in nibli, NOT NAF) — skipped, never mis-judged.
        let negated = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate((
                    "du".into(),
                    vec![
                        LogicalTerm::Constant("adam".into()),
                        LogicalTerm::Constant("bel".into()),
                    ],
                )),
                LogicNode::NotNode(0),
            ],
            roots: vec![1],
        };
        assert_eq!(
            buffer_non_classical(&negated),
            Some("equality (nested or non-ground)")
        );
        assert_eq!(
            buffer_asp_mappable(&negated),
            Some("equality (nested or non-ground)")
        );

        // Numeric `du` (`li pa du li re`) — exact numeric identity is `dunli`/compute
        // territory; skipped.
        let numeric = LogicBuffer {
            nodes: vec![LogicNode::Predicate((
                "du".into(),
                vec![LogicalTerm::Number(1.0), LogicalTerm::Number(2.0)],
            ))],
            roots: vec![0],
        };
        assert_eq!(
            buffer_non_classical(&numeric),
            Some("equality (nested or non-ground)")
        );
        assert_eq!(
            buffer_asp_mappable(&numeric),
            Some("equality (nested or non-ground)")
        );
    }

    #[test]
    fn asp_mappable_accepts_naf_rejects_non_classical() {
        // NAF (NotNode) is accepted by the ASP filter (unlike the classical one).
        let naf = LogicBuffer {
            nodes: vec![
                LogicNode::Predicate(("gerku".into(), vec![LogicalTerm::Variable("x".into())])),
                LogicNode::NotNode(0),
            ],
            roots: vec![1],
        };
        assert_eq!(buffer_asp_mappable(&naf), None);

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
