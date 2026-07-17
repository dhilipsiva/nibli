//! Non-stratified-rejection differential: does the engine's assert-time
//! stratification check accept/reject EXACTLY the programs an independent reading of
//! the proven criterion says it should — and does a rejection leave the KB clean?
//!
//! `proofs/Stratification.lean` proves the CRITERION correct (the graph condition is
//! equivalent to the existence of a valid stratification), and
//! `check_stratification_matches_proven_criterion` conformance-tests the engine's
//! Tarjan/SCC implementation against a naive reachability oracle — but both of those
//! run on hand-built graphs. Nothing checked the END-TO-END path: source-text rules,
//! asserted incrementally, accepted/rejected at registration, with the KB intact
//! afterward. This differential closes that: seeded random rule programs (which,
//! unlike `generator::random_naf_case`, CAN be unstratifiable) are asserted rule by
//! rule, and every accept/reject decision is checked against [`stratifiable`] — a
//! deliberately independent ~15-line implementation of the criterion, written from
//! the Lean file's STATEMENT ("no negative edge whose target reaches back to its
//! source", reachability over all edges), never from `rules.rs`.
//!
//! Two checks per program:
//! 1. **Per-rule decision differential** — the engine checks stratification at EACH
//!    registration against the already-accepted rules, so the reference mirrors that
//!    incrementally: tentatively add the rule's edges, ask the criterion, expect
//!    accept/reject accordingly (a rejected rule's edges are NOT added — the engine
//!    discards a rejected rule).
//! 2. **Post-rejection replay equivalence** — after any rejection, a FRESH engine
//!    asserting only the accepted lines must give byte-identical verdicts on an
//!    entity×predicate query battery: a rejected rule must leave no trace.

use crate::generator::Lcg;

/// A dependency edge `head → body-predicate` (negative iff the body literal is
/// negated). Extracted from the generated program SPEC, not from engine internals.
pub type Edge = (&'static str, &'static str, bool);

/// One rule of a generated program: its source line and its dependency edges.
pub struct SpecRule {
    pub line: String,
    pub edges: Vec<Edge>,
}

/// A generated stratification-differential program.
pub struct StratCase {
    pub name: String,
    /// Ground facts (asserted first; irrelevant to stratification).
    pub facts: Vec<String>,
    /// Rules, asserted in order.
    pub rules: Vec<SpecRule>,
}

/// INDEPENDENT reference of the stratification criterion, from
/// `proofs/Stratification.lean`'s statement: a rule set is stratifiable iff there is
/// **no negative edge whose target reaches back to its source**, where reachability
/// runs over ALL edges (positive and negative alike).
pub fn stratifiable(edges: &[Edge]) -> bool {
    fn reaches(edges: &[Edge], from: &str, to: &str) -> bool {
        let mut seen: Vec<&str> = vec![from];
        let mut stack: Vec<&str> = vec![from];
        while let Some(cur) = stack.pop() {
            if cur == to {
                return true;
            }
            for (s, t, _) in edges {
                if *s == cur && !seen.contains(t) {
                    seen.push(t);
                    stack.push(t);
                }
            }
        }
        false
    }
    edges
        .iter()
        .filter(|(_, _, neg)| *neg)
        .all(|(src, tgt, _)| !reaches(edges, tgt, src))
}

/// Predicates for the rule pool — all curated English aliases (fallback-safe).
/// Any of them may appear as a head OR a negated restrictor (unlike the
/// stratified-by-construction NAF generator), so negative cycles genuinely occur.
const STRAT_PREDS: &[&str] = &["dog", "cat", "animal", "alive", "beautiful"];

/// Entities for the fact base + query battery.
const STRAT_ENTITIES: &[&str] = &["Adam", "Bel"];

/// Generate the program for `seed`: 1..=3 entity facts, then 2..=6 rules of shape
/// `B(every A).` (edge B→A positive) or `B(every A where ~R).` (edges B→A positive,
/// B→R negative). Deterministic.
///
/// COST BOUND (why positive edges are DAG-oriented): the replay battery queries the
/// ACCEPTED rule set, and a debug-build query over dense positive-cycle programs
/// explodes — cycle-cut `Unknown`s are not memoized, so iterative deepening
/// re-explores the cyclic candidate space per NAF sub-check. Positive rule edges
/// therefore always point from a HIGHER-indexed head to a lower-indexed body
/// (`head → body` descends the pool order), while NEGATIVE edges are unrestricted:
/// every cycle then necessarily contains a negative edge, so exactly the cyclic
/// programs are the REJECTED ones, and every accepted set is an acyclic-positive
/// program whose battery queries terminate fast. The reject side loses nothing;
/// accepted positive CYCLES (legitimate accepts the DAG bias excludes) are covered
/// by the curated `positive_cycle_accepted` case in the gate, which involves no
/// rejection and therefore never queries the cyclic KB.
pub fn random_strat_case(seed: u64) -> StratCase {
    let mut rng = Lcg::new(seed);

    let mut facts = Vec::new();
    let n_facts = 1 + rng.below(3);
    for _ in 0..n_facts {
        facts.push(format!(
            "{}({}).",
            rng.pick(STRAT_PREDS),
            rng.pick(STRAT_ENTITIES)
        ));
    }

    let mut rules = Vec::new();
    let n_rules = 2 + rng.below(5);
    for _ in 0..n_rules {
        // Positive edge head→body descends: pick body index strictly below head index.
        let hi = 1 + rng.below(STRAT_PREDS.len() - 1);
        let bi = rng.below(hi);
        let head = STRAT_PREDS[hi];
        let body = STRAT_PREDS[bi];
        if rng.below(5) < 2 {
            let r = rng.pick(STRAT_PREDS); // unrestricted — may close a (negative) cycle
            rules.push(SpecRule {
                line: format!("{head}(every {body} where ~{r})."),
                edges: vec![(head, body, false), (head, r, true)],
            });
        } else {
            rules.push(SpecRule {
                line: format!("{head}(every {body})."),
                edges: vec![(head, body, false)],
            });
        }
    }

    StratCase {
        name: format!("strat_seed{seed}"),
        facts,
        rules,
    }
}

/// The result of running one program through the differential.
#[derive(Debug)]
pub enum StratOutcome {
    /// Every per-rule decision matched the reference, and (when any rule was
    /// rejected) the post-rejection replay was byte-identical.
    Agree { name: String, rejected: usize },
    /// The engine accepted a rule the criterion rejects, or vice versa.
    DecisionDiverge {
        name: String,
        rule: String,
        engine_accepted: bool,
        reference_accepts: bool,
    },
    /// A rejection left the KB in a different state than never-asserted.
    ReplayDiverge {
        name: String,
        query: String,
        incremental: String,
        fresh: String,
    },
    /// A non-stratification assert error or other harness failure.
    Error { name: String, error: String },
}

impl StratOutcome {
    pub fn is_divergence(&self) -> bool {
        matches!(
            self,
            StratOutcome::DecisionDiverge { .. } | StratOutcome::ReplayDiverge { .. }
        )
    }
    pub fn is_error(&self) -> bool {
        matches!(self, StratOutcome::Error { .. })
    }
    pub fn summary(&self) -> String {
        match self {
            StratOutcome::Agree { name, rejected } => {
                format!("AGREE   {name} ({rejected} rejected)")
            }
            StratOutcome::DecisionDiverge {
                name,
                rule,
                engine_accepted,
                reference_accepts,
            } => format!(
                "DIVERGE {name}: '{rule}' engine-accepted={engine_accepted} but \
                 criterion-accepts={reference_accepts}"
            ),
            StratOutcome::ReplayDiverge {
                name,
                query,
                incremental,
                fresh,
            } => {
                format!("REPLAY-DIVERGE {name}: '{query}' incremental={incremental} fresh={fresh}")
            }
            StratOutcome::Error { name, error } => format!("ERROR   {name}: {error}"),
        }
    }
}

/// Run one program end-to-end: incremental assert with per-rule decision checks,
/// then (after any rejection) the fresh-replay equivalence battery.
pub fn run_strat_case(case: &StratCase) -> StratOutcome {
    let name = case.name.clone();
    let engine = crate::kr_engine();

    for f in &case.facts {
        if let Err(e) = engine.assert_text(f) {
            return StratOutcome::Error {
                name,
                error: format!("fact '{f}': {e:?}"),
            };
        }
    }

    let mut accepted_edges: Vec<Edge> = Vec::new();
    let mut accepted_lines: Vec<&str> = Vec::new();
    let mut rejected = 0usize;
    for rule in &case.rules {
        let mut tentative = accepted_edges.clone();
        tentative.extend(rule.edges.iter().copied());
        let reference_accepts = stratifiable(&tentative);
        match engine.assert_text(&rule.line) {
            Ok(_) => {
                if !reference_accepts {
                    return StratOutcome::DecisionDiverge {
                        name,
                        rule: rule.line.clone(),
                        engine_accepted: true,
                        reference_accepts,
                    };
                }
                accepted_edges = tentative;
                accepted_lines.push(&rule.line);
            }
            Err(e) => {
                let msg = format!("{e:?}");
                if !msg.contains("Unstratifiable") {
                    return StratOutcome::Error {
                        name,
                        error: format!("non-stratification reject of '{}': {msg}", rule.line),
                    };
                }
                if reference_accepts {
                    return StratOutcome::DecisionDiverge {
                        name,
                        rule: rule.line.clone(),
                        engine_accepted: false,
                        reference_accepts,
                    };
                }
                rejected += 1;
            }
        }
    }

    // Post-rejection replay equivalence: a fresh engine given only the surviving
    // lines must answer the whole battery identically — a rejected rule leaves no
    // trace (facts, rules, indexes, caches).
    if rejected > 0 {
        let fresh = crate::kr_engine();
        for f in &case.facts {
            if let Err(e) = fresh.assert_text(f) {
                return StratOutcome::Error {
                    name,
                    error: format!("replay fact '{f}': {e:?}"),
                };
            }
        }
        for l in &accepted_lines {
            if let Err(e) = fresh.assert_text(l) {
                return StratOutcome::Error {
                    name,
                    error: format!("replay rule '{l}': {e:?}"),
                };
            }
        }
        for e in STRAT_ENTITIES {
            for p in STRAT_PREDS {
                let q = format!("{p}({e}).");
                let a = engine
                    .query_text_raw_proof(&q)
                    .map(|(v, _)| format!("{v:?}"));
                let b = fresh
                    .query_text_raw_proof(&q)
                    .map(|(v, _)| format!("{v:?}"));
                let (a, b) = match (a, b) {
                    (Ok(a), Ok(b)) => (a, b),
                    (a, b) => {
                        return StratOutcome::Error {
                            name,
                            error: format!("battery query '{q}' errored: {a:?} / {b:?}"),
                        };
                    }
                };
                if a != b {
                    return StratOutcome::ReplayDiverge {
                        name,
                        query: q,
                        incremental: a,
                        fresh: b,
                    };
                }
            }
        }
    }

    StratOutcome::Agree { name, rejected }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_criterion_boundary_shapes() {
        // p ← NOT p: a negative self-edge — its target trivially reaches its source.
        assert!(!stratifiable(&[("p", "p", true)]));
        // Mutual negative cycle across two rules.
        assert!(!stratifiable(&[("q", "r", true), ("r", "q", true)]));
        // A long POSITIVE cycle is fine…
        assert!(stratifiable(&[
            ("a", "b", false),
            ("b", "c", false),
            ("c", "a", false)
        ]));
        // …until one of its edges is negative.
        assert!(!stratifiable(&[
            ("a", "b", true),
            ("b", "c", false),
            ("c", "a", false)
        ]));
        // A negative edge BETWEEN two SCCs (target cannot reach back) is fine.
        assert!(stratifiable(&[("a", "b", true), ("b", "c", false)]));
        // Empty and positive-only sets are trivially stratifiable.
        assert!(stratifiable(&[]));
        assert!(stratifiable(&[("a", "a", false)]));
    }

    #[test]
    fn generator_is_deterministic_and_produces_both_kinds() {
        let a = random_strat_case(7);
        let b = random_strat_case(7);
        assert_eq!(a.facts, b.facts);
        assert_eq!(
            a.rules.iter().map(|r| &r.line).collect::<Vec<_>>(),
            b.rules.iter().map(|r| &r.line).collect::<Vec<_>>()
        );
        // Over a modest seed range, both stratifiable and unstratifiable full
        // programs occur — the differential is never vacuous on either side.
        let (mut ok, mut bad) = (0, 0);
        for seed in 0..200u64 {
            let c = random_strat_case(seed);
            let all: Vec<Edge> = c.rules.iter().flat_map(|r| r.edges.clone()).collect();
            if stratifiable(&all) {
                ok += 1
            } else {
                bad += 1
            }
        }
        assert!(ok > 20, "too few stratifiable programs: {ok}");
        assert!(bad > 20, "too few unstratifiable programs: {bad}");
    }
}
