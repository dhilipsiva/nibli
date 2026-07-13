//! Retraction metamorphic differential: **retract ≡ never-asserted**.
//!
//! `GUARANTEES.md §Retraction Model` promises two paths — O(1) removal for simple
//! ground facts, and a full KB rebuild from surviving base facts for complex
//! assertions (∀-rules, existentials/Skolems, `du` links) — with the rebuild
//! "guaranteed correct". The engine's own suites exercise single retractions; this
//! harness checks the guarantee METAMORPHICALLY at scale: after every retraction in
//! a seeded random op sequence, the incremental engine's verdicts over a fixed
//! entity×predicate battery must be byte-identical to a FRESH engine that asserted
//! only the surviving lines (in original order). Any mismatch means a retraction
//! left residue (stale derived state, index entries, equivalence classes) or
//! removed too much.
//!
//! Op mix per sequence (8–16 ops): ground facts, ∃-skolemizing `lo …` facts,
//! DAG-oriented ∀-rules, `du` identity links, stratified `poi na` NAF rules, and
//! retractions of random still-alive earlier asserts. Two cost/cleanliness bounds
//! carried over from `strat_diff`: positive rule edges descend a fixed predicate
//! order (accepted sets stay acyclic-positive, so battery queries are milliseconds
//! even in debug), and NAF restrictors come from base predicates that are never
//! rule heads (no assert-time rejections muddying the retraction semantics).

use crate::generator::Lcg;

/// Ordered predicate pool. Indexes 0..=1 are BASE (facts + NAF restrictors only,
/// never rule heads); rule heads come from indexes 2.. — so every generated rule
/// set is stratified AND acyclic-positive by construction.
const PREDS: &[&str] = &["gerku", "mlatu", "danlu", "jmive", "melbi"];
const N_BASE: usize = 2;

const ENTS: &[&str] = &["Adam", "Bel"];

/// One operation of a generated sequence.
#[derive(Debug, Clone)]
pub enum Op {
    /// Assert this source line.
    Assert(String),
    /// Retract the fact id produced by the `k`-th `Assert` op (0-based among asserts).
    Retract(usize),
}

/// A generated retraction-differential sequence.
pub struct RetractCase {
    pub name: String,
    pub ops: Vec<Op>,
}

/// Generate the sequence for `seed`: 8..=16 ops. Deterministic.
pub fn random_retract_case(seed: u64) -> RetractCase {
    let mut rng = Lcg::new(seed);
    let mut ops: Vec<Op> = Vec::new();
    let mut n_asserts = 0usize;

    let n_ops = 8 + rng.below(9);
    for _ in 0..n_ops {
        let roll = rng.below(100);
        let op = if roll < 35 {
            // Ground fact.
            Op::Assert(format!("{}({}).", rng.pick(PREDS), rng.pick(ENTS)))
        } else if roll < 45 {
            // ∃-skolemizing fact: `DERIVED(some BASE).` (a witness dog that is an animal).
            let b = PREDS[rng.below(N_BASE)];
            let d = PREDS[N_BASE + rng.below(PREDS.len() - N_BASE)];
            Op::Assert(format!("{d}(some {b})."))
        } else if roll < 55 {
            // du identity link.
            Op::Assert(format!("{} = {}.", rng.pick(ENTS), rng.pick(ENTS)))
        } else if roll < 63 {
            // DAG-oriented positive rule: head index >= 2, body strictly below it.
            let hi = N_BASE + rng.below(PREDS.len() - N_BASE);
            let bi = rng.below(hi);
            Op::Assert(format!("{}(every {}).", PREDS[hi], PREDS[bi]))
        } else if roll < 70 {
            // Stratified NAF rule: base restrictor (never a head), DAG positives.
            let hi = N_BASE + rng.below(PREDS.len() - N_BASE);
            let bi = rng.below(hi);
            let r = PREDS[rng.below(N_BASE)];
            Op::Assert(format!("{}(every {} where ~{r}).", PREDS[hi], PREDS[bi]))
        } else {
            // Retract a random assert made so far (aliveness resolved at run time;
            // retracting an already-retracted id is skipped by the runner).
            if n_asserts == 0 {
                Op::Assert(format!("{}({}).", rng.pick(PREDS), rng.pick(ENTS)))
            } else {
                let k = rng.below(n_asserts);
                ops.push(Op::Retract(k));
                continue;
            }
        };
        if matches!(op, Op::Assert(_)) {
            n_asserts += 1;
        }
        ops.push(op);
    }

    RetractCase {
        name: format!("retract_seed{seed}"),
        ops,
    }
}

/// The result of running one sequence.
#[derive(Debug)]
pub enum RetractOutcome {
    /// Every post-retraction battery matched the fresh replay.
    Agree {
        name: String,
        retractions: usize,
        complex_retractions: usize,
    },
    /// A post-retraction verdict differed from the never-asserted equivalent.
    Diverge {
        name: String,
        after_op: usize,
        retracted_line: String,
        query: String,
        incremental: String,
        fresh: String,
    },
    /// Harness failure (assert/retract/query error).
    Error { name: String, error: String },
}

impl RetractOutcome {
    pub fn is_divergence(&self) -> bool {
        matches!(self, RetractOutcome::Diverge { .. })
    }
    pub fn is_error(&self) -> bool {
        matches!(self, RetractOutcome::Error { .. })
    }
    pub fn summary(&self) -> String {
        match self {
            RetractOutcome::Agree {
                name,
                retractions,
                complex_retractions,
            } => {
                format!("AGREE   {name} ({retractions} retractions, {complex_retractions} complex)")
            }
            RetractOutcome::Diverge {
                name,
                after_op,
                retracted_line,
                query,
                incremental,
                fresh,
            } => format!(
                "DIVERGE {name} after op #{after_op} (retracted '{retracted_line}'): \
                 '{query}' incremental={incremental} fresh={fresh}"
            ),
            RetractOutcome::Error { name, error } => format!("ERROR   {name}: {error}"),
        }
    }
}

/// A complex assertion (rule / existential / `du`) whose retraction takes the
/// full-rebuild path rather than the O(1) ground removal.
fn is_complex(line: &str) -> bool {
    line.contains("(every ") || line.contains("(some ") || line.contains(" = ")
}

/// Run one sequence: apply ops in order on the incremental engine; after every
/// retraction, compare the battery against a fresh engine replaying only the
/// surviving asserts (original order).
pub fn run_retract_case(case: &RetractCase) -> RetractOutcome {
    let name = case.name.clone();
    let engine = crate::kr_engine();

    // (line, engine fact ids, alive) per executed assert, in original order.
    // A line is N independent facts (one per bare `.i` sentence).
    let mut asserts: Vec<(String, Vec<u64>, bool)> = Vec::new();
    let mut retractions = 0usize;
    let mut complex_retractions = 0usize;

    for (op_idx, op) in case.ops.iter().enumerate() {
        match op {
            Op::Assert(line) => match engine.assert_text(line) {
                // A line is N independent facts (one per bare `.i` sentence); track
                // all ids so a retraction removes the whole line as a unit.
                Ok(ids) => asserts.push((line.clone(), ids, true)),
                Err(e) => {
                    return RetractOutcome::Error {
                        name,
                        error: format!("assert '{line}': {e:?}"),
                    };
                }
            },
            Op::Retract(k) => {
                // Resolve to the k-th assert; skip if already retracted.
                let Some((line, ids, alive)) = asserts.get(*k).cloned() else {
                    continue;
                };
                if !alive {
                    continue;
                }
                for id in &ids {
                    if let Err(e) = engine.retract_fact(*id) {
                        return RetractOutcome::Error {
                            name,
                            error: format!("retract '{line}' (id {id}): {e:?}"),
                        };
                    }
                }
                asserts[*k].2 = false;
                retractions += 1;
                if is_complex(&line) {
                    complex_retractions += 1;
                }

                // Fresh replay of the survivors, then the battery on both engines.
                let fresh = crate::kr_engine();
                for (l, _, alive) in &asserts {
                    if *alive {
                        if let Err(e) = fresh.assert_text(l) {
                            return RetractOutcome::Error {
                                name,
                                error: format!("replay '{l}': {e:?}"),
                            };
                        }
                    }
                }
                let mut battery: Vec<String> = Vec::new();
                for e in ENTS {
                    for p in PREDS {
                        battery.push(format!("{p}({e})."));
                    }
                }
                battery.push("Adam = Bel.".to_string());
                for q in &battery {
                    let a = engine
                        .query_text_raw_proof(q)
                        .map(|(v, _)| format!("{v:?}"));
                    let b = fresh.query_text_raw_proof(q).map(|(v, _)| format!("{v:?}"));
                    match (a, b) {
                        (Ok(a), Ok(b)) if a == b => {}
                        (Ok(a), Ok(b)) => {
                            return RetractOutcome::Diverge {
                                name,
                                after_op: op_idx,
                                retracted_line: line,
                                query: q.clone(),
                                incremental: a,
                                fresh: b,
                            };
                        }
                        (a, b) => {
                            return RetractOutcome::Error {
                                name,
                                error: format!("battery '{q}' errored: {a:?} / {b:?}"),
                            };
                        }
                    }
                }
            }
        }
    }

    RetractOutcome::Agree {
        name,
        retractions,
        complex_retractions,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_is_deterministic_and_mixes_ops() {
        let a = random_retract_case(11);
        let b = random_retract_case(11);
        assert_eq!(format!("{:?}", a.ops), format!("{:?}", b.ops));

        // Across a seed range, every op family occurs, including retractions of
        // complex (rebuild-path) assertions — the differential is never vacuous.
        let (mut ground, mut exists, mut du, mut rule, mut naf, mut retracts) = (0, 0, 0, 0, 0, 0);
        for seed in 0..100u64 {
            for op in random_retract_case(seed).ops {
                match op {
                    Op::Assert(l) if l.contains("where ~") => naf += 1,
                    Op::Assert(l) if l.contains("(every ") => rule += 1,
                    Op::Assert(l) if l.contains("(some ") => exists += 1,
                    Op::Assert(l) if l.contains(" = ") => du += 1,
                    Op::Assert(_) => ground += 1,
                    Op::Retract(_) => retracts += 1,
                }
            }
        }
        for (label, n) in [
            ("ground", ground),
            ("exists", exists),
            ("equals", du),
            ("rule", rule),
            ("naf", naf),
            ("retract", retracts),
        ] {
            assert!(n > 20, "op family '{label}' under-generated: {n}");
        }
    }
}
