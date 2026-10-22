//! Retraction metamorphic differential: **retract ≡ never-asserted**.
//!
//! `GUARANTEES.md §Retraction Model` promises retract ≡ never-asserted via a
//! single rebuild path (the former "incremental O(1)" branch was retired
//! 2026-08-01 after this harness's quantified battery rows caught it leaving
//! retracted members in the quantifier domain — 22/200 sequences diverged on
//! bare universals). The engine's own suites exercise single retractions; this
//! harness checks the guarantee METAMORPHICALLY at scale: after every retraction in
//! a seeded random op sequence, the incremental engine's verdicts over a fixed
//! entity×predicate battery must be byte-identical to a FRESH engine that asserted
//! only the surviving lines (in original order). Any mismatch means a retraction
//! left residue (stale derived state, index entries, equivalence classes) or
//! removed too much.
//!
//! Op mix per sequence (8–16 ops): ground facts (entity AND numeric — numbers are
//! quantifier-domain members since 2026-08-01), ∃-skolemizing `lo …` facts,
//! DAG-oriented ∀-rules, `du` identity links, stratified `poi na` NAF rules, and
//! retractions of random still-alive earlier asserts. The battery carries both
//! GROUND rows and QUANTIFIED rows (bare universals, an exact count, and an
//! arithmetic universal satisfiable by numbers only): only quantified queries read
//! the domain-member caches, so retraction residue in `known_*` or the cached
//! member lists is invisible to ground rows — the class behind the 2026-08-01
//! lingering-number and stale-cache findings. Two cost/cleanliness bounds
//! carried over from `strat_diff`: positive rule edges descend a fixed predicate
//! order (accepted sets stay acyclic-positive, so battery queries are milliseconds
//! even in debug), and NAF restrictors come from base predicates that are never
//! rule heads (no assert-time rejections muddying the retraction semantics).

use crate::generator::Lcg;

/// Ordered predicate pool. Indexes 0..=1 are BASE (facts + NAF restrictors only,
/// never rule heads); rule heads come from indexes 2.. — so every generated rule
/// set is stratified AND acyclic-positive by construction.
const PREDS: &[&str] = &["dog", "cat", "animal", "alive", "beautiful"];
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
        let op = if roll < 27 {
            // Ground fact.
            Op::Assert(format!("{}({}).", rng.pick(PREDS), rng.pick(ENTS)))
        } else if roll < 35 {
            // NUMERIC ground fact: numbers are quantifier-domain members
            // (2026-08-01), and a lingering number satisfies arithmetic bodies
            // with no store backing — the retraction residue class the
            // entity-only mix could never surface.
            Op::Assert(format!("{}({}).", rng.pick(PREDS), rng.pick(&["3", "7"])))
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

/// A structurally complex line (rule / existential / `du` / number-bearing) —
/// a summary STAT only, since the incremental-retraction branch was retired
/// (2026-08-01: it left retracted members in the quantifier domain) and every
/// retraction now takes the one rebuild path.
fn is_complex(line: &str) -> bool {
    line.contains("(every ")
        || line.contains("(some ")
        || line.contains(" = ")
        || line.chars().any(|c| c.is_ascii_digit())
}

/// Run one sequence: apply ops in order on the incremental engine; after every
/// retraction, compare the battery against a fresh engine replaying only the
/// surviving asserts (original order).
/// Session-configured rule execution settings ride the differential: applied
/// identically on both engines (override-at-registration makes call order
/// irrelevant), they must survive every rebuild a retraction performs —
/// retract ≡ never-asserted extends to the configuration. Heads from the
/// rule-head pool exercise both the positive-enable and the per-rule
/// NAF-refusal paths (generated NAF rules head `animal`/`alive` too).
fn apply_exec_settings(e: &nibli_engine::NibliEngine) {
    let kb = e.kb();
    kb.set_rule_forward("animal", true);
    kb.set_rule_priority("animal", 3);
    kb.set_rule_forward("alive", true);
}

pub fn run_retract_case(case: &RetractCase) -> RetractOutcome {
    let name = case.name.clone();
    let engine = crate::kr_engine();
    apply_exec_settings(&engine);

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
                apply_exec_settings(&fresh);
                for (l, _, alive) in &asserts {
                    if *alive && let Err(e) = fresh.assert_text(l) {
                        return RetractOutcome::Error {
                            name,
                            error: format!("replay '{l}': {e:?}"),
                        };
                    }
                }
                let mut battery: Vec<String> = Vec::new();
                for e in ENTS {
                    for p in PREDS {
                        battery.push(format!("{p}({e})."));
                    }
                }
                battery.push("Adam = Bel.".to_string());
                // QUANTIFIED battery: ground queries never read the domain
                // member caches, so retraction residue in `known_*`/the cached
                // member lists (a lingering member serving as a counterexample
                // or count subject) was invisible to the ground rows above.
                // Bare universals read the non-event cache directly; counts
                // read the full cache; the arithmetic universal is satisfiable
                // by NUMBERS only, so it pins the lingering-number class.
                for p in PREDS {
                    battery.push(format!("all $x: {p}($x)."));
                }
                battery.push("animal(exactly 1 dog).".to_string());
                battery.push("all $x: sum($x, 2, 2).".to_string());
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
                // The settings themselves are part of the metamorphic
                // property: after the rebuild this retraction performed, the
                // incremental engine's per-predicate rule execution settings
                // must equal the fresh engine's (which applied the same
                // setter calls and then asserted only the survivors).
                for p in PREDS {
                    let a = engine.kb().rule_execution_settings(p);
                    let b = fresh.kb().rule_execution_settings(p);
                    if a != b {
                        return RetractOutcome::Diverge {
                            name,
                            after_op: op_idx,
                            retracted_line: line,
                            query: format!("rule_execution_settings({p})"),
                            incremental: format!("{a:?}"),
                            fresh: format!("{b:?}"),
                        };
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
