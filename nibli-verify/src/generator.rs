//! Deterministic property-based generator of NAF-free definite-Horn cases for the differential
//! gate. Each case is a random taxonomy program — `la .X. cu P` facts, `la .X. cu du la .Y.`
//! identity links, and `ro lo P cu Q` universal rules over a small fallback-dictionary
//! vocabulary — plus a random atomic (or identity) query. Every case is in the mappable
//! classical fragment **by construction** (no negation, no numbers, no tense/deontic/compute;
//! ground `du` maps to native `=`), so it broadens differential soundness coverage without
//! ever leaving the fragment the gate can judge. The filter in `run_lines` is still the final
//! arbiter, so even a case that somehow compiled outside the fragment is skipped, never
//! mis-judged.

/// One generated case: owned strings (unlike the curated `&'static` [`crate::Case`]).
pub struct GeneratedCase {
    pub name: String,
    pub kb: Vec<String>,
    pub query: String,
}

/// Class/property gismu, all present in the in-tree FALLBACK dictionary — so generated cases
/// resolve in CI with no data file. Used one-place as `la .X. cu <pred>` (arity padding fills
/// the rest with `zo'e`).
const PREDS: &[&str] = &[
    "gerku", "mlatu", "danlu", "jmive", "prenu", "morsi", "sutra", "barda", "cmalu", "melbi",
    "blanu", "xunre", "pelxu", "crino",
];

/// cmevla (proper names), each ending in a consonant (a Lojban cmevla requirement).
const ENTITIES: &[&str] = &["adam", "bel", "kim", "dan", "tam"];

/// Tense prefixes for facts/queries: mostly bare, sometimes pu/ca/ba. Facts are
/// flavor-exact and unmarked rules are flavor-polymorphic (see `tense::flavorize`),
/// so mixing flavors into facts + query exercises the isolation diagonal AND the
/// polymorphic rule firing against the oracles.
const TENSES: &[&str] = &["", "pu ", "ca ", "ba "];

/// Small deterministic LCG so a seed reproduces a case exactly (no rng crate; CI must be
/// reproducible).
pub(crate) struct Lcg(pub(crate) u64);

impl Lcg {
    pub(crate) fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407))
    }

    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    pub(crate) fn pick(&mut self, xs: &[&'static str]) -> &'static str {
        xs[self.below(xs.len())]
    }
}

/// Generate the case for `seed`. Deterministic: the same seed always yields the same case.
pub fn random_case(seed: u64) -> GeneratedCase {
    let mut rng = Lcg::new(seed);
    let mut kb: Vec<String> = Vec::new();

    // 1..=3 ground facts `[pu/ca/ba] la .E. cu P` — each fact bare with probability
    // 1/2, else a uniformly-picked flavor (flavor-exact isolation is the engine
    // semantics the flavorizer mirrors).
    let n_facts = 1 + rng.below(3);
    for _ in 0..n_facts {
        let tense = if rng.below(2) == 0 {
            ""
        } else {
            rng.pick(&TENSES[1..])
        };
        kb.push(format!(
            "{tense}la .{}. cu {}",
            rng.pick(ENTITIES),
            rng.pick(PREDS)
        ));
    }
    // 0..=2 identity links `la .E1. cu du la .E2.` — nibli resolves these through its
    // union-find equivalence index; the Vampire side sees native `=` (congruence), so the
    // mix exercises substitutivity through fact lookup AND rule firing. A self-link
    // (`E du E`) or a duplicate link is harmless (reflexivity / idempotent union).
    let n_du = rng.below(3);
    for _ in 0..n_du {
        kb.push(format!(
            "la .{}. cu du la .{}.",
            rng.pick(ENTITIES),
            rng.pick(ENTITIES)
        ));
    }
    // 0..=3 universal (Horn) rules `ro lo P cu Q`. Cycles are fine — definite Horn stays sound;
    // nibli may cut a cycle to Unknown, which the gate simply skips.
    let n_rules = rng.below(4);
    for _ in 0..n_rules {
        kb.push(format!("ro lo {} cu {}", rng.pick(PREDS), rng.pick(PREDS)));
    }
    // Mostly an atomic `[tense] la .E. cu P` query (bare with probability 1/2, else a
    // flavor — exercising both the diagonal and the off-diagonal FALSE sides);
    // 1-in-5 an identity query `la .E1. cu du la .E2.` (never tensed — tensed `du`
    // is outside both oracle fragments).
    let query = if rng.below(5) == 0 {
        format!(
            "la .{}. cu du la .{}.",
            rng.pick(ENTITIES),
            rng.pick(ENTITIES)
        )
    } else {
        let tense = if rng.below(2) == 0 {
            ""
        } else {
            rng.pick(&TENSES[1..])
        };
        format!("{tense}la .{}. cu {}", rng.pick(ENTITIES), rng.pick(PREDS))
    };

    GeneratedCase {
        name: format!("rand_seed{seed}"),
        kb,
        query,
    }
}

/// BASE predicates: used ONLY in facts and as the negated restrictor `R`. Because a base
/// predicate is never a rule head, no negative edge can ever close an SCC — every generated
/// NAF program is **stratified by construction**, for every seed.
const NAF_BASE: &[&str] = &["gerku", "mlatu", "morsi", "sutra"];

/// DERIVED predicates: used ONLY as rule heads (and positive Horn-rule bodies) — never
/// negated. Disjoint from [`NAF_BASE`].
const NAF_DERIVED: &[&str] = &["danlu", "jmive", "melbi", "barda"];

/// The fixed domain type every entity is asserted to have (so the `ro lo prenu poi na R`
/// rule has a non-empty, safe domain to range over).
const NAF_DOMAIN: &str = "prenu";

/// Generate a random **stratified negation-as-failure** case for `seed`: a domain, one
/// `ro lo prenu poi na R cu Q` NAF rule (`R` base, `Q` derived), an optional positive Horn
/// chain among derived predicates, and 1..=2 domain-member entities that may or may not
/// carry the `R` witness. Stratified by construction (see [`NAF_BASE`]); in the ASP-mappable
/// fragment by construction (plain gismu, `poi na`, no compute/tense/deontic; an optional ground `du` link is canonicalized by the translator). The filter
/// in `run_lines_asp` is still the final arbiter, so a case outside the fragment is skipped,
/// never mis-judged.
pub fn random_naf_case(seed: u64) -> GeneratedCase {
    let mut rng = Lcg::new(seed);
    let mut kb: Vec<String> = Vec::new();

    let r = rng.pick(NAF_BASE); // negated restrictor (base predicate)
    let q = rng.pick(NAF_DERIVED); // NAF-rule head (derived predicate)

    // The stratified NAF rule: a domain member with no R-witness gets Q.
    kb.push(format!("ro lo {NAF_DOMAIN} poi na {r} cu {q}"));

    // Optionally a positive Horn chain Q → S (S derived; positive edges never break
    // stratification), extending what a domain member can derive.
    let mut derivable = vec![q];
    if rng.below(2) == 0 {
        let s = rng.pick(NAF_DERIVED);
        kb.push(format!("ro lo {q} cu {s}"));
        derivable.push(s);
    }

    // 1..=2 entities: each is a domain member; each MAY carry the R witness (which blocks Q).
    let n_ent = 1 + rng.below(2);
    let mut ents: Vec<&'static str> = Vec::new();
    for _ in 0..n_ent {
        let e = rng.pick(ENTITIES);
        kb.push(format!("la .{e}. cu {NAF_DOMAIN}"));
        if rng.below(2) == 0 {
            kb.push(format!("la .{e}. cu {r}"));
        }
        ents.push(e);
    }

    // Optionally merge two entities with an identity link — the NAF-THROUGH-EQUALITY shape:
    // an R-witness on either side of the link blocks the rule for BOTH (nibli sees it via
    // the union-find; clingo sees one canonicalized constant). `du` is resolved by the
    // equivalence index, not a rule head, so stratification is untouched.
    if ents.len() == 2 && rng.below(3) == 0 {
        kb.push(format!("la .{}. cu du la .{}.", ents[0], ents[1]));
    }

    let qe = ents[rng.below(ents.len())];
    let qp = derivable[rng.below(derivable.len())];
    let query = format!("la .{qe}. cu {qp}");

    GeneratedCase {
        name: format!("naf_seed{seed}"),
        kb,
        query,
    }
}

/// Lojban digits for the exact-count quantifier `PA lo P cu Q` (1, 2, 3).
const COUNT_DIGITS: &[&str] = &["pa", "re", "ci"];

/// Generate a random **exact-count** case for `seed`: 2..=5 ground facts over a small
/// entity/predicate pool, plus one `PA lo P1 cu P2` query. Both TRUE and FALSE sides
/// arise naturally from the random fact/quantifier mix. Since the 2026-07-02
/// count-semantics decision (entity-level counting), the fragment also mixes in the
/// formerly-guarded shapes: a `du` link between two pool entities (~1 in 3 — the
/// engine counts one representative per equivalence class, matching the translator's
/// canonicalization) and a universal taxonomy rule (~1 in 3 — the engine excludes the
/// xorlo presupposition witness from counting, and the ASP program never had one).
pub fn random_count_case(seed: u64) -> GeneratedCase {
    let mut rng = Lcg::new(seed);
    let mut kb: Vec<String> = Vec::new();

    // A small pool keeps collisions (several entities sharing a predicate) frequent,
    // so counts of 1..3 actually occur.
    let preds = &PREDS[..4];
    let ents = &ENTITIES[..4];
    let n_facts = 2 + rng.below(4);
    for _ in 0..n_facts {
        let e = ents[rng.below(ents.len())];
        let p = preds[rng.below(preds.len())];
        kb.push(format!("la .{e}. cu {p}"));
    }

    // ~1 in 3: a du link (two distinct pool entities become one countable entity).
    if rng.below(3) == 0 {
        let a = ents[rng.below(ents.len())];
        let b = ents[rng.below(ents.len())];
        if a != b {
            kb.push(format!("la .{a}. du la .{b}."));
        }
    }
    // ~1 in 3: a universal taxonomy rule (derived body facts count; the rule's
    // presupposition witness must not).
    if rng.below(3) == 0 {
        let pa = preds[rng.below(preds.len())];
        let pb = preds[rng.below(preds.len())];
        if pa != pb {
            kb.push(format!("ro lo {pa} cu {pb}"));
        }
    }

    let p1 = preds[rng.below(preds.len())];
    // Half the time count `P1 cu P1` (how many P1s), half the time a distinct body.
    let p2 = if rng.below(2) == 0 {
        p1
    } else {
        preds[rng.below(preds.len())]
    };
    let digit = rng.pick(COUNT_DIGITS);
    let query = format!("{digit} lo {p1} cu {p2}");

    GeneratedCase {
        name: format!("count_seed{seed}"),
        kb,
        query,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic() {
        // Same seed → identical case; the gate must be reproducible.
        let a = random_case(42);
        let b = random_case(42);
        assert_eq!(a.name, b.name);
        assert_eq!(a.kb, b.kb);
        assert_eq!(a.query, b.query);
        assert_ne!(random_case(1).kb, random_case(2).kb);
    }

    #[test]
    fn well_formed_mappable_shape() {
        // Every generated line is a fact (optionally tense-prefixed — pu/ca/ba are now
        // in-fragment via `tense::flavorize`) or a Horn rule over the fallback
        // vocabulary — and no whitespace-delimited TOKEN is a negation / number /
        // abstraction cmavo that would leave the mappable fragment. (Token check, not
        // substring — `prenu` legitimately contains "nu".)
        const BAD_TOKENS: &[&str] = &[
            "na", "naku", "na'i", "li", "nu", "du'u", "ka", "ni", "si'o", "ei",
        ];
        for seed in 0u64..50 {
            let c = random_case(seed);
            assert!(!c.kb.is_empty());
            for line in c.kb.iter().chain(std::iter::once(&c.query)) {
                let body = line
                    .strip_prefix("pu ")
                    .or_else(|| line.strip_prefix("ca "))
                    .or_else(|| line.strip_prefix("ba "))
                    .unwrap_or(line);
                assert!(
                    body.starts_with("la .") || body.starts_with("ro lo "),
                    "unexpected generated line: {line}"
                );
                // A tense prefix only ever appears on a fact/query, never a rule.
                assert!(
                    body == line || body.starts_with("la ."),
                    "tense prefix on a non-fact line: {line}"
                );
                for tok in line.split_whitespace() {
                    assert!(
                        !BAD_TOKENS.contains(&tok),
                        "generated line left the fragment (token '{tok}'): {line}"
                    );
                }
            }
        }
    }

    #[test]
    fn naf_case_deterministic() {
        let a = random_naf_case(7);
        let b = random_naf_case(7);
        assert_eq!(a.kb, b.kb);
        assert_eq!(a.query, b.query);
    }

    #[test]
    fn naf_case_stratified_by_construction() {
        // Every generated NAF case has EXACTLY one `poi na R` line, and its negated predicate
        // R is always a BASE predicate — never a rule head. That is the stratification
        // invariant: a base predicate has no incoming rule edge, so no negative edge can lie
        // inside an SCC. (If this held falsely, nibli would reject the KB at assert time and
        // the gate would surface an Error, but we pin it structurally here too.)
        for seed in 0u64..100 {
            let c = random_naf_case(seed);
            let naf_lines: Vec<&String> = c.kb.iter().filter(|l| l.contains("poi na ")).collect();
            assert_eq!(naf_lines.len(), 1, "expected one NAF rule: {:?}", c.kb);
            let neg = naf_lines[0]
                .split("poi na ")
                .nth(1)
                .and_then(|rest| rest.split_whitespace().next())
                .expect("a negated predicate after `poi na`");
            assert!(
                NAF_BASE.contains(&neg),
                "negated predicate '{neg}' must be a BASE predicate (never a head): {:?}",
                c.kb
            );
            // The head Q is derived; heads never appear in NAF_BASE.
            for line in &c.kb {
                if line.starts_with("ro lo ") {
                    let head = line.rsplit(" cu ").next().unwrap_or("").trim();
                    assert!(
                        !NAF_BASE.contains(&head),
                        "a base predicate appeared as a rule head: {line}"
                    );
                }
            }
        }
    }
}
