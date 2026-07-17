//! Deterministic property-based generator of NAF-free definite-Horn cases for the differential
//! gate. Each case is a random taxonomy program — `P(X).` facts, `X = Y.` identity links, and
//! `Q(every P).` universal rules over a small fallback-dictionary vocabulary — plus a random
//! atomic (or identity) query. Every case is in the mappable
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

/// Class/property predicates (curated English aliases), all present in the in-tree
/// FALLBACK alias map — so generated cases resolve in CI with no data file. Used
/// one-place as `<pred>(X).` (arity padding fills the rest with unspecified).
const PREDS: &[&str] = &[
    "dog",
    "cat",
    "animal",
    "alive",
    "person",
    "dead",
    "fast",
    "big",
    "small",
    "beautiful",
    "blue",
    "red",
    "yellow",
    "green",
];

/// KR rigid Names (Capitalized).
const ENTITIES: &[&str] = &["Adam", "Bel", "Kim", "Dan", "Tam"];

/// Tense prefixes for facts/queries: mostly bare, sometimes pu/ca/ba. Facts are
/// flavor-exact and unmarked rules are flavor-polymorphic (see `tense::flavorize`),
/// so mixing flavors into facts + query exercises the isolation diagonal AND the
/// polymorphic rule firing against the oracles.
const TENSES: &[&str] = &["", "past ", "now ", "future "];

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
        // 1-in-3 BARE facts become an And-fact operator claim (one constant
        // subject, two positive conjuncts — the KR twin of the retired GIhA
        // bridi-tail shape): Horn/NAF-free and mappable, so the Vampire sweep
        // differentially checks the conjunct derivations. Tensed facts stay
        // atomic (a tense prefix applies per claim, which the flavorizer
        // models only for atomic facts — conservative).
        if tense.is_empty() && rng.below(3) == 0 {
            let e = rng.pick(ENTITIES);
            kb.push(format!(
                "{}({e}) & {}({e}).",
                rng.pick(PREDS),
                rng.pick(PREDS)
            ));
        } else {
            kb.push(format!(
                "{tense}{}({}).",
                rng.pick(PREDS),
                rng.pick(ENTITIES)
            ));
        }
    }
    // 0..=2 identity links `E1 = E2.` — nibli resolves these through its union-find
    // equivalence index; the Vampire side sees native `=` (congruence), so the mix
    // exercises substitutivity through fact lookup AND rule firing. A self-link
    // (`E = E`) or a duplicate link is harmless (reflexivity / idempotent union).
    let n_equals = rng.below(3);
    for _ in 0..n_equals {
        kb.push(format!("{} = {}.", rng.pick(ENTITIES), rng.pick(ENTITIES)));
    }
    // 0..=3 universal (Horn) rules `Q(every P).`. Cycles are fine — definite Horn stays sound;
    // nibli may cut a cycle to Unknown, which the gate simply skips.
    let n_rules = rng.below(4);
    for _ in 0..n_rules {
        kb.push(format!("{}(every {}).", rng.pick(PREDS), rng.pick(PREDS)));
    }
    // Mostly an atomic `[tense] P(E).` query (bare with probability 1/2, else a
    // flavor — exercising both the diagonal and the off-diagonal FALSE sides);
    // 1-in-5 an identity query `E1 = E2.` (never tensed — tensed `du` is outside
    // both oracle fragments).
    let query = if rng.below(5) == 0 {
        format!("{} = {}.", rng.pick(ENTITIES), rng.pick(ENTITIES))
    } else {
        let tense = if rng.below(2) == 0 {
            ""
        } else {
            rng.pick(&TENSES[1..])
        };
        format!("{tense}{}({}).", rng.pick(PREDS), rng.pick(ENTITIES))
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
const NAF_BASE: &[&str] = &["dog", "cat", "dead", "fast"];

/// DERIVED predicates: used ONLY as rule heads (and positive Horn-rule bodies) — never
/// negated. Disjoint from [`NAF_BASE`].
const NAF_DERIVED: &[&str] = &["animal", "alive", "beautiful", "big"];

/// The fixed domain type every entity is asserted to have (so the
/// `every person where ~R` rule has a non-empty, safe domain to range over).
const NAF_DOMAIN: &str = "person";

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
    kb.push(format!("{q}(every {NAF_DOMAIN} where ~{r})."));

    // Optionally a positive Horn chain Q → S (S derived; positive edges never break
    // stratification), extending what a domain member can derive.
    let mut derivable = vec![q];
    if rng.below(2) == 0 {
        let s = rng.pick(NAF_DERIVED);
        kb.push(format!("{s}(every {q})."));
        derivable.push(s);
    }

    // 1..=2 entities: each is a domain member; each MAY carry the R witness (which blocks Q).
    let n_ent = 1 + rng.below(2);
    let mut ents: Vec<&'static str> = Vec::new();
    for _ in 0..n_ent {
        let e = rng.pick(ENTITIES);
        kb.push(format!("{NAF_DOMAIN}({e})."));
        if rng.below(2) == 0 {
            kb.push(format!("{r}({e})."));
        }
        ents.push(e);
    }

    // Optionally merge two entities with an identity link — the NAF-THROUGH-EQUALITY shape:
    // an R-witness on either side of the link blocks the rule for BOTH (nibli sees it via
    // the union-find; clingo sees one canonicalized constant). `du` is resolved by the
    // equivalence index, not a rule head, so stratification is untouched.
    if ents.len() == 2 && rng.below(3) == 0 {
        kb.push(format!("{} = {}.", ents[0], ents[1]));
    }

    let qe = ents[rng.below(ents.len())];
    let qp = derivable[rng.below(derivable.len())];
    let query = format!("{qp}({qe}).");

    GeneratedCase {
        name: format!("naf_seed{seed}"),
        kb,
        query,
    }
}

/// Digits for the exact-count quantifier `Q(exactly N P).` (1, 2, 3).
const COUNT_DIGITS: &[&str] = &["1", "2", "3"];

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
        kb.push(format!("{p}({e})."));
    }

    // ~1 in 3: a du link (two distinct pool entities become one countable entity).
    if rng.below(3) == 0 {
        let a = ents[rng.below(ents.len())];
        let b = ents[rng.below(ents.len())];
        if a != b {
            kb.push(format!("{a} = {b}."));
        }
    }
    // ~1 in 3: a universal taxonomy rule (derived body facts count; the rule's
    // presupposition witness must not).
    if rng.below(3) == 0 {
        let pa = preds[rng.below(preds.len())];
        let pb = preds[rng.below(preds.len())];
        if pa != pb {
            kb.push(format!("{pb}(every {pa})."));
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
    let query = format!("{p2}(exactly {digit} {p1}).");

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
    fn and_production_appears_in_random_case() {
        // The 1-in-3 bare-fact And-claim production (the KR twin of the retired
        // GIhA shape) must actually fire across seeds — it feeds the Vampire sweep.
        let hits = (0u64..100)
            .filter(|&s| random_case(s).kb.iter().any(|l| l.contains(" & ")))
            .count();
        assert!(
            hits > 15,
            "And-facts under-represented in random_case: {hits}"
        );
    }

    #[test]
    fn well_formed_mappable_shape() {
        // Every generated line is a fact / And-fact / identity link (optionally
        // tense-prefixed facts — past/now/future are in-fragment via
        // `tense::flavorize`) or a Horn rule over the fallback vocabulary —
        // and nothing carries `~` (genuine negation) or any other shape that
        // would leave the mappable fragment.
        for seed in 0u64..50 {
            let c = random_case(seed);
            assert!(!c.kb.is_empty());
            for line in c.kb.iter().chain(std::iter::once(&c.query)) {
                let body = line
                    .strip_prefix("past ")
                    .or_else(|| line.strip_prefix("now "))
                    .or_else(|| line.strip_prefix("future "))
                    .unwrap_or(line);
                let is_rule = body.contains("(every ");
                let is_equals = body.contains(" = ");
                let is_and = body.contains(" & ");
                let is_fact = body.ends_with(").")
                    && body
                        .chars()
                        .next()
                        .is_some_and(|ch| ch.is_ascii_lowercase());
                assert!(
                    is_rule || is_equals || is_and || is_fact,
                    "unexpected generated line: {line}"
                );
                // A tense prefix only ever appears on an atomic fact/query —
                // never a rule, And-fact, or identity link.
                assert!(
                    body == line || (is_fact && !is_rule && !is_equals && !is_and),
                    "tense prefix on a non-atomic line: {line}"
                );
                assert!(
                    !line.contains('~'),
                    "generated line left the fragment (negation): {line}"
                );
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
        // Every generated NAF case has EXACTLY one `where ~R` line, and its negated
        // predicate R is always a BASE predicate — never a rule head. That is the
        // stratification invariant: a base predicate has no incoming rule edge, so no
        // negative edge can lie inside an SCC. (If this held falsely, nibli would reject
        // the KB at assert time and the gate would surface an Error, but we pin it
        // structurally here too.)
        for seed in 0u64..100 {
            let c = random_naf_case(seed);
            let naf_lines: Vec<&String> = c.kb.iter().filter(|l| l.contains("where ~")).collect();
            assert_eq!(naf_lines.len(), 1, "expected one NAF rule: {:?}", c.kb);
            let neg = naf_lines[0]
                .split("where ~")
                .nth(1)
                .map(|rest| rest.trim_end_matches(")."))
                .expect("a negated predicate after `where ~`");
            assert!(
                NAF_BASE.contains(&neg),
                "negated predicate '{neg}' must be a BASE predicate (never a head): {:?}",
                c.kb
            );
            // The head Q is derived; heads never appear in NAF_BASE.
            for line in &c.kb {
                if line.contains("(every ") {
                    let head = line.split('(').next().unwrap_or("").trim();
                    assert!(
                        !NAF_BASE.contains(&head),
                        "a base predicate appeared as a rule head: {line}"
                    );
                }
            }
        }
    }
}
