//! Deterministic property-based generator of NAF-free definite-Horn cases for the differential
//! gate. Each case is a random taxonomy program — `la .X. cu P` facts and `ro lo P cu Q`
//! universal rules over a small fallback-dictionary vocabulary — plus a random atomic query.
//! Every case is in the mappable classical fragment **by construction** (no negation, no
//! numbers, no tense/deontic/compute), so it broadens differential soundness coverage without
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

/// Small deterministic LCG so a seed reproduces a case exactly (no rng crate; CI must be
/// reproducible).
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407))
    }

    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn pick(&mut self, xs: &[&'static str]) -> &'static str {
        xs[self.below(xs.len())]
    }
}

/// Generate the case for `seed`. Deterministic: the same seed always yields the same case.
pub fn random_case(seed: u64) -> GeneratedCase {
    let mut rng = Lcg::new(seed);
    let mut kb: Vec<String> = Vec::new();

    // 1..=3 ground facts `la .E. cu P`.
    let n_facts = 1 + rng.below(3);
    for _ in 0..n_facts {
        kb.push(format!(
            "la .{}. cu {}",
            rng.pick(ENTITIES),
            rng.pick(PREDS)
        ));
    }
    // 0..=3 universal (Horn) rules `ro lo P cu Q`. Cycles are fine — definite Horn stays sound;
    // nibli may cut a cycle to Unknown, which the gate simply skips.
    let n_rules = rng.below(4);
    for _ in 0..n_rules {
        kb.push(format!("ro lo {} cu {}", rng.pick(PREDS), rng.pick(PREDS)));
    }
    let query = format!("la .{}. cu {}", rng.pick(ENTITIES), rng.pick(PREDS));

    GeneratedCase {
        name: format!("rand_seed{seed}"),
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
        // Every generated line is a fact or a Horn rule over the fallback vocabulary — and no
        // whitespace-delimited TOKEN is a negation / number / tense / abstraction cmavo that
        // would leave the mappable fragment. (Token check, not substring — `prenu` legitimately
        // contains "nu".)
        const BAD_TOKENS: &[&str] = &[
            "na", "naku", "na'i", "li", "nu", "du'u", "ka", "ni", "si'o", "pu", "ca", "ba", "ei",
        ];
        for seed in 0u64..50 {
            let c = random_case(seed);
            assert!(!c.kb.is_empty());
            for line in c.kb.iter().chain(std::iter::once(&c.query)) {
                assert!(
                    line.starts_with("la .") || line.starts_with("ro lo "),
                    "unexpected generated line: {line}"
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
}
