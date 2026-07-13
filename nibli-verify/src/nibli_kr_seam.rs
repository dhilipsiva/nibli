//! KR→smuni seam helpers — the metamorphic-pair generator behind the
//! front-end gate in `tests/nibli_kr_seam_gate.rs`.
//!
//! That gate is the KR front-end's independent correctness oracle, built to
//! OUTLIVE the Lojban front-end — and it did: THE DROP (2026-07-13) deleted
//! gerna and the twin battery, and this gate has carried the coverage since,
//! re-anchored on hand-verified FOL structure + KR-internal metamorphic
//! relations, touching no Lojban text.
//!
//! This module owns only the seeded pair generator; the compile/canonicalize
//! plumbing is shared: [`crate::nibli_kr_battery::kompile`] +
//! [`crate::seam::canonicalize`] (both buffer-level, front-end-agnostic).
//!
//! Vocabulary is FALLBACK-SAFE (curated-core aliases only), like the
//! construct inventory — the gate runs full-strength in both dictionary
//! modes and never skips.

/// Same LCG as `seam.rs`/`generator.rs` — deterministic, no rng crate.
fn lcg(seed: u64) -> u64 {
    seed.wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407)
}

/// 2+-place curated predicates for the label-permutation family.
const PERM_PREDS: &[&str] = &["loves", "eats", "sees", "likes", "uses"];
/// Term spellings (pro-terms + rigid names) for argument slots.
const PERM_ENTS: &[&str] = &["me", "you", "Adam", "Betis"];
/// Predicates taking a determiner phrase at x1 for the `no`-sugar family.
const NO_PREDS: &[&str] = &["goes", "eats", "big", "beautiful"];
/// Curated restrictor nouns.
const RESTRS: &[&str] = &["dog", "cat", "person", "animal"];
/// Curated 1-place-ish body predicates for relative-clause bodies.
const BODY_PREDS: &[&str] = &["big", "fast", "small", "red"];

/// One seeded KR-internal metamorphic pair: two DIFFERENT spellings the spec
/// pins to the SAME compiled logic (canonicalized `LogicBuffer` equality).
/// Three families, rotated by seed:
///
/// 1. **Label permutation** — `P(A, B).` ≡ `P(x2: B, x1: A).` (raw `xN`
///    labels resolve for every predicate; NIBLI_KR §5 named args are
///    order-free once labeled).
/// 2. **The `no` sugar** — `Q(no R).` ≡ `Q(exactly 0 R).` (§4: `no X` parses
///    as `Exactly(0)`).
/// 3. **Conjoined ≡ stacked clause bodies** — `P(every R where a(it) & b(it)).`
///    ≡ `P(every R where a where b).` (§7: conjoining inside one clause and
///    stacking clauses both compile to the AND-conjoined restrictor).
pub fn metamorphic_pair(seed: u64) -> (String, String) {
    let mut s = lcg(seed);
    let mut pick = |xs: &[&str]| -> String {
        s = lcg(s);
        xs[((s >> 33) as usize) % xs.len()].to_string()
    };
    match seed % 3 {
        0 => {
            let p = pick(PERM_PREDS);
            let a = pick(PERM_ENTS);
            let b = pick(PERM_ENTS);
            (format!("{p}({a}, {b})."), format!("{p}(x2: {b}, x1: {a})."))
        }
        1 => {
            let q = pick(NO_PREDS);
            let r = pick(RESTRS);
            (format!("{q}(no {r})."), format!("{q}(exactly 0 {r})."))
        }
        _ => {
            let p = pick(NO_PREDS);
            let r = pick(RESTRS);
            let a = pick(BODY_PREDS);
            // Distinct second body predicate, so the pair exercises a real
            // two-conjunct restrictor.
            let mut b = pick(BODY_PREDS);
            if b == a {
                b = BODY_PREDS
                    [(BODY_PREDS.iter().position(|x| *x == a).unwrap() + 1) % BODY_PREDS.len()]
                .to_string();
            }
            (
                format!("{p}(every {r} where {a}(it) & {b}(it))."),
                format!("{p}(every {r} where {a} where {b})."),
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pairs_are_deterministic() {
        for seed in 0..12 {
            assert_eq!(metamorphic_pair(seed), metamorphic_pair(seed));
        }
        assert_ne!(metamorphic_pair(0), metamorphic_pair(3));
    }

    #[test]
    fn all_families_appear_and_compile() {
        let mut families = [false; 3];
        for seed in 0..12 {
            families[(seed % 3) as usize] = true;
            let (a, b) = metamorphic_pair(seed);
            crate::nibli_kr_battery::kompile(&a)
                .unwrap_or_else(|e| panic!("pair side a {a:?}: {e}"));
            crate::nibli_kr_battery::kompile(&b)
                .unwrap_or_else(|e| panic!("pair side b {b:?}: {e}"));
        }
        assert!(families.iter().all(|f| *f), "a family never generated");
    }
}
