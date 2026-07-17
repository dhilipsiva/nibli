//! The committed English corpus — the successor to the build-time
//! dictionary-en.json parse (the committed-corpus milestone).
//!
//! One strongly-typed, English-keyed table of [`PredicateEntry`] (sorted static
//! slice, binary-search lookup) plus a curated [`CompoundEntry`] table. The
//! data files are COMMITTED Rust (`corpus/predicates.rs` is generated once by
//! `tools/lexigen` and hand-refined in place; `corpus/compounds.rs` is
//! hand-authored). Invariants are enforced by CONST EVALUATION at compile time
//! (a bad hand edit is unshippable) with `#[test]` twins that re-run the same
//! logic and print the offender list (const panics cannot format names).
//!
//! Requirements made structural, not merely checked:
//! - **arity = `places.len()`** (1..=5) — no separate arity field to drift;
//! - **every place is NAMED**: each element of `places` is a non-empty,
//!   ident-shaped, non-reserved, non-`xN`-lookalike, entry-unique English
//!   label — "every arity must be named" cannot be violated by construction;
//! - a swapped (converted) entry names its canonical base BY TYPE ([`Swap`]).
//!
//! During the migration series this module coexists with the build.rs-generated
//! `DICTIONARY`/`ALIASES` (the bridge cross-check test pins their agreement);
//! at THE SWAP it becomes the only source.

/// Generation quality of an entry's place names (worst place wins). Everything
/// below `Lensisku` carries a greppable `TODO(corpus):` comment in the data
/// file (the refinement worklist; see the ratchet test).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CorpusTier {
    /// Hand-written or hand-verified labels.
    Curated,
    /// The lensisku export's ordered `place_keywords` (human-authored upstream).
    Lensisku,
    /// A content word before the place's `$x_N$` marker in the definition.
    Prose,
    /// x1 derived from a "$x_1$ is a/the <noun>" definition shape.
    GlossDerived,
    /// Positional English filler (`subject`/`object`/`place3`…) — the
    /// zero-positional backstop; deliberately drab so it self-advertises as
    /// unrefined wherever it renders.
    Generic,
}

/// A place-converted entry: the SURFACE argument order is `base`'s with
/// x1 ↔ x{with} exchanged (exactly what `Predicate::Converted` expresses).
#[derive(Clone, Copy, Debug)]
pub struct Swap {
    /// The exchanged place, `2..=arity` (const-checked).
    pub with: u8,
    /// The canonical (unswapped) entry's NAME — checked to exist, be
    /// unswapped, and share this entry's `source_gismu`.
    pub base: &'static str,
}

/// One committed corpus predicate — the former `DictEntry` + `AliasEntry`
/// merged into a single English-keyed record.
#[derive(Clone, Copy, Debug)]
pub struct PredicateEntry {
    /// The English predicate name — the only resolvable spelling and the IR
    /// relation name. Sorted-unique table key.
    pub name: &'static str,
    /// PROVENANCE ONLY: the source gismu this entry was generated from. Never
    /// resolvable as input; feeds the Predilex bridge and lexigen drift
    /// reports.
    pub source_gismu: &'static str,
    /// `None` = canonical entry (exactly one per `source_gismu`).
    pub swap: Option<Swap>,
    /// English place names in SURFACE order; `places.len()` IS the arity.
    pub places: &'static [&'static str],
    /// Single-word rendering gloss.
    pub gloss: &'static str,
    /// Curated English clause frame (`"{x1} goes to {x2} …"`); `None` = the
    /// renderer's generic gloss+arity frame.
    pub template: Option<&'static str>,
    pub tier: CorpusTier,
}

impl PredicateEntry {
    pub fn arity(&self) -> u8 {
        self.places.len() as u8
    }

    /// Resolve a place label (dictionary name, or the raw `x1..x5` escape
    /// hatch) to a 0-based place index.
    pub fn place_index(&self, label: &str) -> Option<usize> {
        place_index_of(self.places, label)
    }
}

/// A committed compound predicate (the lujvo-concept successor). Places are
/// HAND-AUTHORED — compound place structures are conventional, never derived
/// from the parts.
#[derive(Clone, Copy, Debug)]
pub struct CompoundEntry {
    /// The KR spelling and table key — contains `+` (`"computer+user"`),
    /// head-last by convention.
    pub name: &'static str,
    /// The IR relation name: `name` with `+` → `_` (const-checked equal to
    /// that derivation). NOT resolvable as KR input.
    pub relation: &'static str,
    /// Provenance: the source lujvo, when one exists.
    pub source_lujvo: Option<&'static str>,
    /// English place names; `places.len()` IS the arity (same rules as
    /// [`PredicateEntry::places`]).
    pub places: &'static [&'static str],
    pub gloss: &'static str,
    pub template: Option<&'static str>,
    pub tier: CorpusTier,
}

impl CompoundEntry {
    pub fn arity(&self) -> u8 {
        self.places.len() as u8
    }

    pub fn place_index(&self, label: &str) -> Option<usize> {
        place_index_of(self.places, label)
    }
}

fn place_index_of(places: &[&str], label: &str) -> Option<usize> {
    if let Some(i) = places.iter().position(|p| *p == label) {
        return Some(i);
    }
    // Raw x1..x5 escape hatch — always valid up to the arity.
    let rest = label.strip_prefix('x')?;
    if rest.len() != 1 {
        return None;
    }
    let d = rest.chars().next()?.to_digit(10)? as usize;
    if (1..=places.len()).contains(&d) {
        Some(d - 1)
    } else {
        None
    }
}

#[rustfmt::skip]
mod predicates;
mod compounds;

pub(crate) use compounds::COMPOUNDS;
pub(crate) use predicates::PREDICATES;

/// Look up a predicate by its English name (the only resolvable spelling).
pub fn corpus_predicate(name: &str) -> Option<&'static PredicateEntry> {
    PREDICATES
        .binary_search_by(|e| e.name.cmp(name))
        .ok()
        .map(|i| &PREDICATES[i])
}

/// Look up a compound by its `a+b` KR spelling.
pub fn corpus_compound(spelling: &str) -> Option<&'static CompoundEntry> {
    COMPOUNDS
        .binary_search_by(|e| e.name.cmp(spelling))
        .ok()
        .map(|i| &COMPOUNDS[i])
}

/// Iterate every predicate entry (sorted by name).
pub fn corpus_entries() -> impl Iterator<Item = &'static PredicateEntry> {
    PREDICATES.iter()
}

/// Iterate every compound entry (sorted by name).
pub fn corpus_compounds() -> impl Iterator<Item = &'static CompoundEntry> {
    COMPOUNDS.iter()
}

// ─────────────────────────────────────────────────────────────────────────────
// CONST VALIDATION — compile-time fail-closed. Cheap O(n)/O(n·labels) checks
// run in const eval (sortedness, per-entry shape); the O(n²) cross-entry
// checks (swap.base resolution, one-canonical-per-gismu, compound↔atomic
// collisions) live in the `#[test]` twins below, re-asserted per commit by
// `just test-alias-map` and the verify-alias-map gate.
// ─────────────────────────────────────────────────────────────────────────────

const fn bytes_lt(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    let mut i = 0;
    while i < a.len() && i < b.len() {
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
        i += 1;
    }
    a.len() < b.len()
}

const fn str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// Ident shape: `[a-z][a-z0-9_]*`.
const fn ident_ok(s: &str) -> bool {
    let b = s.as_bytes();
    if b.is_empty() || !b[0].is_ascii_lowercase() {
        return false;
    }
    let mut i = 1;
    while i < b.len() {
        if !(b[i].is_ascii_lowercase() || b[i].is_ascii_digit() || b[i] == b'_') {
            return false;
        }
        i += 1;
    }
    true
}

const fn is_reserved(s: &str) -> bool {
    let words = crate::reserved::RESERVED_WORDS;
    let mut i = 0;
    while i < words.len() {
        if str_eq(words[i], s) {
            return true;
        }
        i += 1;
    }
    false
}

/// `x1`..`x5` lookalike (would shadow the raw place-tag escape hatch).
const fn looks_like_place_tag(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() == 2 && b[0] == b'x' && b[1] >= b'1' && b[1] <= b'5'
}

/// `relation` must equal `name` with every `+` replaced by `_`.
const fn relation_matches_name(name: &str, relation: &str) -> bool {
    let (n, r) = (name.as_bytes(), relation.as_bytes());
    if n.len() != r.len() {
        return false;
    }
    let mut i = 0;
    while i < n.len() {
        let expect = if n[i] == b'+' { b'_' } else { n[i] };
        if r[i] != expect {
            return false;
        }
        i += 1;
    }
    true
}

const fn name_contains(s: &str, needle: u8) -> bool {
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == needle {
            return true;
        }
        i += 1;
    }
    false
}

/// `__` inside an atomic name would make the compound `+`→`_` relation map
/// non-injective.
const fn has_double_underscore(s: &str) -> bool {
    let b = s.as_bytes();
    let mut i = 1;
    while i < b.len() {
        if b[i] == b'_' && b[i - 1] == b'_' {
            return true;
        }
        i += 1;
    }
    false
}

const fn places_ok(places: &[&str]) -> bool {
    if places.is_empty() || places.len() > 5 {
        return false;
    }
    let mut i = 0;
    while i < places.len() {
        let p = places[i];
        if !ident_ok(p) || is_reserved(p) || looks_like_place_tag(p) {
            return false;
        }
        // Entry-unique labels.
        let mut j = 0;
        while j < i {
            if str_eq(places[j], p) {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

const fn validate_predicates(t: &[PredicateEntry]) {
    let mut i = 0;
    while i < t.len() {
        let e = &t[i];
        assert!(
            ident_ok(e.name),
            "corpus: predicate name is not ident-shaped"
        );
        assert!(
            !is_reserved(e.name),
            "corpus: predicate name is a KR keyword"
        );
        assert!(
            !has_double_underscore(e.name),
            "corpus: `__` in an atomic name breaks the compound relation map"
        );
        assert!(places_ok(e.places), "corpus: bad places (see test twin)");
        if let Some(s) = e.swap {
            assert!(
                s.with >= 2 && (s.with as usize) <= e.places.len(),
                "corpus: swap.with outside 2..=arity"
            );
        }
        if i + 1 < t.len() {
            assert!(
                bytes_lt(e.name, t[i + 1].name),
                "corpus: predicates not sorted-unique by name"
            );
        }
        i += 1;
    }
}

const fn validate_compounds(t: &[CompoundEntry]) {
    let mut i = 0;
    while i < t.len() {
        let e = &t[i];
        assert!(
            name_contains(e.name, b'+'),
            "corpus: compound name must contain '+'"
        );
        assert!(
            relation_matches_name(e.name, e.relation),
            "corpus: compound relation != name with '+'->'_'"
        );
        assert!(
            ident_ok(e.relation),
            "corpus: compound relation not ident-shaped"
        );
        assert!(places_ok(e.places), "corpus: bad compound places");
        if i + 1 < t.len() {
            assert!(
                bytes_lt(e.name, t[i + 1].name),
                "corpus: compounds not sorted-unique by name"
            );
        }
        i += 1;
    }
}

// The full-table walk is a few million interpreter steps — deliberate and
// bounded (it is the fail-closed corpus gate), so quiet the stuck-detector.
#[allow(long_running_const_eval)]
const _: () = validate_predicates(PREDICATES);
#[allow(long_running_const_eval)]
const _: () = validate_compounds(COMPOUNDS);

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{BTreeMap, BTreeSet};

    /// Diagnostic twin of the const validation: same rules, offender lists.
    #[test]
    fn corpus_shape_offenders() {
        let mut offenders = Vec::new();
        let mut prev: Option<&str> = None;
        for e in corpus_entries() {
            if let Some(p) = prev {
                if p >= e.name {
                    offenders.push(format!("order: {p:?} !< {:?}", e.name));
                }
            }
            prev = Some(e.name);
            if !ident_ok(e.name) || is_reserved(e.name) || has_double_underscore(e.name) {
                offenders.push(format!("name: {:?}", e.name));
            }
            if !places_ok(e.places) {
                offenders.push(format!("places: {:?} {:?}", e.name, e.places));
            }
            if let Some(s) = e.swap {
                if !(2..=e.places.len() as u8).contains(&s.with) {
                    offenders.push(format!("swap: {:?} x1↔x{}", e.name, s.with));
                }
            }
        }
        assert!(offenders.is_empty(), "{}", offenders.join("\n"));
    }

    /// Cross-entry invariants too heavy for const eval.
    #[test]
    fn corpus_cross_entry_invariants() {
        let mut offenders = Vec::new();

        // Exactly one canonical (unswapped) entry per source_gismu.
        let mut canonical: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for e in corpus_entries() {
            if e.swap.is_none() {
                canonical.entry(e.source_gismu).or_default().push(e.name);
            }
        }
        for (g, names) in &canonical {
            if names.len() > 1 {
                offenders.push(format!(
                    "gismu {g:?} has {} canonical entries: {names:?}",
                    names.len()
                ));
            }
        }

        // Every swap.base resolves to an unswapped entry with the same gismu.
        for e in corpus_entries() {
            if let Some(s) = e.swap {
                match corpus_predicate(s.base) {
                    None => offenders.push(format!("{:?}: swap.base {:?} absent", e.name, s.base)),
                    Some(b) => {
                        if b.swap.is_some() {
                            offenders.push(format!(
                                "{:?}: swap.base {:?} is itself swapped",
                                e.name, s.base
                            ));
                        }
                        if b.source_gismu != e.source_gismu {
                            offenders.push(format!(
                                "{:?}: swap.base {:?} has gismu {:?} != {:?}",
                                e.name, s.base, b.source_gismu, e.source_gismu
                            ));
                        }
                    }
                }
            }
        }

        // Compound relations collide with no atomic name and no other relation.
        let atomic: BTreeSet<&str> = corpus_entries().map(|e| e.name).collect();
        let mut relations: BTreeSet<&str> = BTreeSet::new();
        for c in corpus_compounds() {
            if atomic.contains(c.relation) {
                offenders.push(format!(
                    "compound relation {:?} shadows an atomic entry",
                    c.relation
                ));
            }
            if !relations.insert(c.relation) {
                offenders.push(format!("duplicate compound relation {:?}", c.relation));
            }
        }

        assert!(offenders.is_empty(), "{}", offenders.join("\n"));
    }

    /// TODO(corpus) ratchet: the marker count is pinned; refining an entry
    /// lowers it CONSCIOUSLY, a regen that adds guessed entries raises it in
    /// the same diff (mutants-baseline discipline for label quality).
    #[test]
    fn corpus_todo_ratchet() {
        let src = include_str!("corpus/predicates.rs");
        let todo_count = src.matches("TODO(corpus):").count();
        let guessed = corpus_entries()
            .filter(|e| e.tier > CorpusTier::Lensisku)
            .count();
        assert_eq!(
            todo_count, guessed,
            "TODO(corpus) markers ({todo_count}) must match entries with tier > Lensisku ({guessed}) — \
             refine = fix labels + set tier Curated + delete the marker"
        );
        assert_eq!(
            todo_count, CORPUS_TODO_BASELINE,
            "TODO(corpus) count moved — adjust CORPUS_TODO_BASELINE consciously in the same diff"
        );
    }

    /// Pinned by lexigen bootstrap; lower it as entries are refined.
    const CORPUS_TODO_BASELINE: usize = predicates::TODO_BASELINE;

    /// THE BRIDGE CROSS-CHECK (dies with build.rs at THE SWAP): every
    /// build.rs-generated alias must agree with the committed corpus on every
    /// shared field. In a FULL build this pins all ~1,342 entries (the
    /// load-bearing drift oracle before the swap); a fallback build pins the
    /// curated-core containment.
    #[test]
    fn bridge_cross_check_with_generated_artifacts() {
        let mut offenders = Vec::new();
        for (name, ae) in crate::ALIASES.entries() {
            let Some(e) = corpus_predicate(name) else {
                offenders.push(format!("{name}: absent from the committed corpus"));
                continue;
            };
            if e.source_gismu != ae.gismu {
                offenders.push(format!(
                    "{name}: source_gismu {:?} != generated {:?}",
                    e.source_gismu, ae.gismu
                ));
            }
            if e.arity() != ae.arity {
                offenders.push(format!(
                    "{name}: arity {} != generated {}",
                    e.arity(),
                    ae.arity
                ));
            }
            match (e.swap, ae.swap) {
                (None, None) => {}
                (Some(s), Some(k)) => {
                    if s.with != k {
                        offenders.push(format!("{name}: swap.with {} != generated {k}", s.with));
                    }
                    if Some(s.base) != crate::canonical_alias(ae.gismu) {
                        offenders.push(format!(
                            "{name}: swap.base {:?} != canonical_alias({:?})",
                            s.base, ae.gismu
                        ));
                    }
                }
                (a, b) => offenders.push(format!("{name}: swap {a:?} != generated {b:?}")),
            }
            for (i, label) in ae.place_labels.iter().enumerate() {
                if !label.is_empty() && e.places.get(i).copied() != Some(*label) {
                    offenders.push(format!(
                        "{name}: place x{} {:?} != generated {label:?}",
                        i + 1,
                        e.places.get(i)
                    ));
                }
            }
            if let Some(d) = crate::DICTIONARY.get(ae.gismu) {
                if e.gloss != d.gloss {
                    offenders.push(format!(
                        "{name}: gloss {:?} != generated {:?}",
                        e.gloss, d.gloss
                    ));
                }
                let corpus_template = e.template.unwrap_or("");
                if corpus_template != d.template {
                    offenders.push(format!(
                        "{name}: template {corpus_template:?} != generated {:?}",
                        d.template
                    ));
                }
            }
        }
        assert!(offenders.is_empty(), "{}", offenders.join("\n"));
        // Full build: exact cardinality (no extra corpus entries either).
        if crate::ALIASES.len() >= 1000 {
            assert_eq!(
                PREDICATES.len(),
                crate::ALIASES.len(),
                "corpus and generated alias map must have the same entry count in a full build"
            );
        }
    }

    #[test]
    fn lookup_and_place_index() {
        let goes = corpus_predicate("goes").expect("goes in corpus");
        assert_eq!(goes.arity(), 5);
        assert_eq!(goes.source_gismu, "klama");
        assert_eq!(goes.place_index("destination"), Some(1));
        assert_eq!(goes.place_index("x1"), Some(0));
        assert_eq!(goes.place_index("x9"), None);
        assert!(corpus_predicate("klama").is_none(), "gismu never resolve");
        let cu = corpus_compound("computer+user").expect("seed compound");
        assert_eq!(cu.relation, "computer_user");
        assert!(corpus_compound("dog+cat").is_none(), "undefined compound");
    }
}
