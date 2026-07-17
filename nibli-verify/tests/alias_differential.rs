//! Alias-map differential — the `verify-alias-map` gate (`just verify-alias-map`).
//!
//! Since the dictionary fold, the forward dictionary and the alias map are ONE
//! crate (`nibli-lexicon`) built from a SINGLE parse, so the alias arity and the
//! shipped dictionary arity agree BY CONSTRUCTION — the old cross-crate drift
//! (the dilcu=3/jmive=1 fallback flap this gate was born to catch) is now
//! structurally impossible. What survives has independent value as INTRA-crate
//! invariants over the SHIPPED artifacts:
//!
//! Two tests, both dual-mode and never skipping (the verify contract):
//! 1. `alias_map_differential` — structural: per-alias arity equality against
//!    `nibli_lexicon::get_arity` (now a self-consistency check), `GISMU_TO_ALIAS`
//!    round-trips, swap validity (`2..=arity`, involution), reserved-word
//!    exclusion and label integrity re-asserted from the shipped map, coverage
//!    floors.
//! 2. `alias_behavioral_battery` — for EVERY shipped alias, `alias(A, B, …)`
//!    compiled through nibli-kr+nibli-semantics must equal its twin at the
//!    canonicalized-LogicBuffer level: a PLAIN alias twins with ITSELF under
//!    explicit `xN:` labels (named ≡ positional routing), a CONVERTED alias
//!    twins with its CANONICAL BASE alias under the permuted labels its surface
//!    order implies — the cross-entry conversion oracle. (The old raw-gismu
//!    identity-passthrough twin retired with the committed-corpus milestone:
//!    gismu spellings stop resolving as input.)
//!
//! Mode is read from the shipped artifact (`DICTIONARY.len()` — a compile-time
//! phf property; checking the json file's presence could lie about a stale build).

use nibli_verify::nibli_kr_battery::{canonical, kompile};

/// Full-build detector, shared convention with the predilex gate: the fallback
/// artifacts have ~99/~140 entries, full builds ~1,341/~10.9k.
const FULL_DICT_MIN: usize = 1000;

/// Argument constants for the behavioral battery.
const ARG_NAMES: [&str; 5] = ["Adam", "Bob", "Kim", "Tom", "Sam"];

/// Detect the build mode from the shipped dictionary and print the fallback
/// banner. Returns `true` for a full build (dictionary-en.json present). Since
/// the fold, the forward dictionary and the alias map are ONE crate built from a
/// single parse, so a mixed-mode build is impossible by construction (the old
/// cross-crate mixed-mode assertion is gone).
fn full_mode_checked() -> bool {
    let dict_len = nibli_lexicon::DICTIONARY.len();
    let full = dict_len >= FULL_DICT_MIN;
    if !full {
        eprintln!(
            "alias gate: FALLBACK MODE — curated aliases against the {dict_len}-entry \
             fallback dictionary. Full validation needs `just fetch-dict` + rebuild."
        );
    }
    full
}

/// Deterministically ordered view of the shipped alias map (phf iteration
/// order is arbitrary; sorted output keeps failure lists stable).
fn sorted_aliases() -> Vec<(&'static str, &'static nibli_lexicon::AliasEntry)> {
    let mut all: Vec<_> = nibli_lexicon::ALIASES
        .entries()
        .map(|(name, entry)| (*name, entry))
        .collect();
    all.sort_by_key(|(name, _)| *name);
    all
}

// Mirrors of nibli-lexicon/build.rs `ident_ok` / `looks_like_place_tag` — the
// gate re-asserts the label rules from the SHIPPED map, independent of the
// build-time validation that produced it.
fn ident_ok(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(), Some('a'..='z'))
        && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
}

fn looks_like_place_tag(s: &str) -> bool {
    s.len() == 2 && s.starts_with('x') && matches!(s.as_bytes()[1], b'1'..=b'5')
}

#[test]
fn alias_map_differential() {
    let full_mode = full_mode_checked();
    let aliases = sorted_aliases();
    let mut offenders: Vec<String> = Vec::new();

    // ── leg 1: arity self-consistency (agreement-by-construction since the fold;
    //    a cheap regression check that the alias entry's arity still equals what
    //    the same crate's `get_arity` exposes for the gismu) ──
    for (name, entry) in &aliases {
        match nibli_lexicon::get_arity(entry.gismu) {
            // The build clamps derived arities to 1..=5 (WIT place tags stop at
            // fu/x5), so compare against the same clamp.
            Some(a) if a.clamp(1, 5) == entry.arity as usize => {}
            Some(a) => offenders.push(format!(
                "{name} ({}): alias arity {} != dictionary arity {a}",
                entry.gismu, entry.arity
            )),
            None => offenders.push(format!(
                "{name}: gismu {:?} unknown to nibli-lexicon",
                entry.gismu
            )),
        }
    }

    // ── leg 2: GISMU_TO_ALIAS round-trips + swap validity ──
    for (gismu, alias_name) in nibli_lexicon::GISMU_TO_ALIAS.entries() {
        match nibli_lexicon::alias(alias_name) {
            None => offenders.push(format!(
                "GISMU_TO_ALIAS[{gismu}] = {alias_name:?} which is absent from ALIASES"
            )),
            Some(entry) => {
                if entry.gismu != *gismu {
                    offenders.push(format!(
                        "GISMU_TO_ALIAS[{gismu}] = {alias_name:?} but that alias maps to {}",
                        entry.gismu
                    ));
                }
                if entry.swap.is_some() {
                    offenders.push(format!(
                        "canonical alias {alias_name:?} ({gismu}) carries a swap — the render \
                         direction would silently permute places"
                    ));
                }
            }
        }
    }
    for (name, entry) in &aliases {
        if let Some(n) = entry.swap {
            if !(2..=entry.arity).contains(&n) {
                offenders.push(format!(
                    "{name} ({}): swap x1↔x{n} outside 2..=arity({})",
                    entry.gismu, entry.arity
                ));
            } else {
                // Swap twice = identity on the surface permutation (x1↔xn is an
                // involution — the property render's peel step relies on).
                let arity = entry.arity as usize;
                let mut perm: Vec<usize> = (0..arity).collect();
                perm.swap(0, n as usize - 1);
                perm.swap(0, n as usize - 1);
                if perm != (0..arity).collect::<Vec<usize>>() {
                    offenders.push(format!("{name}: swap x1↔x{n} applied twice != identity"));
                }
            }
            // Every swapped alias must peel to a canonical plain alias.
            if nibli_lexicon::canonical_alias(entry.gismu).is_none() {
                offenders.push(format!(
                    "{name}: converted alias's gismu {} has no canonical plain alias",
                    entry.gismu
                ));
            }
        }
    }

    // ── leg 3: reserved-word exclusion + label integrity from the shipped map ──
    for (name, entry) in &aliases {
        if nibli_lexicon::reserved::is_reserved(name) {
            offenders.push(format!("alias {name:?} collides with a nibli KR keyword"));
        }
        for (i, label) in entry.place_labels.iter().enumerate() {
            if label.is_empty() {
                continue;
            }
            if i >= entry.arity as usize {
                offenders.push(format!(
                    "{name}: label {label:?} at place x{} exceeds arity {}",
                    i + 1,
                    entry.arity
                ));
            }
            if !ident_ok(label) {
                offenders.push(format!("{name}: label {label:?} is not ident-shaped"));
            }
            if nibli_lexicon::reserved::is_reserved(label) {
                offenders.push(format!(
                    "{name}: label {label:?} collides with a nibli KR keyword"
                ));
            }
            if looks_like_place_tag(label) {
                offenders.push(format!(
                    "{name}: label {label:?} looks like a raw place tag"
                ));
            }
            // Self-consistency: the shipped resolver must map the label back to
            // exactly this place (subsumes in-entry duplicates and xN shadowing).
            if nibli_lexicon::label_index(entry, label) != Some(i) {
                offenders.push(format!(
                    "{name}: label_index({label:?}) != Some({i}) — the label does not \
                     resolve to its own place"
                ));
            }
        }
    }

    assert!(
        offenders.is_empty(),
        "{} alias-map offender(s):\n{}",
        offenders.len(),
        offenders.join("\n")
    );

    // ── leg 4: coverage floors ──
    assert!(
        nibli_lexicon::ALIASES.len() >= 95,
        "alias map hollowed out: {} entries",
        nibli_lexicon::ALIASES.len()
    );
    assert!(
        nibli_lexicon::GISMU_TO_ALIAS.len() >= 90,
        "reverse map hollowed out: {} entries",
        nibli_lexicon::GISMU_TO_ALIAS.len()
    );
    assert!(
        nibli_lexicon::curated::CONVERTED_ALIASES.len() >= 3,
        "converted-alias table hollowed out"
    );
    if full_mode {
        assert!(
            nibli_lexicon::GISMU_TO_ALIAS.len() >= 1300,
            "full-mode coverage floor: only {} gismu aliased",
            nibli_lexicon::GISMU_TO_ALIAS.len()
        );
    }
}

#[test]
fn alias_behavioral_battery() {
    let full_mode = full_mode_checked();
    let mut checked = 0usize;
    let mut failures: Vec<String> = Vec::new();

    for (name, entry) in sorted_aliases() {
        let arity = entry.arity as usize;
        let nibli_kr_text = format!("{name}({}).", ARG_NAMES[..arity].join(", "));

        // The twin never uses a raw gismu spelling (the corpus milestone
        // retires gismu input): a PLAIN alias twins with ITSELF under explicit
        // `xN:` labels (named ≡ positional routing on the same predicate); a
        // CONVERTED alias twins with its CANONICAL BASE alias under the
        // permuted labels its surface order implies (se/te/ve/xe = x1↔xk) —
        // the genuine cross-entry conversion oracle.
        let place_of = |pos: usize| -> usize {
            match entry.swap {
                None => pos,
                Some(k) => {
                    let k = k as usize;
                    if pos == 1 {
                        k
                    } else if pos == k {
                        1
                    } else {
                        pos
                    }
                }
            }
        };
        let twin_head: &str = match entry.swap {
            None => name,
            Some(_) => nibli_lexicon::canonical_alias(entry.gismu).unwrap_or_else(|| {
                panic!(
                    "{name}: converted alias's gismu {:?} has no canonical base",
                    entry.gismu
                )
            }),
        };
        let twin_args: Vec<String> = ARG_NAMES[..arity]
            .iter()
            .enumerate()
            .map(|(i, a)| format!("x{}: {a}", place_of(i + 1)))
            .collect();
        let twin_text = format!("{twin_head}({}).", twin_args.join(", "));

        let nibli_kr_buf = match kompile(&nibli_kr_text) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: alias side failed: {nibli_kr_text}\n  {e}"));
                continue;
            }
        };
        let twin_buf = match kompile(&twin_text) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: twin failed: {twin_text}\n  {e}"));
                continue;
            }
        };
        if canonical(&nibli_kr_buf) != canonical(&twin_buf) {
            failures.push(format!(
                "{name}: buffer mismatch\n  alias: {nibli_kr_text}\n  twin:  {twin_text}"
            ));
            continue;
        }
        checked += 1;
    }

    println!("alias behavioral battery: {checked} aliases checked");
    assert!(
        failures.is_empty(),
        "{} behavioral failure(s):\n{}",
        failures.len(),
        failures.join("\n---\n")
    );
    let floor = if full_mode { 1300 } else { 95 };
    assert!(
        checked >= floor,
        "behavioral battery hollowed out: {checked} aliases checked (floor {floor})"
    );
}
