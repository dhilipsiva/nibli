//! Alias-map differential — the `verify-klaro-dict` gate (`just verify-klaro-dict`).
//!
//! `klaro-dictionary` and `smuni-dictionary` are two INDEPENDENTLY BUILT phf
//! maps (klaro-dictionary reads smuni arities as a build-dependency, but its
//! own drift guard runs only inside `generate_full` — a FALLBACK build ships
//! with no cross-check at all). This gate joins the two SHIPPED artifacts at
//! runtime so they cannot drift: the exact gap that hid the dilcu=3/jmive=1
//! fallback flap (smuni's fallback table vs its own full lensisku derivation,
//! found 2026-07-12 by klaro-dictionary's build-time guard, fixed alongside
//! this gate).
//!
//! Two tests, both dual-mode and never skipping (the verify-dict contract):
//! 1. `alias_map_differential` — structural: per-alias arity equality against
//!    `smuni_dictionary::get_arity`, `GISMU_TO_ALIAS` round-trips, swap
//!    validity (`2..=arity`, involution), reserved-word exclusion and label
//!    integrity re-asserted from the shipped map, coverage floors.
//! 2. `alias_behavioral_battery` — for EVERY shipped alias, `alias(A, B, …)`
//!    compiled through klaro+smuni must equal the direct-gismu Lojban sentence
//!    through gerna+smuni at the canonicalized-LogicBuffer level (the seam
//!    gate's equality contract, applied to the whole alias map).
//!
//! Mode is read from the artifacts under test (`DICTIONARY.len()` /
//! `GISMU_TO_ALIAS.len()` — compile-time phf properties; checking the json
//! file's presence could lie about a stale build), and the two crates must be
//! in the SAME mode: a mixed-mode build is a stale artifact (mv preserves
//! mtimes, so a moved data file can leave one crate un-rebuilt) and fails loud.

use nibli_verify::klaro_battery::{canonical, kompile};
use nibli_verify::seam;

/// Full-build detector, shared convention with the predilex gate: the fallback
/// artifacts have ~99/~140 entries, full builds ~1,341/~10.9k.
const FULL_DICT_MIN: usize = 1000;

/// Argument constants for the behavioral battery: (Klaro name, Lojban cmevla).
/// Consonant-final so every truncation is a valid cmevla.
const ARG_NAMES: [(&str, &str); 5] = [
    ("Adam", ".adam."),
    ("Bob", ".bob."),
    ("Kim", ".kim."),
    ("Tom", ".tom."),
    ("Sam", ".sam."),
];

/// Detect the build mode from the shipped artifacts, assert the two crates
/// agree, and print the fallback banner. Returns `true` for a full build.
fn full_mode_checked() -> bool {
    let smuni_len = smuni_dictionary::DICTIONARY.len();
    let klaro_len = klaro_dictionary::GISMU_TO_ALIAS.len();
    let smuni_full = smuni_len >= FULL_DICT_MIN;
    let klaro_full = klaro_len >= FULL_DICT_MIN;
    assert_eq!(
        klaro_full, smuni_full,
        "MIXED-MODE BUILD: klaro-dictionary has {klaro_len} gismu (full={klaro_full}) but \
         smuni-dictionary has {smuni_len} entries (full={smuni_full}) — one artifact is stale \
         (moving dictionary-en.json preserves mtimes, so a build script can skip its rerun). \
         Fix: `cargo clean -p smuni-dictionary -p klaro-dictionary` and rebuild."
    );
    if !smuni_full {
        eprintln!(
            "alias gate: FALLBACK MODE — {klaro_len} curated aliases against the {smuni_len}-entry \
             fallback dictionary. Full validation needs `just fetch-dict` + rebuild."
        );
    }
    smuni_full
}

/// Deterministically ordered view of the shipped alias map (phf iteration
/// order is arbitrary; sorted output keeps failure lists stable).
fn sorted_aliases() -> Vec<(&'static str, &'static klaro_dictionary::AliasEntry)> {
    let mut all: Vec<_> = klaro_dictionary::ALIASES
        .entries()
        .map(|(name, entry)| (*name, entry))
        .collect();
    all.sort_by_key(|(name, _)| *name);
    all
}

// Mirrors of klaro-dictionary/build.rs `ident_ok` / `looks_like_place_tag` —
// the gate re-asserts the label rules from the SHIPPED map, independent of the
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

    // ── leg 1: arity differential (the leg that catches dilcu/jmive-class flaps) ──
    for (name, entry) in &aliases {
        match smuni_dictionary::get_arity(entry.gismu) {
            // The build clamps derived arities to 1..=5 (WIT place tags stop at
            // fu/x5), so compare against the same clamp.
            Some(a) if a.clamp(1, 5) == entry.arity as usize => {}
            Some(a) => offenders.push(format!(
                "{name} ({}): klaro arity {} != smuni arity {a}",
                entry.gismu, entry.arity
            )),
            None => offenders.push(format!(
                "{name}: gismu {:?} unknown to smuni-dictionary",
                entry.gismu
            )),
        }
    }

    // ── leg 2: GISMU_TO_ALIAS round-trips + swap validity ──
    for (gismu, alias_name) in klaro_dictionary::GISMU_TO_ALIAS.entries() {
        match klaro_dictionary::alias(alias_name) {
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
            if klaro_dictionary::canonical_alias(entry.gismu).is_none() {
                offenders.push(format!(
                    "{name}: converted alias's gismu {} has no canonical plain alias",
                    entry.gismu
                ));
            }
        }
    }

    // ── leg 3: reserved-word exclusion + label integrity from the shipped map ──
    for (name, entry) in &aliases {
        if klaro_dictionary::reserved::is_reserved(name) {
            offenders.push(format!("alias {name:?} collides with a Klaro keyword"));
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
            if klaro_dictionary::reserved::is_reserved(label) {
                offenders.push(format!(
                    "{name}: label {label:?} collides with a Klaro keyword"
                ));
            }
            if looks_like_place_tag(label) {
                offenders.push(format!(
                    "{name}: label {label:?} looks like a raw place tag"
                ));
            }
            // Self-consistency: the shipped resolver must map the label back to
            // exactly this place (subsumes in-entry duplicates and xN shadowing).
            if klaro_dictionary::label_index(entry, label) != Some(i) {
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
        klaro_dictionary::ALIASES.len() >= 95,
        "alias map hollowed out: {} entries",
        klaro_dictionary::ALIASES.len()
    );
    assert!(
        klaro_dictionary::GISMU_TO_ALIAS.len() >= 90,
        "reverse map hollowed out: {} entries",
        klaro_dictionary::GISMU_TO_ALIAS.len()
    );
    assert!(
        klaro_dictionary::curated::CONVERTED_ALIASES.len() >= 3,
        "converted-alias table hollowed out"
    );
    if full_mode {
        assert!(
            klaro_dictionary::GISMU_TO_ALIAS.len() >= 1300,
            "full-mode coverage floor: only {} gismu aliased",
            klaro_dictionary::GISMU_TO_ALIAS.len()
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
        let klaro_args: Vec<&str> = ARG_NAMES[..arity].iter().map(|(k, _)| *k).collect();
        let klaro_text = format!("{name}({}).", klaro_args.join(", "));

        // The Lojban twin in the SAME surface order: a swapped alias's surface
        // order is exactly what the se/te/ve/xe conversion spells.
        let conv = match entry.swap {
            None => "",
            Some(2) => "se ",
            Some(3) => "te ",
            Some(4) => "ve ",
            Some(5) => "xe ",
            Some(n) => panic!("{name}: swap {n} outside the conversion family"),
        };
        let mut lojban = format!("la {} cu {conv}{}", ARG_NAMES[0].1, entry.gismu);
        for (_, cmevla) in &ARG_NAMES[1..arity] {
            lojban.push_str(" la ");
            lojban.push_str(cmevla);
        }

        let klaro_buf = match kompile(&klaro_text) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: klaro side failed: {klaro_text}\n  {e}"));
                continue;
            }
        };
        let lojban_buf = match seam::compile(&lojban) {
            Ok(buf) => buf,
            Err(e) => {
                failures.push(format!("{name}: lojban twin failed: {lojban}\n  {e}"));
                continue;
            }
        };
        if canonical(&klaro_buf) != canonical(&lojban_buf) {
            failures.push(format!(
                "{name}: buffer mismatch\n  klaro:  {klaro_text}\n  lojban: {lojban}"
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
