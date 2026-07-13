//! Alias-map differential — the `verify-nibli-kr-dict` gate (`just verify-nibli-kr-dict`).
//!
//! `nibli-kr-dictionary` and `nibli-lexicon` are two INDEPENDENTLY BUILT phf
//! maps (nibli-kr-dictionary reads smuni arities as a build-dependency, but its
//! own drift guard runs only inside `generate_full` — a FALLBACK build ships
//! with no cross-check at all). This gate joins the two SHIPPED artifacts at
//! runtime so they cannot drift: the exact gap that hid the dilcu=3/jmive=1
//! fallback flap (smuni's fallback table vs its own full lensisku derivation,
//! found 2026-07-12 by nibli-kr-dictionary's build-time guard, fixed alongside
//! this gate).
//!
//! Two tests, both dual-mode and never skipping (the verify-dict contract):
//! 1. `alias_map_differential` — structural: per-alias arity equality against
//!    `nibli_lexicon::get_arity`, `GISMU_TO_ALIAS` round-trips, swap
//!    validity (`2..=arity`, involution), reserved-word exclusion and label
//!    integrity re-asserted from the shipped map, coverage floors.
//! 2. `alias_behavioral_battery` — for EVERY shipped alias, `alias(A, B, …)`
//!    compiled through nibli-kr+smuni must equal the RAW-GISMU spelling with
//!    explicit permuted `xN` labels (the identity-passthrough twin — the KR
//!    seam gate's converted≡label-permuted family applied to the whole map)
//!    at the canonicalized-LogicBuffer level. This replaced the gerna-compiled
//!    Lojban twin at THE DROP: raw `xN` labels route places directly, so the
//!    oracle side never touches the alias under test.
//!
//! Mode is read from the artifacts under test (`DICTIONARY.len()` /
//! `GISMU_TO_ALIAS.len()` — compile-time phf properties; checking the json
//! file's presence could lie about a stale build), and the two crates must be
//! in the SAME mode: a mixed-mode build is a stale artifact (mv preserves
//! mtimes, so a moved data file can leave one crate un-rebuilt) and fails loud.

use nibli_verify::nibli_kr_battery::{canonical, kompile};

/// Full-build detector, shared convention with the predilex gate: the fallback
/// artifacts have ~99/~140 entries, full builds ~1,341/~10.9k.
const FULL_DICT_MIN: usize = 1000;

/// Argument constants for the behavioral battery.
const ARG_NAMES: [&str; 5] = ["Adam", "Bob", "Kim", "Tom", "Sam"];

/// Detect the build mode from the shipped artifacts, assert the two crates
/// agree, and print the fallback banner. Returns `true` for a full build.
fn full_mode_checked() -> bool {
    let smuni_len = nibli_lexicon::DICTIONARY.len();
    let nibli_kr_len = nibli_kr_dictionary::GISMU_TO_ALIAS.len();
    let smuni_full = smuni_len >= FULL_DICT_MIN;
    let nibli_kr_full = nibli_kr_len >= FULL_DICT_MIN;
    assert_eq!(
        nibli_kr_full, smuni_full,
        "MIXED-MODE BUILD: nibli-kr-dictionary has {nibli_kr_len} gismu (full={nibli_kr_full}) but \
         nibli-lexicon has {smuni_len} entries (full={smuni_full}) — one artifact is stale \
         (moving dictionary-en.json preserves mtimes, so a build script can skip its rerun). \
         Fix: `cargo clean -p nibli-lexicon -p nibli-kr-dictionary` and rebuild."
    );
    if !smuni_full {
        eprintln!(
            "alias gate: FALLBACK MODE — {nibli_kr_len} curated aliases against the {smuni_len}-entry \
             fallback dictionary. Full validation needs `just fetch-dict` + rebuild."
        );
    }
    smuni_full
}

/// Deterministically ordered view of the shipped alias map (phf iteration
/// order is arbitrary; sorted output keeps failure lists stable).
fn sorted_aliases() -> Vec<(&'static str, &'static nibli_kr_dictionary::AliasEntry)> {
    let mut all: Vec<_> = nibli_kr_dictionary::ALIASES
        .entries()
        .map(|(name, entry)| (*name, entry))
        .collect();
    all.sort_by_key(|(name, _)| *name);
    all
}

// Mirrors of nibli-kr-dictionary/build.rs `ident_ok` / `looks_like_place_tag` —
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
        match nibli_lexicon::get_arity(entry.gismu) {
            // The build clamps derived arities to 1..=5 (WIT place tags stop at
            // fu/x5), so compare against the same clamp.
            Some(a) if a.clamp(1, 5) == entry.arity as usize => {}
            Some(a) => offenders.push(format!(
                "{name} ({}): nibli-kr arity {} != smuni arity {a}",
                entry.gismu, entry.arity
            )),
            None => offenders.push(format!(
                "{name}: gismu {:?} unknown to nibli-lexicon",
                entry.gismu
            )),
        }
    }

    // ── leg 2: GISMU_TO_ALIAS round-trips + swap validity ──
    for (gismu, alias_name) in nibli_kr_dictionary::GISMU_TO_ALIAS.entries() {
        match nibli_kr_dictionary::alias(alias_name) {
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
            if nibli_kr_dictionary::canonical_alias(entry.gismu).is_none() {
                offenders.push(format!(
                    "{name}: converted alias's gismu {} has no canonical plain alias",
                    entry.gismu
                ));
            }
        }
    }

    // ── leg 3: reserved-word exclusion + label integrity from the shipped map ──
    for (name, entry) in &aliases {
        if nibli_kr_dictionary::reserved::is_reserved(name) {
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
            if nibli_kr_dictionary::reserved::is_reserved(label) {
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
            if nibli_kr_dictionary::label_index(entry, label) != Some(i) {
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
        nibli_kr_dictionary::ALIASES.len() >= 95,
        "alias map hollowed out: {} entries",
        nibli_kr_dictionary::ALIASES.len()
    );
    assert!(
        nibli_kr_dictionary::GISMU_TO_ALIAS.len() >= 90,
        "reverse map hollowed out: {} entries",
        nibli_kr_dictionary::GISMU_TO_ALIAS.len()
    );
    assert!(
        nibli_kr_dictionary::curated::CONVERTED_ALIASES.len() >= 3,
        "converted-alias table hollowed out"
    );
    if full_mode {
        assert!(
            nibli_kr_dictionary::GISMU_TO_ALIAS.len() >= 1300,
            "full-mode coverage floor: only {} gismu aliased",
            nibli_kr_dictionary::GISMU_TO_ALIAS.len()
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

        // The identity-passthrough twin in the SAME surface order: raw `xN`
        // labels route each argument to the exact underlying place a swapped
        // alias's surface order implies (se/te/ve/xe = x1↔xk, others fixed),
        // so the twin exercises the routing WITHOUT the alias under test.
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
        let twin_args: Vec<String> = ARG_NAMES[..arity]
            .iter()
            .enumerate()
            .map(|(i, a)| format!("x{}: {a}", place_of(i + 1)))
            .collect();
        let twin_text = format!("{}({}).", entry.gismu, twin_args.join(", "));

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
                failures.push(format!("{name}: identity twin failed: {twin_text}\n  {e}"));
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
