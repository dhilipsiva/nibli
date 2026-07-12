//! Compile-time alias map for the Klaro front-end: English alias → gismu +
//! optional place permutation + place labels.
//!
//! This is NEW TRUSTED BASE for the Klaro surface syntax (SURFACE_SYNTAX.md §13)
//! and deliberately its own crate, NOT an extension of `smuni-dictionary`: klaro
//! needs the reverse (English-keyed) direction plus per-place labels, and none of
//! that belongs in the phf map that ships inside the smuni→lasna/nibli-wasm web
//! bundle. The two crates' agreement (alias arity == smuni arity, swap validity)
//! is enforced by the alias differential gate in nibli-verify, not by shared code.
//!
//! Two build modes, mirroring smuni-dictionary's contract:
//!
//! - **FULL MODE** (repo-root `dictionary-en.json` present — every local build):
//!   all ~1,338 gismu get an alias — curated table first, then `ALIAS_PINS`,
//!   then the first lensisku gloss keyword normalized (base-form as-is; user
//!   decision 2026-07-12 — no mechanical inflection, the export has no
//!   part-of-speech data). Arity comes from `smuni-dictionary` as a BUILD
//!   dependency, so klaro/smuni arity agreement holds by construction. Unpinned
//!   collisions/keyword-hits/dictionary-shadows FAIL THE BUILD listing every
//!   offender; coverage floor ≥ 1,300.
//! - **FALLBACK MODE** (no data file — what CI uses; loud banner): exactly the
//!   curated Rust const tables in [`curated`]. Curated entries are byte-identical
//!   across modes (they are the pin tier — spellings can never flap).
//!
//! All source data is in-tree Rust; the only generated artifact is the phf map
//! in `OUT_DIR`.

/// Provenance of an entry's `place_labels`.
///
/// `Curated` = hand-written labels from the in-tree tables; `Lensisku` = the
/// export's ordered `place_keywords` (70/1,338 gismu); `Prose` = the
/// [`label::prose_labels`] heuristic over the definition's `$x_N$` markers;
/// `Positional` = no labels (callers use raw `x1..x5`). Fallback mode only
/// produces `Curated`/`Positional`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LabelTier {
    Curated,
    Lensisku,
    Prose,
    Positional,
}

/// One alias-map entry.
///
/// `swap: Some(n)` means the SURFACE argument order is the gismu's with x1 ↔ xn
/// exchanged (the se/te/ve/xe family — exactly what `Selbri::Converted` can
/// express); `None` is identity. `place_labels` are in SURFACE order; `""` means
/// no label for that place (positional / raw `x1..x5` only).
#[derive(Clone, Copy, Debug)]
pub struct AliasEntry {
    pub gismu: &'static str,
    pub swap: Option<u8>,
    pub arity: u8,
    pub place_labels: [&'static str; 5],
    pub label_tier: LabelTier,
}

include!(concat!(env!("OUT_DIR"), "/generated_aliases.rs"));

pub mod curated;
pub mod label;
pub mod reserved;

/// Look up an English predicate alias. `None` means the name is unknown to the
/// alias map — klaro's resolver then tries the identity-gismu passthrough and
/// otherwise FAILS CLOSED (no arity-2 default; SURFACE_SYNTAX §13).
pub fn alias(name: &str) -> Option<&'static AliasEntry> {
    ALIASES.get(name)
}

/// The canonical (plain, unswapped) English alias for a gismu — the render
/// direction. Converted aliases are never canonical.
pub fn canonical_alias(gismu: &str) -> Option<&'static str> {
    GISMU_TO_ALIAS.get(gismu).copied()
}

/// Resolve a named-argument label to its 0-based place index for `entry`
/// (matching `nibli_types::ast::PlaceTag::to_index()`).
///
/// Accepts the entry's dictionary labels and the raw `x1`..`x5` escape hatch;
/// both are bounded by the entry's arity (a tag beyond arity is `None` — the
/// caller reports the fail-closed error).
pub fn label_index(entry: &AliasEntry, label: &str) -> Option<usize> {
    if let Some(rest) = label.strip_prefix('x')
        && rest.len() == 1
        && let Some(d) = rest.chars().next().and_then(|c| c.to_digit(10))
        && (1..=5).contains(&d)
    {
        return if d as u8 <= entry.arity {
            Some((d - 1) as usize)
        } else {
            None
        };
    }
    entry
        .place_labels
        .iter()
        .position(|l| !l.is_empty() && *l == label)
        .filter(|&i| i < entry.arity as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_alias_lookups() {
        let goes = alias("goes").expect("goes");
        assert_eq!(goes.gismu, "klama");
        assert_eq!(goes.arity, 5);
        assert_eq!(goes.swap, None);
        assert_eq!(goes.label_tier, LabelTier::Curated);

        let dog = alias("dog").expect("dog");
        assert_eq!(dog.gismu, "gerku");
        assert_eq!(dog.arity, 2);

        // Domain overlays are not core aliases: zanru's canonical name is the
        // honest generic, never the GDPR corpus reading.
        assert_eq!(canonical_alias("zanru"), Some("approves"));
        assert!(alias("zzz_unknown").is_none());
    }

    #[test]
    fn converted_alias_lookups() {
        let obligated = alias("obligated").expect("obligated");
        assert_eq!((obligated.gismu, obligated.swap), ("bilga", Some(2)));
        assert_eq!(obligated.arity, 3);
        assert_eq!(obligated.label_tier, LabelTier::Positional);

        let metabolized_by = alias("metabolized_by").expect("metabolized_by");
        assert_eq!(
            (metabolized_by.gismu, metabolized_by.swap),
            ("katna", Some(2))
        );

        let permitted = alias("permitted").expect("permitted");
        assert_eq!((permitted.gismu, permitted.swap), ("curmi", Some(2)));
    }

    #[test]
    fn keyword_collision_pin() {
        // bilga's lensisku gloss is "must" — a Klaro keyword. The plain alias is
        // the pinned honest form; "must" must never resolve.
        assert!(alias("must").is_none());
        let obliged = alias("obliged").expect("obliged");
        assert_eq!((obliged.gismu, obliged.swap), ("bilga", None));
    }

    #[test]
    fn canonical_round_trips() {
        // Every gismu→alias entry round-trips to a plain (unswapped) alias entry
        // for that same gismu.
        assert!(
            GISMU_TO_ALIAS.len() >= 62,
            "canonical map shrank: {}",
            GISMU_TO_ALIAS.len()
        );
        for (gismu, alias_name) in GISMU_TO_ALIAS.entries() {
            let entry = alias(alias_name)
                .unwrap_or_else(|| panic!("canonical alias {alias_name:?} missing from ALIASES"));
            assert_eq!(entry.gismu, *gismu, "round-trip broke for {alias_name:?}");
            assert_eq!(
                entry.swap, None,
                "canonical alias {alias_name:?} must be unswapped"
            );
        }
        assert_eq!(canonical_alias("klama"), Some("goes"));
        assert_eq!(canonical_alias("bilga"), Some("obliged"));
        assert_eq!(canonical_alias("curmi"), Some("permits"));
        assert_eq!(canonical_alias("nonexistent"), None);
    }

    #[test]
    fn covers_smuni_fallback_core() {
        // The smuni-dictionary FALLBACK_GISMU_ENTRIES word set (+ bilga/curmi) must
        // all be reachable — the vocabulary the shipped gates rely on without
        // dictionary-en.json. The alias differential gate (nibli-verify) will
        // additionally pin arity equality against smuni-dictionary itself.
        assert!(ALIASES.len() >= 65, "alias map shrank: {}", ALIASES.len());
        for gismu in [
            "klama", "ctuca", "ciska", "mrilu", "bevri", "vecnu", "dunda", "prami", "gerku",
            "mlatu", "cmene", "cusku", "djuno", "jimpe", "gasnu", "penmi", "tavla", "catra",
            "citka", "pinxe", "cadzu", "bajra", "viska", "tirna", "nelci", "djica", "nitcu",
            "kakne", "ckana", "zdani", "zarci", "bridi", "jbena", "morsi", "sutra", "melbi",
            "barda", "cmalu", "xamgu", "xlali", "blanu", "xunre", "pelxu", "crino", "prenu",
            "pilji", "sumji", "dilcu", "danlu", "jmive", "zanru", "pilno", "katna", "zenba",
            "cinla", "ckape", "vimcu", "javni", "datni", "turni", "bilga", "curmi",
            // GISMU_PLACE_TEMPLATES set + remaining corpus/spec vocabulary
            // (curated in the full-generation milestone).
            "zukte", "zbasu", "tadni", "kurji", "ponse", "fanta", "kajde", "flalu", "nibli",
            "krinu", "cipni", "finpe", "nanmu", "ninmu", "verba", "remna", "xukmi", "dinju",
            "marce", "cidja", "litki", "ciste", "logji", "masno", "kanro", "birti", "xanri",
            "zmadu", "mleca", "dunli", "facki", "drani", "cfila", "notci",
        ] {
            assert!(
                canonical_alias(gismu).is_some(),
                "smuni fallback-core word {gismu:?} has no canonical alias"
            );
        }
    }

    /// True when this build ran FULL MODE (dictionary-en.json present) — the
    /// generated long tail dwarfs the curated core.
    fn full_mode() -> bool {
        ALIASES.len() > 200
    }

    #[test]
    fn full_mode_generation() {
        if !full_mode() {
            eprintln!("SKIP full_mode_generation: fallback build (no dictionary-en.json)");
            return;
        }
        // Coverage floor (also asserted at build time).
        assert!(
            GISMU_TO_ALIAS.len() >= 1300,
            "full-mode canonical map too small: {}",
            GISMU_TO_ALIAS.len()
        );
        // Long-tail pins hold: collision group, SI-prefix numeric gloss,
        // reserved-word gloss, gloss-less word, dictionary-word shadow.
        assert_eq!(canonical_alias("janta"), Some("bill"));
        assert_eq!(canonical_alias("kilto"), Some("kilo"));
        assert_eq!(canonical_alias("balvi"), Some("later"));
        assert!(
            alias("future").is_none(),
            "keyword glosses must be pinned away"
        );
        assert_eq!(canonical_alias("jukni"), Some("spider"));
        assert_eq!(canonical_alias("kruvi"), Some("bend"));
        // Base-form policy for the uncurated long tail: aliases come from the
        // gloss verbatim (e.g. sisku -> "seek", not "seeks").
        let seek = alias("seek").expect("long-tail base-form alias");
        assert_eq!(seek.gismu, "sisku");
        // Every generated entry still round-trips and respects arity bounds
        // (covered structurally by canonical_round_trips/labels_within_arity_only,
        // which iterate the FULL map in this mode).
        let tiers: Vec<LabelTier> = ALIASES.entries().map(|(_, e)| e.label_tier).collect();
        assert!(
            tiers.contains(&LabelTier::Lensisku),
            "no Lensisku-tier labels — place_keywords went unused"
        );
        assert!(
            tiers.contains(&LabelTier::Prose),
            "no Prose-tier labels — the heuristic went unused"
        );
    }

    #[test]
    fn no_shipped_alias_is_reserved() {
        // Re-asserted from the SHIPPED map (build.rs already fails the build on
        // violation — this guards the generated artifact itself).
        for (name, _) in ALIASES.entries() {
            assert!(
                !reserved::is_reserved(name),
                "shipped alias {name:?} collides with a Klaro keyword"
            );
        }
    }

    #[test]
    fn label_index_dictionary_and_raw() {
        let goes = alias("goes").unwrap();
        assert_eq!(label_index(goes, "goer"), Some(0));
        assert_eq!(label_index(goes, "destination"), Some(1));
        assert_eq!(label_index(goes, "means"), Some(4));
        assert_eq!(label_index(goes, "x1"), Some(0));
        assert_eq!(label_index(goes, "x5"), Some(4));
        assert_eq!(label_index(goes, "nonsense"), None);

        let dog = alias("dog").unwrap();
        assert_eq!(label_index(dog, "breed"), Some(1));
        assert_eq!(label_index(dog, "x2"), Some(1));
        // Fail closed beyond arity: gerku is 2-place.
        assert_eq!(label_index(dog, "x3"), None);
        // Empty string never matches an unlabeled place.
        assert_eq!(label_index(dog, ""), None);
    }

    #[test]
    fn labels_within_arity_only() {
        for (name, entry) in ALIASES.entries() {
            for (i, label) in entry.place_labels.iter().enumerate() {
                if !label.is_empty() {
                    assert!(
                        i < entry.arity as usize,
                        "{name:?}: label {label:?} beyond arity {}",
                        entry.arity
                    );
                }
            }
        }
    }
}
