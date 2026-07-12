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
//! Current mode: FALLBACK ONLY — every entry comes from the curated Rust const
//! tables in [`curated`] (no data files; see that module for the naming policy).
//! Full lensisku generation (all ~1,338 gismu) is the next KLARO_TODO bullet and
//! will layer generation UNDER these tables — the curated entries become pins
//! that win in both build modes.

/// Provenance of an entry's `place_labels`.
///
/// `Lensisku` and `Prose` only appear once full generation lands (labels taken
/// from the export's `place_keywords`, or heuristically from definition prose);
/// in fallback mode every entry is `Curated` (has hand-written labels) or
/// `Positional` (labels all empty — callers use raw `x1..x5`).
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

        assert!(
            alias("consents").is_none(),
            "domain overlays are not core aliases"
        );
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
        ] {
            assert!(
                canonical_alias(gismu).is_some(),
                "smuni fallback-core word {gismu:?} has no canonical alias"
            );
        }
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
