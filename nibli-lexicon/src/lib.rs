//! The nibli compile-time dictionary, built from `dictionary-en.json` (see the
//! Dictionary Data section of CLAUDE.md). Two layers, ONE parse:
//!
//! - the FORWARD dictionary — arity + gloss + place-frame per word ([`get_arity`],
//!   [`get_gloss`], [`get_template`], [`back_translate`]); needed across the engine.
//! - the ALIAS map (folded in from the former nibli-kr-dictionary crate) — English
//!   alias → gismu + optional place swap + place labels ([`alias`],
//!   [`canonical_alias`], [`label_index`], `ALIASES`, `GISMU_TO_ALIAS`); the nibli
//!   KR surface layer, consumed by nibli-kr. Its arity agrees with the forward
//!   dictionary BY CONSTRUCTION (both maps come from the same `build.rs` parse),
//!   so no cross-crate differential is needed.
//!
//! Both layers have a FULL mode (`dictionary-en.json` present — every local build)
//! and a curated FALLBACK mode (no file — what CI uses; loud banner). Curated /
//! fallback data is byte-identical across modes.

/// Dictionary entry with optional arity, English gloss, and place-frame template.
///
/// `template` is a curated English place-frame for the predicate using `{x1}`..`{x5}`
/// placeholders (e.g. `gerku` -> `"{x1} is a dog"`, `klama` -> `"{x1} goes to {x2}
/// from {x3} via {x4} using {x5}"`). An empty `template` means no curated frame
/// exists; the IR renderer falls back to a generic gloss-based frame.
#[derive(Clone, Copy, Debug)]
pub struct DictEntry {
    pub arity: Option<usize>,
    pub gloss: &'static str,
    pub template: &'static str,
}

include!(concat!(env!("OUT_DIR"), "/generated_dictionary.rs"));

/// Canonical place-count extraction from a lensisku definition. Used by `build.rs`
/// (via `#[path]`) to derive arity; exposed here so it is unit-tested by
/// `cargo test -p nibli-lexicon` (CI runs the no-data build, which never calls it,
/// so the pure-function tests are the coverage).
pub mod arity;

/// Look up the arity of a Lojban word (gismu/lujvo only; cmavo returns None).
pub fn get_arity(word: &str) -> Option<usize> {
    DICTIONARY.get(word).and_then(|e| e.arity)
}

/// Look up the primary English gloss of a Lojban word.
pub fn get_gloss(word: &str) -> Option<&'static str> {
    DICTIONARY.get(word).map(|e| e.gloss)
}

/// Look up the curated English place-frame template of a Lojban word.
///
/// Returns `None` when no curated template exists (the entry's `template` is
/// empty) — callers should then build a generic frame from [`get_gloss`] and
/// [`get_arity`]. e.g. `get_template("gerku")` -> `Some("{x1} is a dog")`.
pub fn get_template(word: &str) -> Option<&'static str> {
    DICTIONARY
        .get(word)
        .map(|e| e.template)
        .filter(|t| !t.is_empty())
}

/// Word-by-word robotic back-translation of Lojban text to English glosses.
pub fn back_translate(word: &str) -> String {
    word.split_whitespace()
        .map(|token| {
            // cmevla (a dot-delimited proper name like `.adam.`): the
            // back-translation of a name is the name itself — return the inner
            // form verbatim, never a dictionary gloss. Consulting the dictionary
            // would DROP a name whose inner collides with a suppressed-gloss cmavo
            // (`.cu.`/`.la.` -> "" -> filtered out) and MISTRANSLATE one colliding
            // with a real gloss (`.lo.` -> "the").
            if token.starts_with('.') && token.ends_with('.') && token.len() > 2 {
                return token[1..token.len() - 1].to_string();
            }
            // Regular token: look up in dictionary
            if let Some(entry) = DICTIONARY.get(token) {
                return entry.gloss.to_string();
            }
            // Unknown: pass through
            token.to_string()
        })
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

// ─────────────────────────────────────────────────────────────────────────────
// Alias map (folded from the former nibli-kr-dictionary crate): English alias →
// gismu + optional place permutation + place labels — the nibli KR surface layer.
// ─────────────────────────────────────────────────────────────────────────────

/// Provenance of an entry's `place_labels`.
///
/// `Curated` = hand-written labels from the in-tree tables; `Lensisku` = the
/// export's ordered `place_keywords` (~70/1,338 gismu); `Prose` = the
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
/// exchanged (the se/te/ve/xe family — exactly what `Predicate::Converted` can
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
/// alias map — nibli-kr's resolver then tries the identity-gismu passthrough and
/// otherwise FAILS CLOSED (no arity-2 default; NIBLI_KR §13).
pub fn alias(name: &str) -> Option<&'static AliasEntry> {
    ALIASES.get(name)
}

/// The canonical (plain, unswapped) English alias for a gismu — the render
/// direction. Converted aliases are never canonical.
pub fn canonical_alias(gismu: &str) -> Option<&'static str> {
    GISMU_TO_ALIAS.get(gismu).copied()
}

/// Resolve a named-argument label to its 0-based place index for `entry`
/// (the `u8` place index emit.rs pushes into `Argument::Tagged`).
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
    fn test_gismu_arity() {
        assert_eq!(get_arity("klama"), Some(5));
        assert_eq!(get_arity("gerku"), Some(2));
        assert_eq!(get_arity("prami"), Some(2));
    }

    #[test]
    fn test_cmavo_no_arity() {
        assert_eq!(get_arity("lo"), None);
        assert_eq!(get_arity("cu"), None);
    }

    #[test]
    fn test_gismu_gloss() {
        // Curated glosses win over the alphabetically-first jbovlaste
        // glossword (gerku's glosswords are bitch/canine/dog)
        assert_eq!(get_gloss("gerku"), Some("dog"));
        assert_eq!(get_gloss("prenu"), Some("person"));
        assert_eq!(get_gloss("curmi"), Some("permit"));
        assert_eq!(get_gloss("bilga"), Some("must"));
        assert_eq!(get_gloss("prami"), Some("love"));
        assert!(get_gloss("klama").is_some());
    }

    #[test]
    fn test_cmavo_gloss_overrides() {
        assert_eq!(get_gloss("lo"), Some("the"));
        assert_eq!(get_gloss("na"), Some("not"));
        assert_eq!(get_gloss("pu"), Some("[past]"));
    }

    #[test]
    fn test_corpus_proxy_templates() {
        // Curated place-frames for the GDPR / drug-interaction proxy vocabulary
        // (identical in the data and no-data build modes — single-sourced).
        assert_eq!(get_template("zanru"), Some("{x1} approves of {x2}"));
        assert_eq!(get_template("pilno"), Some("{x1} uses {x2}"));
        assert_eq!(get_template("katna"), Some("{x1} cuts {x2}"));
        assert_eq!(get_template("zenba"), Some("{x1} increases"));
        assert_eq!(get_template("cinla"), Some("{x1} is thin"));
        assert_eq!(get_template("ckape"), Some("{x1} is in danger"));
        assert_eq!(get_template("vimcu"), Some("{x1} is removed"));
        // Already-curated regulatory words stay curated.
        assert_eq!(get_template("curmi"), Some("{x1} permits {x2}"));
        assert_eq!(get_template("javni"), Some("{x1} is a rule about {x2}"));
    }

    #[test]
    fn test_back_translate_basic() {
        let result = back_translate("lo gerku cu klama lo zarci");
        // Should contain glosses for gerku and klama (whatever jbovlaste provides)
        assert!(result.contains("the"), "Expected 'the' in: {}", result);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_back_translate_default_syllogism() {
        // The Transparency Triad UI's default example (book Ch 19)
        assert_eq!(back_translate("ro lo gerku cu danlu"), "all the dog animal");
    }

    #[test]
    fn test_back_translate_cmevla() {
        let result = back_translate(".adam. prami .evas.");
        assert!(result.contains("adam"), "Expected 'adam' in: {}", result);
        assert!(result.contains("evas"), "Expected 'evas' in: {}", result);
    }

    #[test]
    fn test_back_translate_cmevla_collides_with_dictionary_entry() {
        // A dot-delimited name is a proper name: return the inner form verbatim,
        // never the dictionary gloss. Regression for two collision cases:
        //   - inner is a SUPPRESSED-gloss cmavo (`cu` -> "") — the name must NOT
        //     vanish through the empty-gloss filter.
        assert_eq!(back_translate(".cu."), "cu");
        assert_eq!(back_translate(".cu. prami"), "cu love");
        //   - inner has a REAL gloss (`lo` -> "the") — the name must stay the
        //     name, not become the content word.
        assert_eq!(back_translate(".lo."), "lo");
    }

    #[test]
    fn test_back_translate_empty() {
        assert_eq!(back_translate(""), "");
    }

    #[test]
    fn test_structural_suppressed() {
        // "cu" and "ku" should be suppressed (empty gloss)
        let result = back_translate("cu ku");
        assert_eq!(result, "");
    }
}

#[cfg(test)]
mod alias_tests {
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

        let owned = alias("owned").expect("owned");
        assert_eq!((owned.gismu, owned.swap), ("ponse", Some(2)));
        assert_eq!(owned.arity, 3);
    }

    #[test]
    fn keyword_collision_pin() {
        // bilga's lensisku gloss is "must" — a nibli KR keyword. The plain alias is
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
    fn covers_fallback_core() {
        // The FALLBACK_GISMU_ENTRIES word set (+ bilga/curmi) must all be
        // reachable — the vocabulary the shipped gates rely on without
        // dictionary-en.json.
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
                "fallback-core word {gismu:?} has no canonical alias"
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
                "shipped alias {name:?} collides with a nibli KR keyword"
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
