use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

// Canonical arity extraction, shared with the crate's tests (compiled here as a
// build-script module; `#[cfg(test)]` is false for a build script, so its test
// submodule is excluded).
#[path = "src/arity.rs"]
mod arity;

// Curated alias tables, prose-label heuristic, and reserved-word list (folded
// from nibli-lexicon; compiled here as build-script modules — `#[cfg(test)]`
// is false for a build script, so their test submodules are excluded).
#[path = "src/curated.rs"]
mod curated;
#[path = "src/label.rs"]
mod label;
#[path = "src/reserved.rs"]
mod reserved;

use curated::{ALIAS_PINS, CONVERTED_ALIASES, CURATED_ALIASES};
use reserved::is_reserved;

/// A single entry from the lensisku `dictionary-en.json` bulk export (the file is a JSON
/// array of these, one per word). Only the fields the dictionary build consumes are
/// declared; serde ignores the rest (rafsi, selmaho, notes, score, place_keywords, …).
/// Mirrors `lojban/lensisku` `src/export/models.rs::DictionaryEntry`.
#[derive(serde::Deserialize)]
struct LensiskuEntry {
    word: String,
    word_type: String,
    definition: String,
    /// jbovlaste glosswords; the back-translation gloss is the first one. Omitted from the
    /// JSON when empty, so default to an empty list.
    #[serde(default)]
    gloss_keywords: Vec<GlossKeyword>,
    /// Ordered per-place label list (x1 first; present on ~70/1,338 gismu) — the
    /// alias map's label tier 1. Omitted when empty.
    #[serde(default)]
    place_keywords: Vec<GlossKeyword>,
}

/// One gloss keyword; only `word` (the single-word English gloss) is consumed.
#[derive(serde::Deserialize)]
struct GlossKeyword {
    word: String,
}

fn main() {
    println!("cargo:rerun-if-changed=../dictionary-en.json");
    println!("cargo:rerun-if-changed=src/curated.rs");
    println!("cargo:rerun-if-changed=src/label.rs");
    println!("cargo:rerun-if-changed=src/reserved.rs");

    let json_path = "../dictionary-en.json";
    let content = fs::read_to_string(json_path).ok();

    // Collect entries first (phf_codegen borrows value strings for the map's lifetime)
    let mut entries: Vec<(String, String)> = Vec::new();
    // word -> arity for the folded alias generation (Some(n) gismu/lujvo, None
    // cmavo); replaces the old cross-crate `nibli_lexicon::get_arity` build-dep.
    let mut arity_map: HashMap<String, Option<usize>> = HashMap::new();
    let mut gismu_count: usize = 0;
    let mut lujvo_count: usize = 0;
    let mut cmavo_count: usize = 0;

    let lensisku: Option<Vec<LensiskuEntry>> = content.as_deref().map(|c| {
        serde_json::from_str(c).expect("dictionary-en.json is not a valid lensisku export array")
    });

    if let Some(dict) = &lensisku {
        for entry in dict {
            let word = entry.word.as_str();
            let typ = entry.word_type.as_str();

            if word.is_empty() {
                continue;
            }

            match typ {
                "gismu" | "lujvo" => {
                    let arity = if let Some(&(_, a)) =
                        CORE_GISMU_ARITIES.iter().find(|(w, _)| *w == word)
                    {
                        a
                    } else {
                        arity::definition_arity(&entry.definition)
                    };

                    let gloss = if let Some(&(_, g)) =
                        GISMU_GLOSS_OVERRIDES.iter().find(|(w, _)| *w == word)
                    {
                        g
                    } else if let Some(&(_, _, g)) =
                        FALLBACK_GISMU_ENTRIES.iter().find(|(w, _, _)| *w == word)
                    {
                        g
                    } else {
                        entry
                            .gloss_keywords
                            .first()
                            .map(|k| k.word.as_str())
                            .unwrap_or(word)
                    };
                    let escaped_gloss = escape_str(gloss);
                    let template = lookup_template(word);
                    let value = format!(
                        "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                        arity,
                        escaped_gloss,
                        escape_str(template)
                    );
                    entries.push((word.to_string(), value));
                    arity_map.insert(word.to_string(), Some(arity));

                    match typ {
                        "gismu" => gismu_count += 1,
                        "lujvo" => lujvo_count += 1,
                        _ => {}
                    }
                }
                "cmavo" | "cmavo-compound" => {
                    let gloss = if let Some(&(_, g)) =
                        CMAVO_GLOSS_OVERRIDES.iter().find(|(w, _)| *w == word)
                    {
                        g
                    } else {
                        entry
                            .gloss_keywords
                            .first()
                            .map(|k| k.word.as_str())
                            .unwrap_or(word)
                    };
                    let escaped_gloss = escape_str(gloss);
                    let value = format!(
                        "DictEntry {{ arity: None, gloss: \"{}\", template: \"\" }}",
                        escaped_gloss
                    );
                    entries.push((word.to_string(), value));
                    arity_map.insert(word.to_string(), None);
                    cmavo_count += 1;
                }
                _ => continue,
            }
        }
    } else {
        println!("cargo:warning=dictionary-en.json not found, using fallback dictionary entries");
        for (word, arity, gloss) in FALLBACK_GISMU_ENTRIES {
            let value = format!(
                "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                arity,
                escape_str(gloss),
                escape_str(lookup_template(word))
            );
            entries.push(((*word).to_string(), value));
            arity_map.insert((*word).to_string(), Some(*arity));
            gismu_count += 1;
        }
        // Tier-1 curated gloss overrides (e.g. bilga->must, curmi->permit) win over
        // the lensisku gloss keyword in the data branch above; reproduce them here so the
        // no-data build exposes the same glosses (the 3-tier chain documented in the
        // dictionary). Skip any word the fallback list already provides to avoid a
        // phf duplicate key; arity is CORE_GISMU_ARITIES here, else the 2 default.
        for (word, gloss) in GISMU_GLOSS_OVERRIDES {
            if FALLBACK_GISMU_ENTRIES.iter().any(|(w, _, _)| w == word) {
                continue;
            }
            let arity = CORE_GISMU_ARITIES
                .iter()
                .find(|(w, _)| w == word)
                .map(|(_, a)| *a)
                .unwrap_or(2);
            let value = format!(
                "DictEntry {{ arity: Some({}), gloss: \"{}\", template: \"{}\" }}",
                arity,
                escape_str(gloss),
                escape_str(lookup_template(word))
            );
            entries.push(((*word).to_string(), value));
            arity_map.insert((*word).to_string(), Some(arity));
            gismu_count += 1;
        }
        for (word, gloss) in CMAVO_GLOSS_OVERRIDES {
            let value = format!(
                "DictEntry {{ arity: None, gloss: \"{}\", template: \"\" }}",
                escape_str(gloss)
            );
            entries.push(((*word).to_string(), value));
            arity_map.insert((*word).to_string(), None);
            cmavo_count += 1;
        }
    }

    let mut map = phf_codegen::Map::new();
    for (key, value) in &entries {
        map.entry(key.clone(), value.as_str());
    }

    let total = gismu_count + lujvo_count + cmavo_count;
    println!(
        "cargo:warning=dictionary: {} entries ({} gismu, {} lujvo, {} cmavo)",
        total, gismu_count, lujvo_count, cmavo_count
    );

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("generated_dictionary.rs");
    let mut file = BufWriter::new(File::create(&dest_path).unwrap());

    writeln!(
        &mut file,
        "pub static DICTIONARY: phf::Map<&'static str, DictEntry> = \n{};",
        map.build()
    )
    .unwrap();

    // ── alias map (folded from nibli-lexicon) ──
    // Reuses the single parse above; alias arity comes from `arity_map`, not a
    // cross-crate `nibli_lexicon::get_arity` call.
    validate();
    let mut alias_entries: Vec<(String, String)> = Vec::new();
    let mut gismu_entries: Vec<(String, String)> = Vec::new();

    for (alias, gismu, arity, labels) in CURATED_ALIASES {
        let tier = if labels.iter().any(|l| !l.is_empty()) {
            "Curated"
        } else {
            "Positional"
        };
        let labels_src = labels
            .iter()
            .map(|l| format!("\"{l}\""))
            .collect::<Vec<_>>()
            .join(", ");
        alias_entries.push((
            (*alias).to_string(),
            format!(
                "AliasEntry {{ gismu: \"{gismu}\", swap: None, arity: {arity}, \
                 place_labels: [{labels_src}], label_tier: LabelTier::{tier} }}"
            ),
        ));
        gismu_entries.push(((*gismu).to_string(), format!("\"{alias}\"")));
    }

    for (alias, gismu, swap) in CONVERTED_ALIASES {
        // validate() guarantees the referenced gismu exists in CURATED_ALIASES.
        let arity = CURATED_ALIASES
            .iter()
            .find(|(_, g, _, _)| g == gismu)
            .map(|(_, _, a, _)| *a)
            .unwrap();
        alias_entries.push((
            (*alias).to_string(),
            format!(
                "AliasEntry {{ gismu: \"{gismu}\", swap: Some({swap}), arity: {arity}, \
                 place_labels: [\"\", \"\", \"\", \"\", \"\"], \
                 label_tier: LabelTier::Positional }}"
            ),
        ));
    }

    match &lensisku {
        Some(dict) => generate_full(dict, &arity_map, &mut alias_entries, &mut gismu_entries),
        None => {
            println!(
                "cargo:warning=nibli-lexicon alias map: FALLBACK MODE (curated core, {} plain + {} converted aliases)",
                CURATED_ALIASES.len(),
                CONVERTED_ALIASES.len()
            );
        }
    }

    let mut aliases = phf_codegen::Map::new();
    for (key, value) in &alias_entries {
        aliases.entry(key.clone(), value.as_str());
    }
    let mut gismu_to_alias = phf_codegen::Map::new();
    for (key, value) in &gismu_entries {
        gismu_to_alias.entry(key.clone(), value.as_str());
    }
    let alias_dest = Path::new(&out_dir).join("generated_aliases.rs");
    let mut alias_file = BufWriter::new(File::create(&alias_dest).unwrap());
    writeln!(
        &mut alias_file,
        "pub static ALIASES: phf::Map<&'static str, AliasEntry> = \n{};",
        aliases.build()
    )
    .unwrap();
    writeln!(
        &mut alias_file,
        "pub static GISMU_TO_ALIAS: phf::Map<&'static str, &'static str> = \n{};",
        gismu_to_alias.build()
    )
    .unwrap();
}

/// Look up a curated English place-frame template for a gismu/lujvo.
/// Returns "" when none is curated (the renderer falls back to a generic frame).
fn lookup_template(word: &str) -> &'static str {
    GISMU_PLACE_TEMPLATES
        .iter()
        .find(|(w, _)| *w == word)
        .map(|(_, t)| *t)
        .unwrap_or("")
}

/// Escape a string for embedding in a Rust string literal. The lensisku JSON is already
/// decoded by serde (no XML entities), so only Rust-literal escaping is needed.
fn escape_str(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

/// Hardcoded arities for core gismu where definition text is unreliable.
const CORE_GISMU_ARITIES: &[(&str, usize)] = &[
    ("klama", 5),
    ("ctuca", 5),
    ("ciska", 5),
    ("mrilu", 5),
    ("bevri", 5),
    ("vecnu", 4),
    ("dunda", 3),
    ("prami", 2),
    ("gerku", 2),
    ("mlatu", 2),
    ("cmene", 3),
    ("cusku", 4),
    ("djuno", 4),
    ("jimpe", 2),
    ("gasnu", 2),
    ("penmi", 3),
    ("tavla", 4),
    ("catra", 2),
    ("citka", 2),
    ("pinxe", 2),
    ("cadzu", 3),
    ("bajra", 4),
    ("viska", 3),
    ("tirna", 3),
    ("nelci", 2),
    ("djica", 3),
    ("nitcu", 3),
    ("kakne", 2),
    ("ckana", 2),
    ("zdani", 2),
    ("zarci", 3),
    ("bridi", 3),
    ("jbena", 4),
    ("morsi", 1),
    ("sutra", 2),
    ("melbi", 3),
    ("barda", 3),
    ("cmalu", 3),
    ("xamgu", 3),
    ("xlali", 3),
    ("blanu", 1),
    ("xunre", 1),
    ("pelxu", 1),
    ("crino", 1),
    // bilga/curmi reach the fallback build only via GISMU_GLOSS_OVERRIDES,
    // which used to default them to arity 2 while the full lensisku build
    // derives 3 (bilga: obliged-to-x2-by-standard-x3; curmi:
    // permits-x2-under-conditions-x3) — a cross-mode flap the verify-dict
    // gate would trip on. Pin the true arities so both builds agree.
    ("bilga", 3),
    ("curmi", 3),
    // dilcu/jmive were the same flap in the other direction: the fallback
    // table said 3/1 while the full lensisku build derives 4 (quotient with
    // remainder x4) and 2 (alive by standard x2) — found 2026-07-12 by
    // nibli-lexicon's build-time drift guard, now pinned so a future
    // export change can't re-flap (the verify-nibli-kr-dict gate checks both
    // modes against the nibli-kr alias map).
    ("dilcu", 4),
    ("jmive", 2),
    // tenfa: the external-compute smoke's KR payload (`? tenfa(8, 2, 3).`)
    // resolves via identity passthrough, so the fallback build needs the
    // arity (full lensisku derives 3: result, base, exponent).
    ("tenfa", 3),
    // klani: the dose-aggregation engine test's KR payload (identity
    // spelling; full lensisku derives 3: quantity, number, scale).
    ("klani", 3),
    // KR test-corpus + shipped-corpus vocabulary (post-DROP: the KR front-end
    // fails closed on unknown names, so every word a shipped corpus or test
    // uses must resolve in the fallback build too). Arities follow the full
    // lensisku derivation.
    ("pendo", 2),
    ("xagji", 2),
    ("batci", 4),
    ("plise", 2),
    ("tarmi", 2),
    ("nupre", 3),
    ("satci", 3),
    ("judri", 3),
    ("krici", 3),
    ("kunti", 2),
    ("lijda", 3),
    ("marbi", 3),
    ("natmi", 2),
    ("sarcu", 3),
    ("sipna", 1),
];

/// Minimal fallback when dictionary-en.json is absent locally.
const FALLBACK_GISMU_ENTRIES: &[(&str, usize, &str)] = &[
    ("klama", 5, "come"),
    ("ctuca", 5, "teach"),
    ("ciska", 5, "write"),
    ("mrilu", 5, "mail"),
    ("bevri", 5, "carry"),
    ("vecnu", 4, "sell"),
    ("dunda", 3, "give"),
    ("prami", 2, "love"),
    ("gerku", 2, "dog"),
    ("mlatu", 2, "cat"),
    ("cmene", 3, "name"),
    ("cusku", 4, "express"),
    ("djuno", 4, "know"),
    ("jimpe", 2, "understand"),
    ("gasnu", 2, "do"),
    ("penmi", 3, "meet"),
    ("tavla", 4, "talk"),
    ("catra", 2, "kill"),
    ("citka", 2, "eat"),
    ("pinxe", 2, "drink"),
    ("cadzu", 3, "walk"),
    ("bajra", 4, "run"),
    ("viska", 3, "see"),
    ("tirna", 3, "hear"),
    ("nelci", 2, "like"),
    ("djica", 3, "desire"),
    ("nitcu", 3, "need"),
    ("kakne", 2, "can"),
    ("ckana", 2, "bed"),
    ("zdani", 2, "home"),
    ("zarci", 3, "market"),
    ("bridi", 3, "predicate"),
    ("jbena", 4, "born"),
    ("morsi", 1, "dead"),
    ("sutra", 2, "fast"),
    ("melbi", 3, "beautiful"),
    ("barda", 3, "big"),
    ("cmalu", 3, "small"),
    ("xamgu", 3, "good"),
    ("xlali", 3, "bad"),
    ("blanu", 1, "blue"),
    ("xunre", 1, "red"),
    ("pelxu", 1, "yellow"),
    ("crino", 1, "green"),
    ("prenu", 1, "person"),
    ("pilji", 3, "multiply"),
    ("sumji", 3, "sum"),
    // dilcu/jmive arities follow the full lensisku derivation (4: quotient
    // with remainder x4; 2: alive by standard x2), matching the
    // CORE_GISMU_ARITIES pins above — the fallback table previously said
    // 3/1, a cross-mode flap the verify-nibli-kr-dict gate now trips on.
    ("dilcu", 4, "divide"),
    ("tenfa", 3, "exponential"),
    ("klani", 3, "quantity"),
    ("pendo", 2, "friend"),
    ("xagji", 2, "hungry"),
    ("batci", 4, "bite"),
    ("plise", 2, "apple"),
    ("tarmi", 2, "shape"),
    ("nupre", 3, "promise"),
    ("satci", 3, "exact"),
    ("judri", 3, "address"),
    ("krici", 3, "believe"),
    ("kunti", 2, "empty"),
    ("lijda", 3, "religion"),
    ("marbi", 3, "shelter"),
    ("natmi", 2, "nation"),
    ("sarcu", 3, "necessary"),
    ("sipna", 1, "sleep"),
    ("danlu", 2, "animal"),
    ("jmive", 2, "live"),
    // GDPR / drug-interaction corpus proxy + regulatory vocabulary. Without
    // dictionary-en.json these would vanish from the no-data build, so `get_template` and
    // the rendered place-frames silently diverge from the data build and the render /
    // corpus-proxy / C19 back-translation tests fail only in CI. Arities and glosses
    // mirror exactly what the data build derives from lensisku (verified against the
    // generated dictionary), so adding them as tier-2 entries leaves the data build
    // unchanged. Templates come from GISMU_PLACE_TEMPLATES via lookup_template.
    ("zanru", 2, "approve"),
    ("pilno", 3, "use"),
    ("katna", 3, "cut"),
    ("zenba", 3, "increase"),
    ("cinla", 3, "thin"),
    ("ckape", 3, "peril"),
    ("vimcu", 4, "delete"),
    ("javni", 3, "rule"),
    ("datni", 3, "data"),
    ("turni", 2, "govern"),
    // nibli-lexicon curated vocabulary: every gismu the nibli-kr curated alias
    // table references must resolve here too, with the SAME arity in both build
    // modes — otherwise a CI fallback build silently compiles these words with
    // the arity-2 default while nibli-kr's curated table (and every full local
    // build) says otherwise, the exact cross-mode drift class the
    // verify-nibli-kr-dict gate rejects (its first fallback run flagged all 34).
    // Arities mirror the full lensisku derivation (verified equal to nibli-kr's
    // curated arities by nibli-lexicon's build-time drift guard); glosses
    // are the first lensisku gloss keyword, matching the data build's chain.
    ("birti", 2, "certain"),
    ("cfila", 3, "flaw"),
    ("cidja", 2, "food"),
    ("cipni", 2, "bird"),
    ("ciste", 4, "system"),
    ("dinju", 2, "building"),
    ("drani", 4, "correct"),
    ("dunli", 3, "equal"),
    ("facki", 3, "discover"),
    ("fanta", 2, "prevent"),
    ("finpe", 2, "fish"),
    ("flalu", 5, "law"),
    ("kajde", 3, "warn"),
    ("kanro", 2, "healthy"),
    ("krinu", 2, "reason"),
    ("kurji", 2, "take care of"),
    ("litki", 3, "liquid"),
    ("logji", 2, "logic"),
    ("marce", 4, "vehicle"),
    ("masno", 2, "slow"),
    ("mleca", 4, "less"),
    ("nanmu", 1, "man"),
    ("nibli", 3, "necessitate"),
    ("ninmu", 1, "woman"),
    ("notci", 4, "message"),
    ("ponse", 3, "possess"),
    ("remna", 1, "human"),
    ("tadni", 2, "study"),
    ("verba", 3, "child"),
    ("xanri", 2, "imaginary"),
    ("xukmi", 3, "chemical"),
    ("zbasu", 3, "build"),
    ("zmadu", 4, "more"),
    ("zukte", 3, "act"),
];

/// Curated gloss overrides for gismu where the first lensisku gloss keyword
/// is alphabetically accidental rather than canonical (e.g. gerku's
/// gloss keywords are bitch/canine/dog — "dog" is the right back-translation).
/// Consulted before FALLBACK_GISMU_ENTRIES and the lensisku gloss keywords.
const GISMU_GLOSS_OVERRIDES: &[(&str, &str)] = &[("bilga", "must"), ("curmi", "permit")];

/// Curated English place-frame templates, keyed by gismu/lujvo, using `{x1}`..`{x5}`
/// placeholders. Covers the predicates the shipped corpora (`readme.lojban`,
/// `gdpr.lojban`, `drug-interactions.lojban`) actually use; everything else falls
/// back to a generic gloss-based frame in the renderer. Templates are written so
/// the filled form reads as a complete English clause. Keep to 1-/2-place frames
/// where the reading is unambiguous; higher-arity frames spell every place so the
/// renderer can drop trailing unfilled (`zo'e`) places cleanly.
///
/// NOTE: templates are keyed on the bare predicate name. `se`/`te`/… conversion is
/// already reflected in the IR's argument order, so the same template renders both
/// `prami` and `se prami` correctly (the swapped sumti land in the swapped `{xN}`).
const GISMU_PLACE_TEMPLATES: &[(&str, &str)] = &[
    // ── Motion / action verbs ──
    ("klama", "{x1} goes to {x2} from {x3} via {x4} using {x5}"),
    ("bevri", "{x1} carries {x2} to {x3} from {x4} via {x5}"),
    ("cadzu", "{x1} walks on {x2} using {x3}"),
    ("bajra", "{x1} runs on {x2} to {x3} from {x4}"),
    ("citka", "{x1} eats {x2}"),
    ("pinxe", "{x1} drinks {x2}"),
    ("catra", "{x1} kills {x2}"),
    ("gasnu", "{x1} does {x2}"),
    ("zukte", "{x1} acts toward goal {x2}"),
    ("zbasu", "{x1} makes {x2} from {x3}"),
    // ── Mental / communicative ──
    ("prami", "{x1} loves {x2}"),
    ("nelci", "{x1} likes {x2}"),
    ("djica", "{x1} desires {x2}"),
    ("djuno", "{x1} knows {x2}"),
    ("jimpe", "{x1} understands {x2}"),
    ("viska", "{x1} sees {x2}"),
    ("tirna", "{x1} hears {x2}"),
    ("tavla", "{x1} talks to {x2} about {x3}"),
    ("cusku", "{x1} expresses {x2} to {x3} via {x4}"),
    ("ctuca", "{x1} teaches {x2} to {x3}"),
    ("tadni", "{x1} studies {x2}"),
    ("nitcu", "{x1} needs {x2}"),
    ("kakne", "{x1} is able to {x2}"),
    ("kurji", "{x1} takes care of {x2}"),
    ("ponse", "{x1} possesses {x2}"),
    ("penmi", "{x1} meets {x2}"),
    // ── Deontic / regulatory (incl. corpus proxy vocabulary) ──
    ("bilga", "{x1} is obligated to {x2}"),
    ("curmi", "{x1} permits {x2}"),
    ("fanta", "{x1} prevents {x2}"),
    ("kajde", "{x1} warns about {x2}"),
    ("flalu", "{x1} is a law about {x2}"),
    ("javni", "{x1} is a rule about {x2}"),
    ("nibli", "{x1} logically entails {x2}"),
    ("krinu", "{x1} is the reason for {x2}"),
    // ── Corpus proxy vocabulary (GDPR + drug-interaction case studies) ──
    // Literal, grammatical gismu frames, place-count matched to how the corpora
    // use them; the proxy reading (consent / toxicity risk / metabolism / …) is
    // the reader's overlay, not the dictionary's. `se`-converted uses (se vimcu,
    // se katna) swap args at compile time, so these key on the BARE gismu.
    ("zanru", "{x1} approves of {x2}"), // GDPR: consents to a plan/treatment
    ("vimcu", "{x1} is removed"),       // GDPR se vimcu: data is erased (Art 17)
    ("pilno", "{x1} uses {x2}"),        // DDI: a patient takes a drug
    ("katna", "{x1} cuts {x2}"),        // DDI se katna: substrate metabolised by enzyme
    ("zenba", "{x1} increases"),        // DDI: drug concentration rises
    ("cinla", "{x1} is thin"),          // DDI: narrow therapeutic index
    ("ckape", "{x1} is in danger"),     // DDI: toxicity risk
    // ── Class predicates (x1 is a …) ──
    ("danlu", "{x1} is an animal"),
    ("gerku", "{x1} is a dog"),
    ("mlatu", "{x1} is a cat"),
    ("cipni", "{x1} is a bird"),
    ("finpe", "{x1} is a fish"),
    ("prenu", "{x1} is a person"),
    ("nanmu", "{x1} is a man"),
    ("ninmu", "{x1} is a woman"),
    ("verba", "{x1} is a child"),
    ("remna", "{x1} is a human"),
    ("xukmi", "{x1} is a chemical"),
    ("dinju", "{x1} is a building"),
    ("zdani", "{x1} is a home"),
    ("zarci", "{x1} is a market"),
    ("marce", "{x1} is a vehicle"),
    ("cidja", "{x1} is food"),
    ("litki", "{x1} is a liquid"),
    ("datni", "{x1} is data"),
    ("ciste", "{x1} is a system"),
    ("logji", "{x1} is logical"),
    // ── Property predicates (x1 is …) ──
    ("jmive", "{x1} is alive"),
    ("morsi", "{x1} is dead"),
    ("barda", "{x1} is big"),
    ("cmalu", "{x1} is small"),
    ("sutra", "{x1} is fast"),
    ("masno", "{x1} is slow"),
    ("xamgu", "{x1} is good"),
    ("xlali", "{x1} is bad"),
    ("kanro", "{x1} is healthy"),
    ("melbi", "{x1} is beautiful"),
    ("birti", "{x1} is certain"),
    ("xanri", "{x1} is imaginary"),
    // ── Numeric / compute (arithmetic relations) ──
    ("pilji", "{x1} is the product of {x2} and {x3}"),
    ("sumji", "{x1} is the sum of {x2} and {x3}"),
    ("dilcu", "{x1} is the quotient of {x2} and {x3}"),
    ("zmadu", "{x1} is greater than {x2}"),
    ("mleca", "{x1} is less than {x2}"),
    ("dunli", "{x1} equals {x2}"),
];

/// Hardcoded gloss overrides for common cmavo where jbovlaste glosses
/// are too technical for readable back-translation.
const CMAVO_GLOSS_OVERRIDES: &[(&str, &str)] = &[
    // Determiner (articles)
    ("lo", "the"),
    ("le", "the"),
    ("la", ""),
    // Structural terminators (suppress in output)
    ("cu", ""),
    ("ku", ""),
    ("ku'o", ""),
    ("kei", ""),
    ("ke'e", ""),
    ("vau", ""),
    ("li'u", ""),
    ("be'o", ""),
    ("fe'u", ""),
    // Negation
    ("na", "not"),
    ("nai", "not"),
    // Conversion
    ("se", "(swap-2)"),
    ("te", "(swap-3)"),
    ("ve", "(swap-4)"),
    ("xe", "(swap-5)"),
    // Tense
    ("pu", "[past]"),
    ("ca", "[present]"),
    ("ba", "[future]"),
    // Quantifiers
    ("ro", "all"),
    ("su'o", "some"),
    ("pa", "one"),
    ("re", "two"),
    ("ci", "three"),
    ("vo", "four"),
    ("mu", "five"),
    // Sentence separator
    (".i", "."),
    // Relative clauses
    ("poi", "which"),
    ("noi", ", which"),
    ("voi", "the-said"),
    ("ke'a", "(it)"),
    // Abstractions
    ("nu", "event-of"),
    ("du'u", "that"),
    ("ka", "property-of"),
    ("ni", "amount-of"),
    ("si'o", "concept-of"),
    // Pro-sumti
    ("mi", "I"),
    ("do", "you"),
    ("ti", "this"),
    ("ta", "that"),
    ("tu", "yonder"),
    ("zo'e", "(something)"),
    ("ri", "(it)"),
    // Logic variables
    ("da", "X"),
    ("de", "Y"),
    ("di", "Z"),
    // Questions
    ("ma", "what?"),
    ("mo", "is-what?"),
    ("xu", "is-it-true?"),
    // Place tags
    ("fa", "(x1=)"),
    ("fe", "(x2=)"),
    ("fi", "(x3=)"),
    ("fo", "(x4=)"),
    ("fu", "(x5=)"),
    // Forethought connectives
    ("ge", "both"),
    ("gi", "and"),
    ("ga", "either"),
    ("ganai", "if"),
    // Afterthought connectives
    ("je", "and"),
    ("ja", "or"),
    ("jo", "iff"),
    ("ju", "whether-or-not"),
    // DeonticMoods
    ("ei", "[should]"),
    ("e'e", "[may]"),
    // Modal tags
    ("ri'a", "because"),
    ("ni'i", "logically-because"),
    ("mu'i", "motivated-by"),
    ("ki'u", "justified-by"),
    ("pi'o", "using"),
    ("ba'i", "instead-of"),
    // Misc
    ("be", "with"),
    ("bei", "and-with"),
    ("pe", "associated-with"),
    ("lu", "\""),
    ("li", "#"),
    ("ce'u", "(lambda)"),
    ("go'i", "(previous)"),
];

// ─────────────────────────────────────────────────────────────────────────────
// Alias-map generation (folded from nibli-lexicon). Consumes the SAME
// parsed export + the in-loop `arity_map`, so the alias arity and the shipped
// dictionary arity agree by construction.
// ─────────────────────────────────────────────────────────────────────────────

/// FULL MODE: generate an alias for every non-curated gismu in the export.
///
/// Alias = pinned spelling (ALIAS_PINS) else the first gloss keyword normalized
/// (base-form as-is — no mechanical inflection; corpus/spec vocabulary is pinned
/// 3rd-person in CURATED_ALIASES instead). Arity comes from `arity_map` (the
/// forward-dict data that produces DICTIONARY), so agreement holds by
/// construction. UNPINNED problems fail the build with the full offender list.
fn generate_full(
    dict: &[LensiskuEntry],
    arity_map: &HashMap<String, Option<usize>>,
    alias_entries: &mut Vec<(String, String)>,
    gismu_entries: &mut Vec<(String, String)>,
) {
    let curated_gismu: HashSet<&str> = CURATED_ALIASES.iter().map(|(_, g, _, _)| *g).collect();
    let pins: HashMap<&str, &str> = ALIAS_PINS.iter().copied().collect();
    let mut taken: HashSet<String> = alias_entries.iter().map(|(a, _)| a.clone()).collect();

    let mut errors: Vec<String> = Vec::new();
    let (mut n_lensisku, mut n_prose, mut n_positional) = (0usize, 0usize, 0usize);
    let mut generated = 0usize;

    for entry in dict {
        if entry.word_type != "gismu" || entry.word.is_empty() {
            continue;
        }
        let word = entry.word.as_str();
        if curated_gismu.contains(word) {
            continue;
        }

        let alias: String = match pins.get(word) {
            Some(pin) => (*pin).to_string(),
            None => match entry.gloss_keywords.first() {
                Some(k) => normalize(&k.word),
                None => {
                    errors.push(format!(
                        "{word}: no gloss_keywords in export — pin required"
                    ));
                    continue;
                }
            },
        };
        if !ident_ok(&alias) {
            errors.push(format!(
                "{word}: derived alias {alias:?} is not ident-shaped — pin required"
            ));
            continue;
        }
        if is_reserved(&alias) {
            errors.push(format!(
                "{word}: derived alias {alias:?} is a nibli KR keyword — pin required"
            ));
            continue;
        }
        // A self-alias (alias == its own gismu) is the identity passthrough spelled
        // explicitly — harmless. Any OTHER dictionary word would shadow that word's
        // identity passthrough.
        if alias != word && arity_map.get(alias.as_str()).copied().flatten().is_some() {
            errors.push(format!(
                "{word}: derived alias {alias:?} is itself a dictionary word (would shadow \
                 the identity-gismu passthrough) — pin required"
            ));
            continue;
        }
        if !taken.insert(alias.clone()) {
            errors.push(format!(
                "{word}: derived alias {alias:?} collides with an existing alias — pin required"
            ));
            continue;
        }

        let arity = arity_map
            .get(word)
            .copied()
            .flatten()
            .unwrap_or(2)
            .clamp(1, 5) as u8;

        let (labels, tier) = derive_labels(entry, arity);
        match tier {
            "Lensisku" => n_lensisku += 1,
            "Prose" => n_prose += 1,
            _ => n_positional += 1,
        }
        let labels_src = labels
            .iter()
            .map(|l| format!("\"{l}\""))
            .collect::<Vec<_>>()
            .join(", ");
        alias_entries.push((
            alias.clone(),
            format!(
                "AliasEntry {{ gismu: \"{word}\", swap: None, arity: {arity}, \
                 place_labels: [{labels_src}], label_tier: LabelTier::{tier} }}"
            ),
        ));
        gismu_entries.push((word.to_string(), format!("\"{alias}\"")));
        generated += 1;
    }

    // Data-mode drift guard: curated arities must equal what the forward dict derives.
    for (alias, gismu, arity, _) in CURATED_ALIASES {
        match arity_map.get(*gismu).copied().flatten() {
            Some(dict_arity) if dict_arity == *arity as usize => {}
            Some(dict_arity) => errors.push(format!(
                "curated {alias:?} ({gismu}): declared arity {arity} != dictionary arity {dict_arity}"
            )),
            None => errors.push(format!(
                "curated {alias:?}: gismu {gismu:?} unknown to the dictionary"
            )),
        }
    }
    // Dead-pin guard: a pin for a curated (or unknown) word is a mistake.
    let export_gismu: HashSet<&str> = dict
        .iter()
        .filter(|e| e.word_type == "gismu")
        .map(|e| e.word.as_str())
        .collect();
    for (gismu, alias) in ALIAS_PINS {
        if curated_gismu.contains(gismu) {
            errors.push(format!(
                "pin ({gismu:?}, {alias:?}) is dead — the word is already in CURATED_ALIASES"
            ));
        }
        if !export_gismu.contains(gismu) {
            errors.push(format!(
                "pin ({gismu:?}, {alias:?}) is dead — no such gismu in the export"
            ));
        }
    }

    if !errors.is_empty() {
        panic!(
            "nibli-lexicon alias generation failed ({} error(s)):\n  {}",
            errors.len(),
            errors.join("\n  ")
        );
    }

    let total_plain = CURATED_ALIASES.len() + generated;
    assert!(
        total_plain >= 1300,
        "nibli-lexicon alias coverage floor: {total_plain} plain aliases < 1300"
    );
    println!(
        "cargo:warning=nibli-lexicon alias map: FULL MODE ({} plain aliases = {} curated + {} generated; \
         {} converted; labels: {} lensisku, {} prose, {} positional)",
        total_plain,
        CURATED_ALIASES.len(),
        generated,
        CONVERTED_ALIASES.len(),
        n_lensisku,
        n_prose,
        n_positional
    );
}

/// Label chain for a generated entry: lensisku `place_keywords` (ordered from
/// x1; skipped entirely when longer than the arity) → prose heuristic →
/// positional. Generated labels are SANITIZED to `""` rather than failing the
/// build (curated labels, by contrast, fail the build in `validate()`).
fn derive_labels(entry: &LensiskuEntry, arity: u8) -> ([String; 5], &'static str) {
    if !entry.place_keywords.is_empty() && entry.place_keywords.len() <= arity as usize {
        let mut labels: [String; 5] = Default::default();
        for (i, kw) in entry.place_keywords.iter().enumerate().take(5) {
            labels[i] = normalize(&kw.word);
        }
        sanitize_labels(&mut labels, arity);
        if labels.iter().any(|l| !l.is_empty()) {
            return (labels, "Lensisku");
        }
    }
    let mut labels = label::prose_labels(&entry.definition, arity);
    sanitize_labels(&mut labels, arity);
    if labels.iter().any(|l| !l.is_empty()) {
        return (labels, "Prose");
    }
    (Default::default(), "Positional")
}

/// Clear any generated label that is non-ident, reserved, an x-tag lookalike,
/// beyond the arity, or a duplicate of an earlier (surviving) label.
fn sanitize_labels(labels: &mut [String; 5], arity: u8) {
    for i in 0..5 {
        let keep = {
            let l = &labels[i];
            !l.is_empty()
                && ident_ok(l)
                && !is_reserved(l)
                && !looks_like_place_tag(l)
                && i < arity as usize
                && !labels[..i].contains(l)
        };
        if !keep {
            labels[i].clear();
        }
    }
}

/// Gloss/label normalization: lowercase; space, `/`, `-` → `_`.
fn normalize(raw: &str) -> String {
    raw.to_ascii_lowercase().replace([' ', '/', '-'], "_")
}

fn ident_ok(s: &str) -> bool {
    let mut chars = s.chars();
    matches!(chars.next(), Some('a'..='z'))
        && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
}

fn looks_like_place_tag(s: &str) -> bool {
    s.len() == 2 && s.starts_with('x') && matches!(s.as_bytes()[1], b'1'..=b'5')
}

/// Fail-closed CURATED-table validation, both build modes: any violation fails
/// the BUILD with the full offender list (the alias map is trusted base — a bad
/// entry must never ship). Generation-side checks live in `generate_full`.
fn validate() {
    let mut errors: Vec<String> = Vec::new();

    let mut seen_aliases = HashSet::new();
    let mut seen_gismu = HashSet::new();

    for (alias, gismu, arity, labels) in CURATED_ALIASES {
        if !ident_ok(alias) {
            errors.push(format!(
                "alias {alias:?} is not ident-shaped ([a-z][a-z0-9_]*)"
            ));
        }
        if is_reserved(alias) {
            errors.push(format!("alias {alias:?} collides with a nibli KR keyword"));
        }
        if !seen_aliases.insert(*alias) {
            errors.push(format!("duplicate alias {alias:?}"));
        }
        if !seen_gismu.insert(*gismu) {
            errors.push(format!(
                "gismu {gismu:?} has two plain aliases — GISMU_TO_ALIAS would be ambiguous"
            ));
        }
        if !(1..=5).contains(arity) {
            errors.push(format!("{alias:?}: arity {arity} outside 1..=5"));
        }
        for (i, label) in labels.iter().enumerate() {
            if label.is_empty() {
                continue;
            }
            if !ident_ok(label) {
                errors.push(format!("{alias:?}: label {label:?} is not ident-shaped"));
            }
            if is_reserved(label) {
                errors.push(format!(
                    "{alias:?}: label {label:?} collides with a nibli KR keyword"
                ));
            }
            if looks_like_place_tag(label) {
                errors.push(format!(
                    "{alias:?}: label {label:?} looks like a raw place tag — a label spelled \
                     x2 that means x3 would silently reroute arguments"
                ));
            }
            if i >= *arity as usize {
                errors.push(format!(
                    "{alias:?}: label {label:?} at place x{} exceeds arity {arity}",
                    i + 1
                ));
            }
            if labels[..i].contains(label) {
                errors.push(format!(
                    "{alias:?}: label {label:?} duplicated within the entry"
                ));
            }
        }
    }

    for (alias, gismu, swap) in CONVERTED_ALIASES {
        if !ident_ok(alias) {
            errors.push(format!("converted alias {alias:?} is not ident-shaped"));
        }
        if is_reserved(alias) {
            errors.push(format!(
                "converted alias {alias:?} collides with a nibli KR keyword"
            ));
        }
        if !seen_aliases.insert(*alias) {
            errors.push(format!("duplicate alias {alias:?} (converted vs plain)"));
        }
        match CURATED_ALIASES.iter().find(|(_, g, _, _)| g == gismu) {
            None => errors.push(format!(
                "converted alias {alias:?} references gismu {gismu:?} absent from CURATED_ALIASES"
            )),
            Some((_, _, arity, _)) => {
                if !(2..=*arity).contains(swap) {
                    errors.push(format!(
                        "converted alias {alias:?}: swap x1↔x{swap} outside 2..=arity({arity})"
                    ));
                }
            }
        }
    }

    let mut seen_pinned_gismu = HashSet::new();
    for (gismu, alias) in ALIAS_PINS {
        if !ident_ok(alias) {
            errors.push(format!("pin alias {alias:?} ({gismu}) is not ident-shaped"));
        }
        if is_reserved(alias) {
            errors.push(format!(
                "pin alias {alias:?} ({gismu}) collides with a nibli KR keyword"
            ));
        }
        if !seen_aliases.insert(*alias) {
            errors.push(format!(
                "pin alias {alias:?} ({gismu}) duplicates another alias"
            ));
        }
        if !seen_pinned_gismu.insert(*gismu) {
            errors.push(format!("gismu {gismu:?} pinned twice"));
        }
    }

    if !errors.is_empty() {
        panic!(
            "nibli-lexicon alias-table validation failed ({} error(s)):\n  {}",
            errors.len(),
            errors.join("\n  ")
        );
    }
}
