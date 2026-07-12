use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

// Curated alias tables, prose-label heuristic, and reserved-word list, shared
// with the crate (compiled here as build-script modules; `#[cfg(test)]` is false
// for a build script, so their test submodules are excluded — the
// smuni-dictionary `src/arity.rs` pattern).
#[path = "src/curated.rs"]
mod curated;
#[path = "src/label.rs"]
mod label;
#[path = "src/reserved.rs"]
mod reserved;

use curated::{ALIAS_PINS, CONVERTED_ALIASES, CURATED_ALIASES};
use reserved::is_reserved;

/// A single entry from the lensisku `dictionary-en.json` bulk export. Only the
/// fields alias generation consumes are declared; serde ignores the rest.
/// Unlike smuni-dictionary's copy, this one ALSO consumes `place_keywords` —
/// the ordered per-place label list (x1 first; present on 70/1,338 gismu).
#[derive(serde::Deserialize)]
struct LensiskuEntry {
    word: String,
    word_type: String,
    definition: String,
    #[serde(default)]
    gloss_keywords: Vec<Keyword>,
    #[serde(default)]
    place_keywords: Vec<Keyword>,
}

/// One keyword; only `word` is consumed (`meaning` is nullable prose).
#[derive(serde::Deserialize)]
struct Keyword {
    word: String,
}

fn main() {
    println!("cargo:rerun-if-changed=src/curated.rs");
    println!("cargo:rerun-if-changed=src/label.rs");
    println!("cargo:rerun-if-changed=src/reserved.rs");
    println!("cargo:rerun-if-changed=../dictionary-en.json");

    validate();

    // Collect entries first (phf_codegen borrows value strings for the map's lifetime).
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

    match fs::read_to_string("../dictionary-en.json").ok() {
        Some(content) => generate_full(&content, &mut alias_entries, &mut gismu_entries),
        None => {
            println!(
                "cargo:warning=klaro-dictionary: FALLBACK MODE (curated core, {} plain + {} converted aliases)",
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

    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("generated_aliases.rs");
    let mut file = BufWriter::new(File::create(&dest_path).unwrap());

    writeln!(
        &mut file,
        "pub static ALIASES: phf::Map<&'static str, AliasEntry> = \n{};",
        aliases.build()
    )
    .unwrap();
    writeln!(
        &mut file,
        "pub static GISMU_TO_ALIAS: phf::Map<&'static str, &'static str> = \n{};",
        gismu_to_alias.build()
    )
    .unwrap();
}

/// FULL MODE: generate an alias for every non-curated gismu in the export.
///
/// Alias = pinned spelling (ALIAS_PINS) else the first gloss keyword normalized
/// (base-form as-is — user decision 2026-07-12: no mechanical inflection, since
/// the export carries no part-of-speech data and inflecting nouns/adjectives
/// would corrupt them; corpus/spec vocabulary is pinned 3rd-person in
/// CURATED_ALIASES instead). Arity comes from smuni-dictionary (build-dep — the
/// actual shipped map, so agreement holds by construction). UNPINNED problems
/// fail the build with the full offender list.
fn generate_full(
    json: &str,
    alias_entries: &mut Vec<(String, String)>,
    gismu_entries: &mut Vec<(String, String)>,
) {
    let dict: Vec<LensiskuEntry> = serde_json::from_str(json)
        .expect("dictionary-en.json is not a valid lensisku export array");

    let curated_gismu: HashSet<&str> = CURATED_ALIASES.iter().map(|(_, g, _, _)| *g).collect();
    let pins: HashMap<&str, &str> = ALIAS_PINS.iter().copied().collect();
    let mut taken: HashSet<String> = alias_entries.iter().map(|(a, _)| a.clone()).collect();

    let mut errors: Vec<String> = Vec::new();
    let (mut n_lensisku, mut n_prose, mut n_positional) = (0usize, 0usize, 0usize);
    let mut generated = 0usize;

    for entry in &dict {
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
                "{word}: derived alias {alias:?} is a Klaro keyword — pin required"
            ));
            continue;
        }
        // A self-alias (alias == its own gismu, e.g. centi→"centi") is the
        // identity passthrough spelled explicitly — harmless. Any OTHER
        // dictionary word would shadow that word's identity passthrough.
        if alias != word && smuni_dictionary::get_arity(&alias).is_some() {
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

        // Every gismu in the export is present in smuni's map (same file); the
        // fallback keeps generation total anyway.
        let arity = smuni_dictionary::get_arity(word).unwrap_or(2).clamp(1, 5) as u8;

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

    // Data-mode drift guard: curated arities must equal what smuni derives from
    // the same export (the cross-mode flap CORE_GISMU_ARITIES pins exist for).
    for (alias, gismu, arity, _) in CURATED_ALIASES {
        match smuni_dictionary::get_arity(gismu) {
            Some(smuni_arity) if smuni_arity == *arity as usize => {}
            Some(smuni_arity) => errors.push(format!(
                "curated {alias:?} ({gismu}): declared arity {arity} != smuni arity {smuni_arity}"
            )),
            None => errors.push(format!(
                "curated {alias:?}: gismu {gismu:?} unknown to smuni-dictionary"
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
            "klaro-dictionary full generation failed ({} error(s)):\n  {}",
            errors.len(),
            errors.join("\n  ")
        );
    }

    let total_plain = CURATED_ALIASES.len() + generated;
    assert!(
        total_plain >= 1300,
        "klaro-dictionary coverage floor: {total_plain} plain aliases < 1300"
    );
    println!(
        "cargo:warning=klaro-dictionary: FULL MODE ({} plain aliases = {} curated + {} generated; \
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
/// x1; skipped entirely when longer than the arity — arity-inconsistent) →
/// prose heuristic → positional. Generated labels are SANITIZED to `""` rather
/// than failing the build: positional is always honest, and a 9.9 MB external
/// dump must not brick the build on one weird label. (Curated labels, by
/// contrast, fail the build in `validate()`.)
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

/// Gloss/label normalization: lowercase; space, `/`, `-` → `_`. (For glosses the
/// first `/`-alternative policy lives in the prose module; gloss KEYWORDS are
/// single terms where `/` is rare and a conjoined spelling is acceptable.)
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

    let mut seen_aliases = std::collections::HashSet::new();
    let mut seen_gismu = std::collections::HashSet::new();

    for (alias, gismu, arity, labels) in CURATED_ALIASES {
        if !ident_ok(alias) {
            errors.push(format!(
                "alias {alias:?} is not ident-shaped ([a-z][a-z0-9_]*)"
            ));
        }
        if is_reserved(alias) {
            errors.push(format!("alias {alias:?} collides with a Klaro keyword"));
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
                    "{alias:?}: label {label:?} collides with a Klaro keyword"
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
                "converted alias {alias:?} collides with a Klaro keyword"
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

    let mut seen_pinned_gismu = std::collections::HashSet::new();
    for (gismu, alias) in ALIAS_PINS {
        if !ident_ok(alias) {
            errors.push(format!("pin alias {alias:?} ({gismu}) is not ident-shaped"));
        }
        if is_reserved(alias) {
            errors.push(format!(
                "pin alias {alias:?} ({gismu}) collides with a Klaro keyword"
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
            "klaro-dictionary curated-table validation failed ({} error(s)):\n  {}",
            errors.len(),
            errors.join("\n  ")
        );
    }
}
