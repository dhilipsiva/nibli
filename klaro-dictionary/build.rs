use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

// Curated alias tables + reserved-word list, shared with the crate (compiled here
// as build-script modules; `#[cfg(test)]` is false for a build script, so their
// test submodules are excluded — the smuni-dictionary `src/arity.rs` pattern).
#[path = "src/curated.rs"]
mod curated;
#[path = "src/reserved.rs"]
mod reserved;

use curated::{CONVERTED_ALIASES, CURATED_ALIASES};
use reserved::is_reserved;

fn main() {
    println!("cargo:rerun-if-changed=src/curated.rs");
    println!("cargo:rerun-if-changed=src/reserved.rs");

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

    let mut aliases = phf_codegen::Map::new();
    for (key, value) in &alias_entries {
        aliases.entry(key.clone(), value.as_str());
    }
    let mut gismu_to_alias = phf_codegen::Map::new();
    for (key, value) in &gismu_entries {
        gismu_to_alias.entry(key.clone(), value.as_str());
    }

    // In this milestone the curated fallback path is the ONLY path; the loud banner
    // keeps parity with smuni-dictionary's no-data mode and stays honest once the
    // full lensisku generation lands beside it.
    println!(
        "cargo:warning=klaro-dictionary: FALLBACK MODE (curated core, {} plain + {} converted aliases)",
        CURATED_ALIASES.len(),
        CONVERTED_ALIASES.len()
    );

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

/// Fail-closed table validation: any violation fails the BUILD with the full
/// offender list (the alias map is trusted base — a bad entry must never ship).
fn validate() {
    let mut errors: Vec<String> = Vec::new();

    let ident_ok = |s: &str| {
        let mut chars = s.chars();
        matches!(chars.next(), Some('a'..='z'))
            && chars.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
    };
    let looks_like_place_tag =
        |s: &str| s.len() == 2 && s.starts_with('x') && matches!(s.as_bytes()[1], b'1'..=b'5');

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

    if !errors.is_empty() {
        panic!(
            "klaro-dictionary curated-table validation failed ({} error(s)):\n  {}",
            errors.len(),
            errors.join("\n  ")
        );
    }
}
