//! nibli-lexigen — the corpus refresh tool (`just regen-lexicon`).
//!
//! `regen` NEVER rewrites existing entries: it compares a lensisku export
//! against the COMMITTED corpus (via the compiled `nibli_lexicon` crate — the
//! pin source; no syn-parsing, no drift), emits candidate entries for export
//! gismu ABSENT from the corpus to a scratch file, and prints a drift report
//! (arity/gloss divergence between the export and committed entries).
//! Refinement stays human, in-tree.
//!
//! The one-time `bootstrap` subcommand that seeded `corpus/predicates.rs` from
//! the pre-swap build.rs artifacts retired with those artifacts — it lives in
//! git history (the corpus-series commit that landed the corpus).
//!
//! Label chain per place for NEW candidates (zero positional survivors):
//! lensisku `place_keywords[i]` → prose heuristic → GlossDerived (x1 of an
//! "is a/the <noun>" definition) → Generic filler (`subject`/`object`/
//! `place{N}`). Every candidate is sanitized (ident shape, reserved words,
//! `xN` lookalikes, in-entry duplicates) and falls through on failure.

use serde::Deserialize;
use std::collections::BTreeMap;
use std::fmt::Write as _;

#[derive(Deserialize)]
struct LensiskuEntry {
    word: String,
    word_type: String,
    definition: String,
    #[serde(default)]
    gloss_keywords: Vec<GlossKeyword>,
    #[serde(default)]
    place_keywords: Vec<GlossKeyword>,
}

#[derive(Deserialize)]
struct GlossKeyword {
    word: String,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Tier {
    Lensisku,
    Prose,
    GlossDerived,
    Generic,
}

impl Tier {
    fn rust(self) -> &'static str {
        match self {
            Tier::Lensisku => "CorpusTier::Lensisku",
            Tier::Prose => "CorpusTier::Prose",
            Tier::GlossDerived => "CorpusTier::GlossDerived",
            Tier::Generic => "CorpusTier::Generic",
        }
    }
    fn short(self) -> &'static str {
        match self {
            Tier::Lensisku => "lensisku",
            Tier::Prose => "prose",
            Tier::GlossDerived => "gloss",
            Tier::Generic => "generic",
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd = args.first().map(String::as_str).unwrap_or("");
    let dict = flag(&args, "--dict").unwrap_or_else(|| "dictionary-en.json".into());
    match cmd {
        "regen" => {
            let out =
                flag(&args, "--out").unwrap_or_else(|| "target/lexigen/new_entries.rs".into());
            regen(&dict, &out);
        }
        _ => {
            eprintln!("usage: nibli-lexigen regen [--dict dictionary-en.json] [--out PATH]");
            std::process::exit(2);
        }
    }
}

fn flag(args: &[String], name: &str) -> Option<String> {
    args.iter()
        .position(|a| a == name)
        .and_then(|i| args.get(i + 1))
        .cloned()
}

fn load_export(path: &str) -> BTreeMap<String, LensiskuEntry> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("cannot read {path}: {e} (run `just fetch-dict`)"));
    let entries: Vec<LensiskuEntry> = serde_json::from_str(&text).expect("lensisku JSON parse");
    entries
        .into_iter()
        .filter(|e| e.word_type == "gismu")
        .map(|e| (e.word.clone(), e))
        .collect()
}

// ── sanitization (mirrors the corpus const rules) ──

fn ident_ok(s: &str) -> bool {
    let mut c = s.chars();
    matches!(c.next(), Some('a'..='z')) && c.all(|c| matches!(c, 'a'..='z' | '0'..='9' | '_'))
}

fn looks_like_place_tag(s: &str) -> bool {
    s.len() == 2 && s.starts_with('x') && matches!(s.as_bytes()[1], b'1'..=b'5')
}

/// Words that never make useful place labels (articles/copulas the heuristics
/// can leak).
const LABEL_STOPWORDS: &[&str] = &[
    "a", "an", "and", "as", "at", "be", "by", "in", "is", "it", "of", "on", "or", "the", "to",
];

fn sanitize(cand: &str, taken: &[String]) -> Option<String> {
    let cand = cand.trim().to_lowercase().replace(['-', ' ', '/'], "_");
    // A slash/space-alternative keeps its first branch.
    let cand = cand.split('_').next().unwrap_or("").to_string();
    if cand.len() < 2
        || !ident_ok(&cand)
        || LABEL_STOPWORDS.contains(&cand.as_str())
        || nibli_lexicon::reserved::is_reserved(&cand)
        || looks_like_place_tag(&cand)
        || taken.contains(&cand)
    {
        return None;
    }
    Some(cand)
}

/// x1 of a class/property-shaped definition: `$x_1$ is a/an/the <noun>`.
fn gloss_derived_x1(definition: &str) -> Option<String> {
    // First alphabetic run of a word ("a/the" -> "a", "god." -> "god").
    fn alpha_head(w: &str) -> String {
        w.chars()
            .take_while(|c| c.is_ascii_alphabetic() || *c == '-')
            .collect()
    }
    let after = definition
        .strip_prefix("$x_1$")
        .or_else(|| definition.strip_prefix("$x_{1}$"))?;
    let mut words = after.split_whitespace();
    if words.next()? != "is" {
        return None;
    }
    let mut noun = alpha_head(words.next()?);
    if matches!(noun.as_str(), "a" | "an" | "the") {
        noun = alpha_head(words.next()?);
    }
    if noun.is_empty() { None } else { Some(noun) }
}

fn generic_filler(index: usize, taken: &[String]) -> String {
    let preferred = match index {
        0 => "subject".to_string(),
        1 => "object".to_string(),
        n => format!("place{}", n + 1),
    };
    if !taken.contains(&preferred) {
        return preferred;
    }
    // Guaranteed-unique fallback: bump the number until free.
    let mut n = index + 1;
    loop {
        let cand = format!("place{n}");
        if !taken.contains(&cand) {
            return cand;
        }
        n += 1;
    }
}

struct Candidate {
    name: String,
    gismu: String,
    places: Vec<String>,
    place_tiers: Vec<Tier>,
    gloss: String,
    tier: Tier,
    definition_head: String,
}

/// Build a candidate entry for an export gismu ABSENT from the corpus.
fn build_candidate(name: &str, lens: &LensiskuEntry) -> Candidate {
    let arity = nibli_lexicon::arity::definition_arity(&lens.definition).clamp(1, 5);
    let prose = nibli_lexicon::label::prose_labels(&lens.definition, arity as u8);
    let mut places: Vec<String> = Vec::with_capacity(arity);
    let mut tiers: Vec<Tier> = Vec::with_capacity(arity);
    for i in 0..arity {
        let taken: Vec<String> = places.clone();
        let mut filled: Option<(String, Tier)> = None;
        if let Some(kw) = lens.place_keywords.get(i)
            && let Some(s) = sanitize(&kw.word, &taken)
        {
            filled = Some((s, Tier::Lensisku));
        }
        if filled.is_none()
            && !prose[i].is_empty()
            && let Some(s) = sanitize(&prose[i], &taken)
        {
            filled = Some((s, Tier::Prose));
        }
        if filled.is_none()
            && i == 0
            && let Some(noun) = gloss_derived_x1(&lens.definition)
            && let Some(s) = sanitize(&noun, &taken)
        {
            filled = Some((s, Tier::GlossDerived));
        }
        let (label, tier) = filled.unwrap_or_else(|| (generic_filler(i, &taken), Tier::Generic));
        places.push(label);
        tiers.push(tier);
    }
    let tier = tiers.iter().copied().max().unwrap_or(Tier::Generic);
    let one_line: String = lens.definition.replace(['\n', '\r'], " ");
    let mut definition_head: String = one_line.chars().take(72).collect();
    if one_line.chars().count() > 72 {
        definition_head.push('…');
    }
    Candidate {
        name: name.to_string(),
        gismu: lens.word.clone(),
        places,
        place_tiers: tiers,
        gloss: lens
            .gloss_keywords
            .first()
            .map(|g| g.word.clone())
            .unwrap_or_else(|| lens.word.clone()),
        tier,
        definition_head,
    }
}

fn emit_candidate(out: &mut String, e: &Candidate) {
    let guessed: Vec<String> = e
        .place_tiers
        .iter()
        .enumerate()
        .filter(|(_, t)| **t > Tier::Lensisku)
        .map(|(i, t)| format!("x{}:{}", i + 1, t.short()))
        .collect();
    if !guessed.is_empty() {
        let _ = writeln!(
            out,
            "    // TODO(corpus): guessed places [{}] — lensisku: {:?}",
            guessed.join(", "),
            e.definition_head
        );
    }
    let places: Vec<String> = e.places.iter().map(|p| format!("{p:?}")).collect();
    let _ = writeln!(
        out,
        "    PredicateEntry {{ name: {:?}, source_gismu: {:?}, swap: None, places: &[{}], gloss: {:?}, template: None, tier: {} }},",
        e.name,
        e.gismu,
        places.join(", "),
        e.gloss,
        e.tier.rust()
    );
}

fn regen(dict_path: &str, out_path: &str) {
    let export = load_export(dict_path);

    let mut new_entries = 0usize;
    let mut drift = 0usize;
    // (When splicing: the TODO_BASELINE const in predicates.rs keeps its
    // `#[allow(dead_code)]` — it is consumed by the ratchet test only.)
    let mut scratch = String::from(
        "// Candidate NEW entries from `nibli-lexigen regen` — review, refine, and\n\
         // splice into corpus/predicates.rs at the sorted position (the const\n\
         // guard rejects a wrong position). Raise TODO_BASELINE consciously.\n\n",
    );

    for (word, lens) in &export {
        match nibli_lexicon::by_provenance(word) {
            Some(entry) => {
                // Drift report only — regen never rewrites committed entries.
                let fresh_arity = nibli_lexicon::arity::definition_arity(&lens.definition);
                if fresh_arity != entry.places.len() {
                    drift += 1;
                    println!(
                        "drift: {word} ({}) — export arity {fresh_arity} vs corpus {}",
                        entry.name,
                        entry.places.len()
                    );
                }
                let fresh_gloss = lens.gloss_keywords.first().map(|g| g.word.as_str());
                if let Some(g) = fresh_gloss
                    && g != entry.gloss
                {
                    drift += 1;
                    println!(
                        "drift: {word} ({}) — export gloss {g:?} vs corpus {:?}",
                        entry.name, entry.gloss
                    );
                }
            }
            None => {
                new_entries += 1;
                let cand = lens
                    .gloss_keywords
                    .first()
                    .and_then(|g| sanitize(&g.word, &[]))
                    .filter(|c| {
                        nibli_lexicon::alias(c).is_none()
                            && !nibli_lexicon::reserved::is_reserved(c)
                    });
                match cand {
                    Some(alias_name) => {
                        emit_candidate(&mut scratch, &build_candidate(&alias_name, lens));
                    }
                    None => {
                        let _ = writeln!(
                            scratch,
                            "    // {word}: no usable name candidate (gloss collision/keyword) — needs a hand pick"
                        );
                    }
                }
            }
        }
    }

    if let Some(parent) = std::path::Path::new(out_path).parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(out_path, scratch).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
    println!("regen: {new_entries} new-entry candidate(s) -> {out_path}; {drift} drift finding(s)");
}
