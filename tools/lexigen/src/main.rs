//! nibli-lexigen — the corpus generation/refresh tool.
//!
//! `bootstrap` seeds `nibli-lexicon/src/corpus/predicates.rs` from a lensisku
//! export + the CURRENTLY SHIPPED alias/dictionary artifacts (so the seeded
//! corpus agrees with the build.rs output by construction — the bridge
//! cross-check test then pins it). `regen` NEVER rewrites existing entries:
//! it emits candidate entries for export words ABSENT from the corpus to a
//! scratch file and prints a drift report — refinement stays human, in-tree.
//!
//! Both subcommands need the FULL-mode build of nibli-lexicon (run
//! `just fetch-dict` first; the tool bails on a fallback artifact).
//!
//! Label chain per place (zero positional survivors): shipped label →
//! lensisku `place_keywords[i]` → prose heuristic → GlossDerived (x1 of an
//! "is a/the <noun>" definition) → Generic filler (`subject`/`object`/
//! `place{N}`). Every candidate is sanitized (ident shape, reserved words,
//! `xN` lookalikes, in-entry duplicates) and falls through on failure —
//! totality by construction. Entries whose worst tier is below Lensisku get a
//! greppable `TODO(corpus):` marker (the refinement worklist).

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
    Curated,
    Lensisku,
    Prose,
    GlossDerived,
    Generic,
}

impl Tier {
    fn rust(self) -> &'static str {
        match self {
            Tier::Curated => "CorpusTier::Curated",
            Tier::Lensisku => "CorpusTier::Lensisku",
            Tier::Prose => "CorpusTier::Prose",
            Tier::GlossDerived => "CorpusTier::GlossDerived",
            Tier::Generic => "CorpusTier::Generic",
        }
    }
    fn short(self) -> &'static str {
        match self {
            Tier::Curated => "curated",
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
        "bootstrap" => {
            let out = flag(&args, "--out")
                .unwrap_or_else(|| "nibli-lexicon/src/corpus/predicates.rs".into());
            bootstrap(&dict, &out);
        }
        "regen" => {
            let out =
                flag(&args, "--out").unwrap_or_else(|| "target/lexigen/new_entries.rs".into());
            regen(&dict, &out);
        }
        _ => {
            eprintln!(
                "usage: nibli-lexigen <bootstrap|regen> [--dict dictionary-en.json] [--out PATH]"
            );
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

fn require_full_mode() {
    assert!(
        nibli_lexicon::ALIASES.len() >= 1000,
        "lexigen needs the FULL-mode nibli-lexicon build (run `just fetch-dict`, then rebuild)"
    );
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

struct BuiltEntry {
    name: String,
    gismu: String,
    swap_rust: String,
    places: Vec<String>,
    place_tiers: Vec<Tier>,
    gloss: String,
    template: Option<String>,
    tier: Tier,
    definition_head: String,
}

fn build_entry(
    name: &str,
    ae: &nibli_lexicon::AliasEntry,
    export: &BTreeMap<String, LensiskuEntry>,
) -> BuiltEntry {
    let arity = ae.arity as usize;
    let dict = nibli_lexicon::DICTIONARY
        .get(ae.gismu)
        .unwrap_or_else(|| panic!("{name}: gismu {:?} missing from DICTIONARY", ae.gismu));
    let lens = export.get(ae.gismu);
    let existing_tier = match ae.label_tier {
        nibli_lexicon::LabelTier::Curated => Tier::Curated,
        nibli_lexicon::LabelTier::Lensisku => Tier::Lensisku,
        nibli_lexicon::LabelTier::Prose => Tier::Prose,
        nibli_lexicon::LabelTier::Positional => Tier::Generic, // unreachable for non-empty
    };

    let prose = lens.map(|l| nibli_lexicon::label::prose_labels(&l.definition, ae.arity));
    // TWO-PASS fill: shipped labels are fixed (the bridge cross-check pins
    // them), so reserve them ALL first — a new fill must not duplicate a
    // shipped label at ANY index, earlier or later.
    let mut places: Vec<String> = (0..arity).map(|i| ae.place_labels[i].to_string()).collect();
    let mut tiers: Vec<Tier> = places
        .iter()
        .map(|p| {
            if p.is_empty() {
                Tier::Generic
            } else {
                existing_tier
            }
        })
        .collect();
    for i in 0..arity {
        if !places[i].is_empty() {
            continue;
        }
        let taken: Vec<String> = places.iter().filter(|p| !p.is_empty()).cloned().collect();
        let mut filled: Option<(String, Tier)> = None;
        if let Some(l) = lens {
            if let Some(kw) = l.place_keywords.get(i)
                && let Some(s) = sanitize(&kw.word, &taken)
            {
                filled = Some((s, Tier::Lensisku));
            }
            if filled.is_none()
                && let Some(p) = &prose
                && !p[i].is_empty()
                && let Some(s) = sanitize(&p[i], &taken)
            {
                filled = Some((s, Tier::Prose));
            }
            if filled.is_none()
                && i == 0
                && let Some(noun) = gloss_derived_x1(&l.definition)
                && let Some(s) = sanitize(&noun, &taken)
            {
                filled = Some((s, Tier::GlossDerived));
            }
        }
        let (label, tier) = filled.unwrap_or_else(|| (generic_filler(i, &taken), Tier::Generic));
        places[i] = label;
        tiers[i] = tier;
    }

    let tier = tiers.iter().copied().max().unwrap_or(Tier::Curated);
    let swap_rust = match ae.swap {
        None => "None".to_string(),
        Some(k) => {
            let base = nibli_lexicon::canonical_alias(ae.gismu)
                .unwrap_or_else(|| panic!("{name}: converted alias without canonical base"));
            format!("Some(Swap {{ with: {k}, base: {base:?} }})")
        }
    };
    let definition_head = lens
        .map(|l| {
            let one_line: String = l.definition.replace(['\n', '\r'], " ");
            let mut head: String = one_line.chars().take(72).collect();
            if one_line.chars().count() > 72 {
                head.push('…');
            }
            head
        })
        .unwrap_or_default();

    BuiltEntry {
        name: name.to_string(),
        gismu: ae.gismu.to_string(),
        swap_rust,
        places,
        place_tiers: tiers,
        gloss: dict.gloss.to_string(),
        template: (!dict.template.is_empty()).then(|| dict.template.to_string()),
        tier,
        definition_head,
    }
}

fn emit_entry(out: &mut String, e: &BuiltEntry) {
    if e.tier > Tier::Lensisku {
        let guessed: Vec<String> = e
            .place_tiers
            .iter()
            .enumerate()
            .filter(|(_, t)| **t > Tier::Lensisku)
            .map(|(i, t)| format!("x{}:{}", i + 1, t.short()))
            .collect();
        let _ = writeln!(
            out,
            "    // TODO(corpus): guessed places [{}] — lensisku: {:?}",
            guessed.join(", "),
            e.definition_head
        );
    }
    let places: Vec<String> = e.places.iter().map(|p| format!("{p:?}")).collect();
    let template = match &e.template {
        None => "None".to_string(),
        Some(t) => format!("Some({t:?})"),
    };
    let _ = writeln!(
        out,
        "    PredicateEntry {{ name: {:?}, source_gismu: {:?}, swap: {}, places: &[{}], gloss: {:?}, template: {}, tier: {} }},",
        e.name,
        e.gismu,
        e.swap_rust,
        places.join(", "),
        e.gloss,
        template,
        e.tier.rust()
    );
}

fn bootstrap(dict_path: &str, out_path: &str) {
    require_full_mode();
    let export = load_export(dict_path);

    let mut names: Vec<&str> = nibli_lexicon::ALIASES.entries().map(|(n, _)| *n).collect();
    names.sort_unstable();

    let mut body = String::new();
    let mut todo_count = 0usize;
    for name in &names {
        let ae = nibli_lexicon::alias(name).unwrap();
        let built = build_entry(name, ae, &export);
        if built.tier > Tier::Lensisku {
            todo_count += 1;
        }
        emit_entry(&mut body, &built);
    }

    let mut out = String::new();
    let _ = writeln!(
        out,
        "//! GENERATED by `nibli-lexigen bootstrap` from a lensisku export — then\n\
         //! HAND-REFINED IN PLACE (the committed file is the source of truth; regen\n\
         //! never rewrites an existing entry). Refinement protocol: fix the labels,\n\
         //! set `tier: CorpusTier::Curated`, delete the marker comment above the\n\
         //! entry, and lower `TODO_BASELINE` in the same diff.\n\
         //!\n\
         //! Sorted by `name`; the const validation in `corpus.rs` fails the compile\n\
         //! on any shape violation.\n\
         \n\
         use super::{{CorpusTier, PredicateEntry, Swap}};\n\
         \n\
         /// The `TODO(corpus)` marker count — the label-quality ratchet.\n\
         pub(crate) const TODO_BASELINE: usize = {todo_count};\n\
         \n\
         pub(crate) static PREDICATES: &[PredicateEntry] = &["
    );
    out.push_str(&body);
    out.push_str("];\n");

    if let Some(parent) = std::path::Path::new(out_path).parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(out_path, out).unwrap_or_else(|e| panic!("write {out_path}: {e}"));
    println!(
        "bootstrap: {} entries ({} TODO-marked) -> {out_path}",
        names.len(),
        todo_count
    );
}

fn regen(dict_path: &str, out_path: &str) {
    require_full_mode();
    let export = load_export(dict_path);

    // Provenance index over the committed corpus.
    let by_gismu: BTreeMap<&str, &nibli_lexicon::corpus::PredicateEntry> =
        nibli_lexicon::corpus::corpus_entries()
            .filter(|e| e.swap.is_none())
            .map(|e| (e.source_gismu, e))
            .collect();

    let mut new_entries = 0usize;
    let mut drift = 0usize;
    let mut scratch = String::from(
        "// Candidate NEW entries from `nibli-lexigen regen` — review, refine, and\n\
         // splice into corpus/predicates.rs at the sorted position (the const\n\
         // guard rejects a wrong position). Raise TODO_BASELINE consciously.\n\n",
    );

    for (word, lens) in &export {
        match by_gismu.get(word.as_str()) {
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
                    .filter(|c| nibli_lexicon::corpus::corpus_predicate(c).is_none());
                match cand {
                    Some(alias) => {
                        let ae = nibli_lexicon::AliasEntry {
                            gismu: Box::leak(word.clone().into_boxed_str()),
                            swap: None,
                            arity: nibli_lexicon::arity::definition_arity(&lens.definition)
                                .clamp(1, 5) as u8,
                            place_labels: ["", "", "", "", ""],
                            label_tier: nibli_lexicon::LabelTier::Positional,
                        };
                        let built = build_entry(&alias, &ae, &export);
                        emit_entry(&mut scratch, &built);
                    }
                    None => {
                        let _ = writeln!(
                            scratch,
                            "    // {word}: no usable alias candidate (gloss collision/keyword) — needs a hand pick"
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
