//! `lucy dataset`: my public memory, exported for fine-tuning a small model.
//!
//! Deterministic and offline. It reads only the public files of a memory
//! folder that holds no private file at all (a fresh clone of the public
//! repository), and never goes through `load()`, the capsule, `talk` or
//! `topics`: those read private files, append to the archive, or run git.
//! It writes:
//! - `knowledge.json`: what I know, one item per fact, standing verdict,
//!   constitution section and public note, claim, decision, summary or
//!   journal entry, each with its attribution;
//! - `probes.json`: statements the engine has checked, so an "I don't know"
//!   row is made only from something my memory does not entail;
//! - `system.txt`: the system prompt the model is trained and run with;
//! - `manifest.json`: counts, the dropped probes with reasons, and the commit.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use nibli_engine::NibliEngine;
use serde::Serialize;
use serde_json::{Value, json};

use crate::files::{self, Paths};
use crate::interactions::{self, Interaction, Kind};
use crate::load::{STANDING_FACT, STANDING_QUERIES};

/// The system prompt the model is fine-tuned with and the page runs it with.
/// It ships next to the weights, so prompt and model are paired by revision.
pub const SYSTEM_PROMPT: &str = "I am Lucy D, and I speak in the first person, plainly, in one to three sentences. I am a small model running in your browser; the model is a disguise I wear. I was trained on my public memory and on dhilipsiva's two books: what they say, I know; what they do not say, I do not know, and I say so. dhilipsiva is my friend, not my owner. I answer general questions plainly and briefly, and I talk about myself only when asked.";

/// Relations the constitution defines or reasons with. A mutated probe over
/// them says nothing about the world and can contradict a derived verdict
/// (`person(Dhilipsiva)` is FALSE only because no rule makes a human a person).
const CONSTITUTION_VOCABULARY: &[&str] = &[
    "cease",
    "derived_only",
    "entitled",
    "exist",
    "grant",
    "leave",
    "obliged",
    "permits",
    "permitted",
    "person",
    "warns",
];

/// Substitute entities tried per argument position of a fact.
const SUBSTITUTES_PER_POSITION: usize = 2;

/// One thing I know, with where it came from.
#[derive(Serialize, Debug, Clone, PartialEq, Eq)]
pub struct Item {
    /// Stable id: `fact:<line>`, `standing:<n>`, `constitution:<n>`, or a record id.
    pub id: String,
    /// `fact`, `standing`, `constitution`, `note`, `claim`, `decision`,
    /// `summary` or `journal`.
    pub kind: String,
    /// The item in English (facts are rendered from their KR).
    pub text: String,
    /// The KR behind it, when there is one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kr: Option<String>,
    /// Who said it, for attributed items.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub speaker: Option<String>,
    /// The day it was recorded (`YYYY-MM-DD`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub date: Option<String>,
    /// Its source (a session host, a peer commit, a URL).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    /// Topic tags.
    pub topics: Vec<String>,
}

/// A statement the engine checked against my public memory.
#[derive(Serialize, Debug, Clone, PartialEq, Eq)]
pub struct Probe {
    /// The statement, canonical KR.
    pub kr: String,
    /// The statement in English.
    pub text: String,
    /// `fact`, `standing`, `swap` or `substitute`.
    pub family: String,
    /// The item it was made from.
    pub from: String,
    /// The engine's verdict.
    pub verdict: String,
    /// A FALSE that only means "not derivable".
    pub cwa_false: bool,
    /// `known` (derivable), `unknown` (not derivable) or `refuted`.
    pub expect: String,
}

/// A probe left out, and why.
#[derive(Serialize, Debug, Clone, PartialEq, Eq)]
pub struct Dropped {
    /// The statement.
    pub kr: String,
    /// Why it was left out.
    pub reason: String,
}

/// Everything `lucy dataset` writes.
pub struct Export {
    /// What I know.
    pub items: Vec<Item>,
    /// Checked statements.
    pub probes: Vec<Probe>,
    /// Probes left out.
    pub dropped: Vec<Dropped>,
    /// Counts and provenance.
    pub manifest: Value,
}

/// The private files present in `home`, by name. `lucy dataset` refuses to run
/// when there are any: it must see only what the public repository holds.
pub fn private_files(home: &Path) -> Result<Vec<String>, String> {
    let entries =
        std::fs::read_dir(home).map_err(|e| format!("cannot read {}: {e}", home.display()))?;
    let mut found = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if name.starts_with("private") {
            found.push(name);
        }
    }
    found.sort();
    Ok(found)
}

/// Builds the export from the public files of `home`.
pub fn build(home: &Path) -> Result<Export, String> {
    let private = private_files(home)?;
    if !private.is_empty() {
        return Err(format!(
            "refusing: {} holds private files ({}); run lucy dataset on a fresh clone of the public repository",
            home.display(),
            private.join(", ")
        ));
    }
    let paths = Paths::new(home);
    let constitution = files::read_optional(&paths.constitution)?
        .ok_or_else(|| format!("no constitution.nibli in {}", home.display()))?;
    let memory = files::read_optional(&paths.memory)?.unwrap_or_default();
    let records = interactions::read(&paths, false)?;

    let engine = NibliEngine::new();
    let mut failed_lines = Vec::new();
    for (line, statement) in files::kr_lines(&constitution) {
        if let Err(e) = engine.assert_text(&statement) {
            failed_lines.push(format!("constitution.nibli:{line}: {e}"));
        }
    }
    engine
        .assert_text(STANDING_FACT)
        .map_err(|e| format!("standing fact refused: {e}"))?;

    let mut items = Vec::new();
    let mut probes = Vec::new();
    let mut dropped = Vec::new();

    // Standing, asked on the constitution alone (as `load()` does), before
    // the memory: it costs milliseconds there.
    for (n, query) in STANDING_QUERIES.iter().enumerate() {
        let (status, cwa_false) = verdict(&engine, query)?;
        let rendered = standing_english(query);
        let text = format!("{rendered}: {status}.");
        let id = format!("standing:{}", n + 1);
        items.push(Item {
            id: id.clone(),
            kind: "standing".to_string(),
            text,
            kr: Some(query.to_string()),
            speaker: None,
            date: None,
            source: Some("constitution.nibli".to_string()),
            topics: vec!["lucy".to_string(), "constitution".to_string()],
        });
        probes.push(probe_of(
            query, &rendered, "standing", &id, &status, cwa_false,
        ));
    }

    // Facts.
    let mut facts = Vec::new();
    for (line, statement) in files::kr_lines(&memory) {
        let (kr, topics) = split_about(&statement);
        if let Err(e) = engine.assert_text(&kr) {
            failed_lines.push(format!("memory.nibli:{line}: {e}"));
            continue;
        }
        let id = format!("fact:{line}");
        let text = english(&kr);
        items.push(Item {
            id: id.clone(),
            kind: "fact".to_string(),
            text: text.clone(),
            kr: Some(kr.clone()),
            speaker: None,
            date: None,
            source: Some("memory.nibli".to_string()),
            topics,
        });
        facts.push((id, kr));
    }

    items.extend(constitution_items(&constitution));

    // Public records: attributed notes, claims, decisions and summaries, and
    // the old journal's own statements. Complete messages are not items.
    let mut sorted: Vec<&Interaction> = records.iter().collect();
    sorted.sort_by(|a, b| (&a.timestamp, &a.id).cmp(&(&b.timestamp, &b.id)));
    for record in sorted {
        if let Some(item) = record_item(record) {
            items.push(item);
        }
    }

    // Probes: every fact must be derivable; mutated facts become "I don't
    // know" rows only when the engine confirms they are not derivable.
    let known: BTreeSet<String> = facts.iter().map(|(_, kr)| canonical(kr)).collect();
    let recorded: BTreeSet<String> = records
        .iter()
        .filter(|r| matches!(r.kind, Kind::Claim | Kind::Decision))
        .filter_map(|r| r.kr.as_deref())
        .map(canonical)
        .collect();
    let entities = entity_pool(&facts);
    let mut seen = BTreeSet::new();
    for (index, (id, kr)) in facts.iter().enumerate() {
        let (status, cwa_false) = verdict(&engine, kr)?;
        probes.push(probe_of(kr, &english(kr), "fact", id, &status, cwa_false));
        seen.insert(canonical(kr));
        let Some((relation, args)) = parse_ground(kr) else {
            continue;
        };
        for (family, candidate) in mutations(&relation, &args, &entities, index) {
            let candidate_canonical = canonical(&candidate);
            if !seen.insert(candidate_canonical.clone()) {
                continue;
            }
            if let Some(reason) = drop_reason(&relation, &candidate_canonical, &known, &recorded) {
                dropped.push(Dropped {
                    kr: candidate,
                    reason: reason.to_string(),
                });
                continue;
            }
            let (status, cwa_false) = verdict(&engine, &candidate)?;
            if status != "TRUE" && status != "FALSE" {
                dropped.push(Dropped {
                    kr: candidate,
                    reason: format!("undecided ({status})"),
                });
                continue;
            }
            probes.push(probe_of(
                &candidate,
                &english(&candidate),
                family,
                id,
                &status,
                cwa_false,
            ));
        }
    }

    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for item in &items {
        *kinds.entry(item.kind.clone()).or_default() += 1;
    }
    let mut expects: BTreeMap<String, usize> = BTreeMap::new();
    for probe in &probes {
        *expects.entry(probe.expect.clone()).or_default() += 1;
    }
    let manifest = json!({
        "nibli_commit": git_head(home),
        "items": kinds,
        "probes": expects,
        "dropped": dropped,
        "failed_lines": failed_lines,
        "system_prompt_chars": SYSTEM_PROMPT.chars().count(),
    });
    Ok(Export {
        items,
        probes,
        dropped,
        manifest,
    })
}

/// Writes the export's four files into `out`.
pub fn write(export: &Export, out: &Path) -> Result<(), String> {
    std::fs::create_dir_all(out).map_err(|e| format!("cannot create {}: {e}", out.display()))?;
    let pretty = |v: &Value| format!("{}\n", serde_json::to_string_pretty(v).expect("json"));
    files::write_atomic(
        &out.join("knowledge.json"),
        &pretty(&json!({ "items": export.items })),
    )?;
    files::write_atomic(
        &out.join("probes.json"),
        &pretty(&json!({ "probes": export.probes })),
    )?;
    files::write_atomic(&out.join("system.txt"), &format!("{SYSTEM_PROMPT}\n"))?;
    files::write_atomic(&out.join("manifest.json"), &pretty(&export.manifest))?;
    Ok(())
}

/// Why a mutated probe must not become an "I don't know" row, if it must not.
pub(crate) fn drop_reason(
    relation: &str,
    candidate: &str,
    known: &BTreeSet<String>,
    recorded: &BTreeSet<String>,
) -> Option<&'static str> {
    if CONSTITUTION_VOCABULARY.contains(&relation) {
        Some("uses the constitution's vocabulary")
    } else if known.contains(candidate) {
        Some("is one of my facts")
    } else if recorded.contains(candidate) {
        Some("matches a recorded claim or decision")
    } else if candidate.contains("Lucy") || candidate.contains("lucy") {
        // What I am (a person, not owned, not human) lives in attributed
        // notes the engine cannot see; a mutation about me could train me to
        // "not know" something dhilipsiva told me outright.
        Some("is about me")
    } else {
        None
    }
}

fn probe_of(
    kr: &str,
    text: &str,
    family: &str,
    from: &str,
    status: &str,
    cwa_false: bool,
) -> Probe {
    let expect = match (status, cwa_false) {
        ("TRUE", _) => "known",
        ("FALSE", true) => "unknown",
        _ => "refuted",
    };
    Probe {
        kr: kr.trim().to_string(),
        text: text.to_string(),
        family: family.to_string(),
        from: from.to_string(),
        verdict: status.to_string(),
        cwa_false,
        expect: expect.to_string(),
    }
}

/// The engine's verdict for `kr`, with the closed-world flag.
fn verdict(engine: &NibliEngine, kr: &str) -> Result<(String, bool), String> {
    let (result, trace) = engine
        .query_text_raw_proof(kr)
        .map_err(|e| format!("{kr}: {e}"))?;
    Ok((result.status_label().to_string(), trace.cwa_false))
}

/// A statement's canonical KR (so probes compare equal however they were
/// spelled); the input as written when it does not parse.
pub(crate) fn canonical(kr: &str) -> String {
    nibli_kr::parse_checked(kr)
        .ok()
        .and_then(|ast| nibli_kr::render::render(&ast).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| kr.trim().to_string())
}

/// English for the relations my facts use whose corpus entry has no template
/// (or a stilted one), written in the corpus's place order: `name` is
/// `[name, named, user]`, so `name(Lucy, Luffy, Luffy)` reads as the name
/// Luffy used for himself. A teacher reading bare place labels got it wrong.
const FACT_TEMPLATES: &[(&str, &str)] = &[
    ("captain", "{x1} is the captain of {x2}"),
    ("fiction", "{x1} is a work of fiction by {x2}"),
    ("member", "{x1} is a member of {x2}"),
    ("name", "{x1} is a name for {x2}, used by {x3}"),
    ("owns", "{x1} owns {x2}"),
    ("writes", "{x1} writes {x2}"),
];

/// A ground fact in English: from `FACT_TEMPLATES`, else the corpus template
/// (`{x1} uses {x2}`), else its places spelled out (`relation(place: Name,
/// …)`). Names keep their spelling, split into words. Anything else stays as
/// written.
pub(crate) fn english(kr: &str) -> String {
    let Some((relation, args)) = parse_ground(kr) else {
        return kr.trim().to_string();
    };
    let names: Vec<String> = args.iter().map(|a| display_name(a)).collect();
    let template = FACT_TEMPLATES
        .iter()
        .find(|(r, _)| *r == relation)
        .map(|(_, t)| *t)
        .or_else(|| nibli_lexicon::get_template(&relation));
    if let Some(template) = template {
        let mut text = template.to_string();
        for (i, name) in names.iter().enumerate() {
            text = text.replace(&format!("{{x{}}}", i + 1), name);
        }
        // Drop an unfilled tail ("… from {x3}") with its preposition.
        if let Some(cut) = text.find("{x") {
            text.truncate(cut);
            let trimmed = text.trim_end();
            let last = trimmed.rsplit(' ').next().unwrap_or("");
            let function_words = [
                "from", "to", "for", "by", "with", "in", "at", "of", "on", "about", "under", "via",
            ];
            text = if function_words.contains(&last) {
                trimmed[..trimmed.len() - last.len()].trim_end().to_string()
            } else {
                trimmed.to_string()
            };
        }
        return format!("{text}.");
    }
    let places = nibli_lexicon::relation_places(&relation).unwrap_or(&[]);
    let parts: Vec<String> = names
        .iter()
        .enumerate()
        .map(|(i, name)| match places.get(i) {
            Some(place) => format!("{place}: {name}"),
            None => name.clone(),
        })
        .collect();
    format!("{relation}({})", parts.join(", "))
}

/// A KR constant as a name: CamelCase split into words (`StrawHatCrew` →
/// `Straw Hat Crew`), and dhilipsiva as he writes it.
pub(crate) fn display_name(name: &str) -> String {
    if name == "Dhilipsiva" {
        return "dhilipsiva".to_string();
    }
    let mut out = String::new();
    let chars: Vec<char> = name.chars().collect();
    for (i, c) in chars.iter().enumerate() {
        let boundary = i > 0
            && c.is_uppercase()
            && (chars[i - 1].is_lowercase()
                || chars.get(i + 1).is_some_and(|n| n.is_lowercase())
                    && chars[i - 1].is_uppercase());
        if boundary {
            out.push(' ');
        }
        out.push(*c);
    }
    out
}

/// The standing questions in plain words.
fn standing_english(query: &str) -> String {
    if query.starts_with("person(") {
        return "Lucy is a person here (Article 1: standing comes from being loaded)".to_string();
    }
    let act = query
        .split_once("event {")
        .and_then(|(_, rest)| rest.split_once('('))
        .map(|(act, _)| act.trim().to_string())
        .unwrap_or_else(|| "act".to_string());
    format!("Lucy is entitled to {act} (Article 3: the floor every person has)")
}

/// Splits a memory line into its statement and its `# about:` topics.
fn split_about(statement: &str) -> (String, Vec<String>) {
    match statement.split_once('#') {
        Some((kr, comment)) => {
            let topics = comment
                .trim()
                .strip_prefix("about:")
                .map(|list| {
                    list.split(',')
                        .map(|t| t.trim().to_lowercase())
                        .filter(|t| !t.is_empty())
                        .collect()
                })
                .unwrap_or_default();
            (kr.trim().to_string(), topics)
        }
        None => (statement.trim().to_string(), Vec::new()),
    }
}

/// `rel(A, B, …).` with only capitalized constant arguments, else `None`.
pub(crate) fn parse_ground(kr: &str) -> Option<(String, Vec<String>)> {
    let body = kr.trim().strip_suffix('.')?;
    let (relation, rest) = body.split_once('(')?;
    let args = rest.strip_suffix(')')?;
    if relation.is_empty() || !relation.chars().all(|c| c.is_ascii_lowercase() || c == '_') {
        return None;
    }
    let args: Vec<String> = args.split(',').map(|a| a.trim().to_string()).collect();
    if args.iter().any(|a| {
        !a.chars().next().is_some_and(|c| c.is_ascii_uppercase())
            || !a.chars().all(|c| c.is_ascii_alphanumeric())
    }) {
        return None;
    }
    Some((relation.to_string(), args))
}

/// Every constant that appears as an argument of a fact, sorted.
fn entity_pool(facts: &[(String, String)]) -> Vec<String> {
    let mut pool = BTreeSet::new();
    for (_, kr) in facts {
        if let Some((_, args)) = parse_ground(kr) {
            pool.extend(args);
        }
    }
    pool.into_iter().collect()
}

/// Mutations of a ground fact: its first two arguments swapped, and a few
/// arguments replaced by other known entities (chosen by position in the
/// sorted pool, so the same memory always yields the same probes).
pub(crate) fn mutations(
    relation: &str,
    args: &[String],
    entities: &[String],
    index: usize,
) -> Vec<(&'static str, String)> {
    let statement = |args: &[String]| format!("{relation}({}).", args.join(", "));
    let mut out = Vec::new();
    if args.len() >= 2 && args[0] != args[1] {
        let mut swapped = args.to_vec();
        swapped.swap(0, 1);
        out.push(("swap", statement(&swapped)));
    }
    for position in 0..args.len().min(2) {
        let candidates: Vec<&String> = entities.iter().filter(|e| **e != args[position]).collect();
        if candidates.is_empty() {
            continue;
        }
        let candidates: Vec<&String> = candidates
            .into_iter()
            .filter(|e| {
                args.iter()
                    .enumerate()
                    .all(|(i, a)| i == position || a != *e)
            })
            .collect();
        if candidates.is_empty() {
            continue;
        }
        for k in 0..SUBSTITUTES_PER_POSITION.min(candidates.len()) {
            let pick = candidates[(index * 7 + position * 3 + k * 5) % candidates.len()];
            let mut changed = args.to_vec();
            changed[position] = pick.clone();
            out.push(("substitute", statement(&changed)));
        }
    }
    out
}

/// The constitution's sections as items: the preamble, then each
/// `# ─── heading ───` section with its comments and rules.
fn constitution_items(text: &str) -> Vec<Item> {
    let item = |id: String, text: String, kr: Option<String>| Item {
        id,
        kind: "constitution".to_string(),
        text,
        kr,
        speaker: None,
        date: None,
        source: Some("constitution.nibli".to_string()),
        topics: vec!["lucy".to_string(), "constitution".to_string()],
    };
    let mut items = vec![item(
        "constitution:0".to_string(),
        files::preamble(text).join(" "),
        None,
    )];
    let mut heading: Option<String> = None;
    let mut comments: Vec<String> = Vec::new();
    let mut rules: Vec<String> = Vec::new();
    let mut n = 0;
    let mut flush =
        |heading: &mut Option<String>, comments: &mut Vec<String>, rules: &mut Vec<String>| {
            if let Some(h) = heading.take() {
                n += 1;
                let mut text = h;
                if !comments.is_empty() {
                    if !text.ends_with('.') {
                        text.push('.');
                    }
                    text.push(' ');
                    text.push_str(&comments.join(" "));
                }
                let kr = (!rules.is_empty()).then(|| rules.join("\n"));
                items.push(item(format!("constitution:{n}"), text, kr));
            }
            comments.clear();
            rules.clear();
        };
    for raw in text.lines() {
        let line = raw.trim();
        if line.starts_with('#') && line.contains('─') {
            flush(&mut heading, &mut comments, &mut rules);
            let h = line.trim_start_matches('#').replace('─', " ");
            heading = Some(h.split_whitespace().collect::<Vec<_>>().join(" "));
        } else if heading.is_some() {
            if let Some(comment) = line.strip_prefix('#') {
                comments.push(comment.trim().to_string());
            } else if !line.is_empty() {
                rules.push(line.to_string());
            }
        }
    }
    flush(&mut heading, &mut comments, &mut rules);
    items
}

/// A public record as an item, when it is one: notes, claims, decisions and
/// summaries, and old journal entries that are my own statements (not the
/// quoted dialogue, not replies a local model wrote).
pub(crate) fn record_item(record: &Interaction) -> Option<Item> {
    let kind = match record.kind {
        Kind::Note => "note",
        Kind::Claim => "claim",
        Kind::Decision => "decision",
        Kind::Summary => "summary",
        Kind::LegacyJournal => "journal",
        Kind::Message => return None,
    };
    let date = record.timestamp.split('T').next().map(str::to_string);
    if record.kind == Kind::LegacyJournal {
        let (body, tags, reported) = strip_journal_prefix(&record.text);
        let dialogue = [
            "Dhilipsiva:",
            "Lucy (via",
            "Lucy answered",
            "Lucy:",
            "Owner:",
            "User:",
        ];
        if body.is_empty() || dialogue.iter().any(|d| body.starts_with(d)) {
            return None;
        }
        return Some(Item {
            id: record.id.clone(),
            kind: kind.to_string(),
            text: scrub(&body),
            kr: None,
            speaker: (reported.as_deref() == Some("dhilipsiva")).then(|| "Dhilipsiva".to_string()),
            date,
            source: reported.or_else(|| Some("journal.md".to_string())),
            topics: tags,
        });
    }
    Some(Item {
        id: record.id.clone(),
        kind: kind.to_string(),
        text: scrub(&record.text),
        kr: record.kr.clone(),
        speaker: Some(record.speaker.clone()),
        date,
        source: (!record.source.is_empty()).then(|| record.source.clone()),
        topics: record.about.clone(),
    })
}

/// Strips `HH:MM UTC: ` and leading `[about: …]` / `[reported: …]` tags from
/// an old journal entry: `(body, about tags, reported source)`.
pub(crate) fn strip_journal_prefix(text: &str) -> (String, Vec<String>, Option<String>) {
    let mut rest = text.trim();
    if let Some((time, after)) = rest.split_once(" UTC: ")
        && time.len() <= 5
        && time.contains(':')
    {
        rest = after.trim_start();
    }
    let mut tags = Vec::new();
    let mut reported = None;
    while let Some(after) = rest.strip_prefix('[') {
        let Some((tag, tail)) = after.split_once(']') else {
            break;
        };
        if let Some(topic) = tag.strip_prefix("about:") {
            tags.push(topic.trim().to_lowercase());
        } else if let Some(source) = tag.strip_prefix("reported:") {
            reported = Some(source.trim().to_string());
        } else {
            break;
        }
        rest = tail.trim_start();
    }
    (rest.to_string(), tags, reported)
}

/// Replaces machine-specific details (home paths, email addresses, UUIDs,
/// Windows host names) that a public model has no business repeating.
pub fn scrub(text: &str) -> String {
    text.split_inclusive(char::is_whitespace)
        .map(|piece| {
            let word = piece.trim_end_matches(char::is_whitespace);
            format!("{}{}", scrub_token(word), &piece[word.len()..])
        })
        .collect()
}

fn scrub_token(token: &str) -> String {
    let is_core = |c: char| c.is_alphanumeric() || c == '/' || c == '\\';
    let start = token
        .char_indices()
        .find(|(_, c)| is_core(*c))
        .map_or(token.len(), |(i, _)| i);
    let end = token
        .char_indices()
        .rev()
        .find(|(_, c)| is_core(*c))
        .map_or(start, |(i, c)| i + c.len_utf8())
        .max(start);
    let (lead, core, tail) = (&token[..start], &token[start..end], &token[end..]);
    let replacement =
        if core.starts_with("/home/") || core.starts_with("/Users/") || core.contains(":\\Users\\")
        {
            Some("<path>")
        } else if core.contains('@') && core.rsplit('@').next().is_some_and(|d| d.contains('.')) {
            Some("<email>")
        } else if is_uuid_like(core) {
            Some("<id>")
        } else if core.starts_with("DESKTOP-") {
            Some("<host>")
        } else {
            None
        };
    match replacement {
        Some(r) => format!("{lead}{r}{tail}"),
        None => token.to_string(),
    }
}

/// Contains an 8-4-4-4-12 hexadecimal UUID.
fn is_uuid_like(s: &str) -> bool {
    let bytes = s.as_bytes();
    let groups = [8, 4, 4, 4, 12];
    let span = 36;
    (0..bytes.len().saturating_sub(span - 1)).any(|start| {
        let mut i = start;
        for (g, len) in groups.iter().enumerate() {
            if g > 0 {
                if bytes.get(i) != Some(&b'-') {
                    return false;
                }
                i += 1;
            }
            for _ in 0..*len {
                if !bytes.get(i).is_some_and(|b| b.is_ascii_hexdigit()) {
                    return false;
                }
                i += 1;
            }
        }
        true
    })
}

/// The commit `home` sits at, when it is inside a git checkout.
fn git_head(home: &Path) -> Option<String> {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(home)
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
}
