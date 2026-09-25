//! Conversation records stored as ordinary nibli KR, with exact text in a
//! JSON string (KR strings cannot contain raw newlines). The accompanying
//! facts expose attribution, topics, time and session to any nibli reader.
//! Extracted claims remain inside opaque `fact { ... }` abstractions.

use std::fs::{File, OpenOptions};
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

use nibli_engine::NibliEngine;
use nibli_types::ast::{Argument, Predicate, Sentence};
use serde::{Deserialize, Serialize};

use crate::env::Env;
use crate::files::{self, JournalEntry, Paths};

/// An interaction's epistemic status, independent of who recorded it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    #[default]
    Message,
    Note,
    Summary,
    LegacyJournal,
    Claim,
    Decision,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Self::Message => "Message",
            Self::Note => "Note",
            Self::Summary => "Summary",
            Self::LegacyJournal => "LegacyJournal",
            Self::Claim => "Claim",
            Self::Decision => "Decision",
        }
    }
}

/// One complete message, legacy entry, or attributed extraction.
/// Empty ids and timestamps are assigned at recording time. A supplied id
/// makes retries idempotent; reusing it with different content is an error.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct Interaction {
    pub id: String,
    pub speaker: String,
    pub text: String,
    pub kind: Kind,
    pub timestamp: String,
    pub host: String,
    pub source: String,
    pub session: String,
    pub channel: String,
    pub about: Vec<String>,
    pub private: bool,
    /// Id of the message from which this claim or decision was extracted.
    pub from: Option<String>,
    /// Interpreted KR, always quoted when asserted into the engine.
    pub kr: Option<String>,
}

/// A printable KR constant. Metadata is single-line; arbitrary message
/// bytes first pass through JSON, whose control characters are escaped.
fn quoted(value: &str) -> Result<String, String> {
    if value.chars().any(char::is_control) {
        return Err("interaction metadata must not contain control characters".to_string());
    }
    Ok(format!(
        "\"{}\"",
        value.replace('\\', "\\\\").replace('"', "\\\"")
    ))
}

/// All facts for a record, also the canonical representation checked on read.
pub fn facts(entry: &Interaction) -> Result<String, String> {
    if entry.id.is_empty() || entry.speaker.is_empty() || entry.text.is_empty() {
        return Err("interaction needs a nonempty id, speaker and text".to_string());
    }
    let payload = serde_json::to_string(entry).map_err(|e| e.to_string())?;
    let id = quoted(&entry.id)?;
    let speaker = quoted(&entry.speaker)?;
    let mut out = format!(
        "record({id}, {}, {}, Json).\n",
        quoted(&payload)?,
        entry.kind.name()
    );
    out.push_str(&format!(
        "message({id}, {}, Conversation, {speaker}).\n",
        quoted(entry.kind.name())?
    ));
    for topic in &entry.about {
        out.push_str(&format!(
            "message({id}, {}, Conversation, {speaker}).\n",
            quoted(topic)?
        ));
    }
    out.push_str(&format!(
        "date({}, {id}, {}, Utc).\nsource({}, {id}).\n",
        quoted(&entry.timestamp)?,
        quoted(&entry.host)?,
        quoted(&entry.source)?
    ));
    if !entry.session.is_empty() {
        out.push_str(&format!("member({id}, {}).\n", quoted(&entry.session)?));
    }
    if let Some(from) = &entry.from {
        out.push_str(&format!("source({}, {id}).\n", quoted(from)?));
    }
    if let Some(kr) = &entry.kr {
        if !matches!(entry.kind, Kind::Claim | Kind::Decision) || entry.from.is_none() {
            return Err("interpreted KR needs claim/decision kind and a source message".into());
        }
        let ast = nibli_kr::parse_checked(kr).map_err(|e| e.to_string())?;
        if ast.roots.len() != 1 {
            return Err("an extraction must contain exactly one KR statement".into());
        }
        // Rendering discards comments and guarantees that quotes/braces in
        // the input cannot escape the abstraction that attributes the claim.
        let canonical = nibli_kr::render::render(&ast).map_err(|e| e.to_string())?;
        let body = canonical
            .trim()
            .strip_suffix('.')
            .unwrap_or(canonical.trim());
        out.push_str(&format!(
            "expresses({speaker}, fact {{ {body} }}, Conversation, {id}).\n"
        ));
    } else if matches!(entry.kind, Kind::Claim | Kind::Decision) {
        return Err("a claim or decision needs interpreted KR".into());
    }
    Ok(out)
}

fn render(entries: &[Interaction]) -> Result<String, String> {
    let mut out = String::from(
        "# Lucy conversation KB v1\n\
         # record(id, JSON payload, kind, Json); following facts index that record.\n\
         # Message text is quoted data. Attributed claims do not assert their contents.\n\
         # Use lucy record / claim; lucy transcript returns exact decoded text.\n",
    );
    for entry in entries {
        out.push_str(&facts(entry)?);
    }
    Ok(out)
}

/// Decode using the actual KR parser; never parse quotes or escapes by regex.
/// Metadata must agree with the payload, so an edited index cannot tell the
/// engine a different story from the transcript shown to a reader.
fn decode(text: &str, private: bool) -> Result<Vec<Interaction>, String> {
    let ast = nibli_kr::parse_checked(text).map_err(|e| e.to_string())?;
    let mut entries = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for root in &ast.roots {
        let Sentence::Simple(proposition) = &ast.sentences[*root as usize] else {
            continue;
        };
        let Predicate::Root(relation) = &ast.predicates[proposition.relation as usize] else {
            continue;
        };
        if relation != "record" {
            continue;
        }
        let Some(payload) = proposition.terms.get(1) else {
            return Err("interaction record has no JSON payload".into());
        };
        let Argument::QuotedLiteral(payload) = &ast.arguments[*payload as usize] else {
            return Err("interaction record payload must be a quoted JSON string".into());
        };
        let entry: Interaction = serde_json::from_str(payload).map_err(|e| e.to_string())?;
        if entry.private != private {
            return Err("interaction privacy does not match its archive".into());
        }
        if !seen.insert(entry.id.clone()) {
            return Err(format!("duplicate interaction id {}", entry.id));
        }
        entries.push(entry);
    }
    let expected = render(&entries)?;
    let statements = |s: &str| {
        files::kr_lines(s)
            .into_iter()
            .map(|(_, t)| t)
            .collect::<Vec<_>>()
    };
    if statements(text) != statements(&expected) {
        return Err(
            "interaction facts disagree with their records; restore the archive or use lucy record"
                .into(),
        );
    }
    Ok(entries)
}

fn legacy(paths: &Paths, private: bool) -> Result<Vec<Interaction>, String> {
    let path = if private {
        &paths.private_journal
    } else {
        &paths.journal
    };
    let Some(text) = files::read_optional(path)? else {
        return Ok(Vec::new());
    };
    Ok(files::parse_journal(&text, private)
        .into_iter()
        .enumerate()
        .map(|(i, entry)| {
            let time = entry.text.get(..5).filter(|s| s.as_bytes()[2] == b':');
            let timestamp = time
                .map(|t| format!("{}T{t}:00Z", entry.date))
                .unwrap_or(entry.date);
            Interaction {
                id: format!(
                    "Legacy{}{}",
                    if private { "Private" } else { "Public" },
                    i + 1
                ),
                speaker: "Unknown".into(),
                about: crate::topics::tags_of(&entry.text),
                text: entry.text,
                kind: Kind::LegacyJournal,
                timestamp,
                host: entry.host,
                source: files::short_name(path),
                private,
                ..Interaction::default()
            }
        })
        .collect())
}

pub fn archive_path(paths: &Paths, private: bool) -> &Path {
    if private {
        &paths.private_interactions
    } else {
        &paths.interactions
    }
}

/// Legacy Markdown remains available when no archive exists. The first write
/// imports it once; subsequent reads use the KB exclusively.
pub fn read(paths: &Paths, private: bool) -> Result<Vec<Interaction>, String> {
    let path = archive_path(paths, private);
    match files::read_optional(path)? {
        Some(text) => decode(&text, private).map_err(|e| format!("{}: {e}", path.display())),
        None => legacy(paths, private),
    }
}

/// An explicit conversation-only scope. The constitution's universal rules
/// otherwise make even an unrelated message query grow with the whole domain.
pub fn query_engine(paths: &Paths) -> Result<NibliEngine, String> {
    if !paths.constitution.is_file() {
        return Err("no memory folder: run `lucy init`".into());
    }
    let engine = NibliEngine::new();
    for private in [false, true] {
        for entry in read(paths, private)? {
            engine
                .assert_text(&facts(&entry)?)
                .map_err(|e| e.to_string())?;
        }
    }
    Ok(engine)
}

fn lock(paths: &Paths) -> Result<File, String> {
    if !paths.constitution.is_file() {
        return Err("no memory folder: run `lucy init`".into());
    }
    let path = paths.interactions.with_file_name(".interactions.lock");
    let file = OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&path)
        .map_err(|e| format!("cannot open {}: {e}", path.display()))?;
    file.lock()
        .map_err(|e| format!("cannot lock {}: {e}", path.display()))?;
    Ok(file)
}

fn validate(contents: &str) -> Result<(), String> {
    let engine = NibliEngine::new();
    engine
        .assert_text(contents)
        .map_err(|e| format!("conversation KB refused: {e}"))?;
    Ok(())
}

/// Import both journals without treating old summaries as verbatim messages.
pub fn migrate(paths: &Paths) -> Result<usize, String> {
    let _guard = lock(paths)?;
    let mut imported = 0;
    for private in [false, true] {
        let path = archive_path(paths, private);
        if path.exists() {
            continue;
        }
        let entries = legacy(paths, private)?;
        if entries.is_empty() && private {
            continue;
        }
        let contents = render(&entries)?;
        validate(&contents)?;
        files::write_atomic(path, &contents)?;
        imported += entries.len();
    }
    Ok(imported)
}

/// Append a batch to one privacy partition atomically. The lock spans the
/// entire read/allocate/validate/replace cycle, including separate processes.
pub fn append(
    env: &Env,
    paths: &Paths,
    mut incoming: Vec<Interaction>,
) -> Result<Vec<Interaction>, String> {
    if incoming.is_empty() {
        return Err("record needs at least one interaction".into());
    }
    let _guard = lock(paths)?;
    let private = incoming[0].private;
    if incoming.iter().any(|e| e.private != private) {
        return Err("record a public and a private batch separately".into());
    }
    let mut existing = read(paths, private)?;
    let other = read(paths, !private)?;
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_secs();
    let (date, hm) = files::stamp_utc(secs as i64);
    let now = format!("{date}T{hm}:{:02}Z", secs % 60);
    let mut additions = String::new();
    for entry in &mut incoming {
        if entry.id.is_empty() {
            let mut n = existing.len() + 1;
            loop {
                let id = format!("Lucy{}{}", if private { "Private" } else { "Public" }, n);
                if !existing.iter().any(|e| e.id == id) {
                    entry.id = id;
                    break;
                }
                n += 1;
            }
        }
        if other.iter().any(|e| e.id == entry.id) {
            return Err(format!(
                "interaction id {} already exists in the other archive",
                entry.id
            ));
        }
        let previous = existing.iter().find(|e| e.id == entry.id);
        if entry.timestamp.is_empty() {
            entry.timestamp = previous
                .map(|e| e.timestamp.clone())
                .unwrap_or_else(|| now.clone());
        }
        if entry.host.is_empty() {
            entry.host = previous
                .map(|e| e.host.clone())
                .unwrap_or_else(|| env.host.clone());
        }
        if let Some(from) = &entry.from {
            let origin = existing
                .iter()
                .chain(other.iter())
                .find(|e| &e.id == from)
                .ok_or_else(|| format!("source interaction {from} does not exist"))?;
            if origin.private && !private {
                return Err("an extraction of a private interaction must stay private".into());
            }
            if matches!(entry.kind, Kind::Claim | Kind::Decision) && entry.speaker != origin.speaker
            {
                return Err("extraction speaker must match the cited interaction".into());
            }
        }
        if let Some(previous) = previous {
            if entry != previous {
                return Err(format!(
                    "interaction id {} already has different content",
                    entry.id
                ));
            }
            continue;
        }
        additions.push_str(&facts(entry)?);
        existing.push(entry.clone());
    }
    // Compile quoted text plus metadata before any write. In particular a
    // malformed extraction cannot leave its message or half a batch behind.
    validate(&additions)?;
    let contents = render(&existing)?;
    files::write_atomic(archive_path(paths, private), &contents)?;
    Ok(incoming)
}

/// A readable capsule entry; exact source text remains available via transcript.
pub fn journal(entry: &Interaction) -> JournalEntry {
    let mut prefix = format!("[interaction: {}] [kind: {}] ", entry.id, entry.kind.name());
    if entry.kind != Kind::LegacyJournal {
        for topic in &entry.about {
            prefix.push_str(&format!("[about: {topic}] "));
        }
        if entry.kind == Kind::Note && !entry.source.is_empty() {
            prefix.push_str(&format!("[reported: {}] ", entry.source));
        }
        if entry.kind == Kind::Message {
            prefix.push_str(&entry.speaker);
            if entry.speaker == "Lucy" && entry.source.starts_with("ollama:") {
                prefix.push_str(&format!(
                    " (via {})",
                    entry.source.trim_start_matches("ollama:")
                ));
            }
            prefix.push_str(": ");
        }
    }
    JournalEntry {
        date: entry.timestamp.split('T').next().unwrap_or("").into(),
        host: entry.host.clone(),
        text: format!("{prefix}{}", entry.text),
        private: entry.private,
    }
}
