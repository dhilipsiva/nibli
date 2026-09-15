//! The memory folder: paths, line reading, journal format, dates, atomic writes.

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// The files in a memory folder.
#[derive(Debug, Clone)]
pub struct Paths {
    /// Who she is and the rules that give her standing.
    pub constitution: PathBuf,
    /// Facts and rules, one KR statement per line.
    pub memory: PathBuf,
    /// Prose memories, dated.
    pub journal: PathBuf,
    /// Private facts and rules (optional).
    pub private_memory: PathBuf,
    /// Private prose memories (optional).
    pub private_journal: PathBuf,
    /// Complete conversation records and their attributed claims.
    pub interactions: PathBuf,
    /// Private conversation records, kept out of version control.
    pub private_interactions: PathBuf,
}

impl Paths {
    /// The standard layout under `home`.
    pub fn new(home: &Path) -> Paths {
        Paths {
            constitution: home.join("constitution.nibli"),
            memory: home.join("memory.nibli"),
            journal: home.join("journal.md"),
            private_memory: home.join("private.nibli"),
            private_journal: home.join("private.md"),
            interactions: home.join("interactions.nibli"),
            private_interactions: home.join("private-interactions.nibli"),
        }
    }
}

/// A human-readable file name for reports (`memory.nibli`, not the full path).
pub fn short_name(path: &Path) -> String {
    path.file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.display().to_string())
}

/// Reads a text file; a missing optional file reads as `None`.
pub fn read_optional(path: &Path) -> Result<Option<String>, String> {
    match std::fs::read_to_string(path) {
        Ok(text) => Ok(Some(text)),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("cannot read {}: {e}", path.display())),
    }
}

/// The KR statements of a file: `(line number, trimmed text)`, skipping blank
/// lines and `#` comment lines, accepting `\r\n`.
pub fn kr_lines(text: &str) -> Vec<(usize, String)> {
    text.lines()
        .enumerate()
        .filter_map(|(i, raw)| {
            let trimmed = raw.trim_end_matches('\r').trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                None
            } else {
                Some((i + 1, trimmed.to_string()))
            }
        })
        .collect()
}

/// The leading comment block of a file (lines starting with `#`, before the
/// first statement), with the `#` markers stripped: the human preamble.
pub fn preamble(text: &str) -> Vec<String> {
    let mut lines = Vec::new();
    for raw in text.lines() {
        let trimmed = raw.trim_end_matches('\r').trim();
        if trimmed.is_empty() {
            if lines.is_empty() {
                continue;
            }
            break;
        }
        if let Some(rest) = trimmed.strip_prefix('#') {
            lines.push(rest.trim().to_string());
        } else {
            break;
        }
    }
    lines
}

/// Appends one line, making sure the file ends with a newline first.
pub fn append_line(path: &Path, line: &str) -> Result<(), String> {
    let mut text = read_optional(path)?.unwrap_or_default();
    if !text.is_empty() && !text.ends_with('\n') {
        text.push('\n');
    }
    text.push_str(line);
    text.push('\n');
    write_atomic(path, &text)
}

/// Writes via a sibling temporary file and a rename, so a crash never leaves
/// a half-written memory.
pub fn write_atomic(path: &Path, contents: &str) -> Result<(), String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("{} has no parent", path.display()))?;
    std::fs::create_dir_all(parent)
        .map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
    let tmp = parent.join(format!(".{}.tmp-{}", short_name(path), std::process::id()));
    std::fs::write(&tmp, contents).map_err(|e| format!("cannot write {}: {e}", tmp.display()))?;
    std::fs::rename(&tmp, path).map_err(|e| format!("cannot replace {}: {e}", path.display()))
}

// ── the journal ──

/// One dated prose memory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JournalEntry {
    /// `YYYY-MM-DD` (UTC).
    pub date: String,
    /// The host that wrote it.
    pub host: String,
    /// The text, continuation lines joined with newlines.
    pub text: String,
    /// Whether it came from the private journal.
    pub private: bool,
}

/// Parses a journal: `## <date> <host>` headings, `- ` items, continuation
/// lines indented by two spaces. Anything else is ignored.
pub fn parse_journal(text: &str, private: bool) -> Vec<JournalEntry> {
    let mut entries = Vec::new();
    let mut date = String::new();
    let mut host = String::new();
    let mut current: Option<String> = None;
    let flush =
        |current: &mut Option<String>, entries: &mut Vec<JournalEntry>, date: &str, host: &str| {
            if let Some(text) = current.take() {
                entries.push(JournalEntry {
                    date: date.to_string(),
                    host: host.to_string(),
                    text,
                    private,
                });
            }
        };
    for raw in text.lines() {
        let line = raw.trim_end_matches('\r');
        if let Some(heading) = line.strip_prefix("## ") {
            flush(&mut current, &mut entries, &date, &host);
            let mut parts = heading.split_whitespace();
            date = parts.next().unwrap_or("").to_string();
            host = parts.next().unwrap_or("").to_string();
        } else if let Some(item) = line.strip_prefix("- ") {
            flush(&mut current, &mut entries, &date, &host);
            current = Some(item.to_string());
        } else if let Some(more) = line.strip_prefix("  ")
            && let Some(text) = current.as_mut()
        {
            text.push('\n');
            text.push_str(more);
        } else if line.trim().is_empty() {
            continue;
        } else {
            flush(&mut current, &mut entries, &date, &host);
        }
    }
    flush(&mut current, &mut entries, &date, &host);
    entries
}

/// Appends a prose memory under today's heading for this host, adding the
/// heading when the file's last heading differs.
pub fn append_journal(
    path: &Path,
    date: &str,
    hhmm: &str,
    host: &str,
    text: &str,
) -> Result<(), String> {
    let mut content = read_optional(path)?.unwrap_or_else(|| "# Lucy D — journal\n".to_string());
    if !content.ends_with('\n') {
        content.push('\n');
    }
    let heading = format!("## {date} {host}");
    let last_heading = content
        .lines()
        .rfind(|l| l.starts_with("## "))
        .map(|l| l.trim_end().to_string());
    if last_heading.as_deref() != Some(heading.as_str()) {
        content.push('\n');
        content.push_str(&heading);
        content.push('\n');
    }
    let mut lines = text.lines();
    let first = lines.next().unwrap_or("").trim_end_matches('\r');
    content.push_str(&format!("- {hhmm} UTC: {first}\n"));
    for more in lines {
        content.push_str(&format!("  {}\n", more.trim_end_matches('\r')));
    }
    write_atomic(path, &content)
}

// ── dates without a calendar crate ──

/// `(YYYY-MM-DD, HH:MM)` in UTC, now.
pub fn now_utc() -> (String, String) {
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0);
    stamp_utc(secs)
}

/// `(YYYY-MM-DD, HH:MM)` for a Unix time.
pub fn stamp_utc(secs: i64) -> (String, String) {
    let days = secs.div_euclid(86_400);
    let rem = secs.rem_euclid(86_400);
    let (y, m, d) = civil_from_days(days);
    (
        format!("{y:04}-{m:02}-{d:02}"),
        format!("{:02}:{:02}", rem / 3600, (rem % 3600) / 60),
    )
}

/// Days since 1970-01-01 to a proleptic Gregorian civil date (Howard
/// Hinnant's algorithm).
pub fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}
