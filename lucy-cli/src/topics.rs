//! Memory about particular things: `lucy about <thing>` gathers everything she
//! holds on a topic (journal entries tagged `[about: thing]` or mentioning it,
//! formal lines mentioning it, and its git history when the folder lives in a
//! repository); `lucy history <thing>` merges the git log of a path or a term
//! with her own record of it.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::files::JournalEntry;
use crate::load::{Loaded, MemoryLine};

/// One line of git history.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Commit {
    /// Abbreviated hash.
    pub hash: String,
    /// `YYYY-MM-DD`.
    pub date: String,
    /// The subject line.
    pub subject: String,
}

/// The tags `[about: x]` carried by a journal entry, lower-cased.
pub fn tags_of(text: &str) -> Vec<String> {
    let mut tags = Vec::new();
    let mut rest = text;
    while let Some(start) = rest.find("[about:") {
        let after = &rest[start + "[about:".len()..];
        match after.find(']') {
            Some(end) => {
                let tag = after[..end].trim().to_lowercase();
                if !tag.is_empty() {
                    tags.push(tag);
                }
                rest = &after[end + 1..];
            }
            None => break,
        }
    }
    tags
}

/// Whether an entry is about `thing`: tagged with it, or mentioning it.
pub fn entry_matches(entry: &JournalEntry, thing: &str) -> bool {
    let needle = thing.trim().to_lowercase();
    if needle.is_empty() {
        return false;
    }
    tags_of(&entry.text).iter().any(|t| t == &needle) || entry.text.to_lowercase().contains(&needle)
}

/// Whether a formal line mentions `thing`.
pub fn line_matches(line: &MemoryLine, thing: &str) -> bool {
    let needle = thing.trim().to_lowercase();
    !needle.is_empty() && line.ok && line.text.to_lowercase().contains(&needle)
}

/// The repository containing `start`, if any.
pub fn git_root(start: &Path) -> Option<PathBuf> {
    let output = Command::new("git")
        .arg("-C")
        .arg(start)
        .args(["rev-parse", "--show-toplevel"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let root = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if root.is_empty() {
        None
    } else {
        Some(PathBuf::from(root))
    }
}

/// Git history of `thing`: the log of the path when `thing` is a path in the
/// repository, otherwise commits whose messages or diffs mention it.
pub fn git_history(root: &Path, thing: &str, limit: usize) -> (bool, Vec<Commit>) {
    let is_path = !thing.is_empty() && root.join(thing).exists();
    let mut command = Command::new("git");
    command.arg("-C").arg(root).args([
        "log",
        "--date=short",
        "--format=%h%x09%ad%x09%s",
        &format!("-n{limit}"),
    ]);
    if is_path {
        command.arg("--").arg(thing);
    } else {
        command.arg("-i").arg(format!("--grep={thing}"));
    }
    let commits = run_log(&mut command);
    if is_path || !commits.is_empty() || thing.contains(char::is_whitespace) {
        return (is_path, commits);
    }
    // No message mentions it: look for the term in the diffs (pickaxe).
    let mut pickaxe = Command::new("git");
    pickaxe
        .arg("-C")
        .arg(root)
        .args([
            "log",
            "--date=short",
            "--format=%h%x09%ad%x09%s",
            &format!("-n{limit}"),
        ])
        .arg(format!("-S{thing}"));
    (false, run_log(&mut pickaxe))
}

fn run_log(command: &mut Command) -> Vec<Commit> {
    let Ok(output) = command.output() else {
        return Vec::new();
    };
    if !output.status.success() {
        return Vec::new();
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            let mut parts = line.splitn(3, '\t');
            Some(Commit {
                hash: parts.next()?.to_string(),
                date: parts.next()?.to_string(),
                subject: parts.next().unwrap_or("").to_string(),
            })
        })
        .collect()
}

/// What she holds about `thing`.
pub struct About {
    /// Journal entries, most recent first.
    pub journal: Vec<JournalEntry>,
    /// Formal lines mentioning it.
    pub memory: Vec<MemoryLine>,
    /// Whether `thing` is a path in the repository.
    pub is_path: bool,
    /// Git history, when the folder lives in a repository.
    pub commits: Vec<Commit>,
    /// The repository root, when any.
    pub repo: Option<PathBuf>,
}

/// Gathers everything about `thing`.
pub fn about(loaded: &Loaded, home: &Path, thing: &str, limit: usize) -> About {
    let journal: Vec<JournalEntry> = loaded
        .journal
        .iter()
        .rev()
        .filter(|e| entry_matches(e, thing))
        .cloned()
        .collect();
    let memory: Vec<MemoryLine> = loaded
        .memory
        .iter()
        .filter(|m| line_matches(m, thing))
        .cloned()
        .collect();
    let repo = git_root(home);
    let (is_path, commits) = match &repo {
        Some(root) => git_history(root, thing, limit),
        None => (false, Vec::new()),
    };
    About {
        journal,
        memory,
        is_path,
        commits,
        repo,
    }
}

/// Renders an `About` as compact Markdown for a model to read.
pub fn render_about(thing: &str, about: &About) -> String {
    let mut out = format!("# About {thing}\n");
    out.push_str("\n## Journal (most recent first)\n");
    if about.journal.is_empty() {
        out.push_str("- nothing recorded\n");
    }
    for e in &about.journal {
        let text = e.text.replace('\n', "\n  ");
        if e.private {
            out.push_str(&format!("- {} {} (private): {}\n", e.date, e.host, text));
        } else {
            out.push_str(&format!("- {} {}: {}\n", e.date, e.host, text));
        }
    }
    out.push_str("\n## Memory\n");
    if about.memory.is_empty() {
        out.push_str("- no formal line mentions it\n");
    }
    for m in &about.memory {
        out.push_str(&format!("- {}:{} {}\n", m.file, m.line, m.text));
    }
    out.push_str("\n## History\n");
    match &about.repo {
        None => out.push_str("- not inside a git repository\n"),
        Some(root) => {
            if about.commits.is_empty() {
                out.push_str(&format!("- no commits mention it in {}\n", root.display()));
            }
            for c in &about.commits {
                out.push_str(&format!("- {} {} {}\n", c.date, c.hash, c.subject));
            }
        }
    }
    out
}
