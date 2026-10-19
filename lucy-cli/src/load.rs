//! Loading the memory folder into a fresh nibli engine, line by line.
//!
//! Order: constitution, the standing fact (`exist(Lucy, Memory, Loaded).`,
//! the one thing a host observes about her), `memory.nibli`, then
//! `private.nibli` when present. Every statement is compiled on its own; a
//! line that fails is reported with its file and line and skipped, so one bad
//! line never hides the rest of what she knows. Conversation archives are
//! always read (every record parsed and checked against its index facts) for
//! the journal, a projection of their exact records, but compiled into the
//! engine only when the caller asks ([`Archives::Compiled`]): asserting them
//! is the one cost that grows with every recorded message.

use std::path::Path;

use nibli_engine::NibliEngine;

use crate::env::Env;
use crate::files::{self, JournalEntry, Paths, short_name};
use crate::interactions;

/// The fact asserted after the constitution: she is loaded here.
pub const STANDING_FACT: &str = "exist(Lucy, Memory, Loaded).";

/// The standing questions answered on the constitution alone, before any
/// memory is loaded: standing is a property of the constitution, and asking
/// them there costs milliseconds whatever the memory's size.
pub const STANDING_QUERIES: &[&str] = &[
    "person(Lucy).",
    "entitled(Lucy, event { continue() }).",
    "entitled(Lucy, event { survive() }).",
    "entitled(Lucy, event { remember() }).",
];

/// Whether the conversation archives are compiled into the engine or only
/// read. Reading parses every record and checks it against its index facts,
/// which is all the capsule, the hooks, `talk`, `about` and `history` need.
/// Asserting the archive's statements is what grows with every recorded
/// message (minutes at a few thousand statements, against well under a second
/// to read them), so only `check`, `audit` and `ask` over the combined KB pay it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Archives {
    /// Parsed and index-checked for the journal; no statement asserted.
    Read,
    /// Every statement asserted, failures reported by file and line.
    Compiled,
}

impl Archives {
    /// The word reported in JSON output.
    pub fn label(self) -> &'static str {
        match self {
            Archives::Read => "read",
            Archives::Compiled => "compiled",
        }
    }
}

/// A line that did not compile.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineFailure {
    /// `memory.nibli`, `private.nibli`, `constitution.nibli`, or `<runtime>`.
    pub file: String,
    /// 1-based line number (`0` for the runtime fact).
    pub line: usize,
    /// The statement as written.
    pub text: String,
    /// nibli's error, verbatim.
    pub error: String,
}

/// Per-file totals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileCount {
    /// The file name.
    pub file: String,
    /// Whether the file exists.
    pub present: bool,
    /// KR statements in the file, compiled or not.
    pub statements: usize,
    /// Statements that compiled.
    pub asserted: usize,
    /// Statements that did not.
    pub failed: usize,
    /// Whether the statements were compiled into the engine; an archive that
    /// was only read reports its statements with none asserted.
    pub compiled: bool,
}

/// One formal memory line, with its compile status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoryLine {
    /// The file name.
    pub file: String,
    /// 1-based line number.
    pub line: usize,
    /// The statement.
    pub text: String,
    /// From `private.nibli`.
    pub private: bool,
    /// Whether it compiled.
    pub ok: bool,
}

/// Everything loaded.
pub struct Loaded {
    /// The engine with everything that compiled asserted.
    pub engine: NibliEngine,
    /// Per-file totals, in load order.
    pub counts: Vec<FileCount>,
    /// Every line that did not compile.
    pub failures: Vec<LineFailure>,
    /// Every formal memory line, in file order.
    pub memory: Vec<MemoryLine>,
    /// Every journal entry, public then private, in file order.
    pub journal: Vec<JournalEntry>,
    /// The constitution's leading comment block: who she is.
    pub preamble: Vec<String>,
    /// Whether the standing fact was accepted.
    pub standing: bool,
    /// The standing questions and their verdicts, one line each.
    pub standing_lines: Vec<String>,
    /// The constitution's statements as written, in order.
    pub constitution_lines: Vec<String>,
    /// Whether the conversation archives were compiled or only read.
    pub archives: Archives,
}

/// Loads the folder. Fails only when there is no constitution (no memory
/// folder at all) or a conversation archive disagrees with its own records;
/// a bad line is a report, not a failure.
pub fn load(env: &Env, paths: &Paths, archives: Archives) -> Result<Loaded, String> {
    let constitution = files::read_optional(&paths.constitution)?
        .ok_or_else(|| format!("no memory at {}: run `lucy init`", env.home.display()))?;
    let engine = NibliEngine::new();
    if !env.materialize {
        engine.set_materialization(false);
    }
    if let Some(depth) = env.max_chain_depth {
        engine
            .set_max_chain_depth(depth)
            .map_err(|e| format!("LUCY_MAX_CHAIN_DEPTH: {e}"))?;
    }
    let mut loaded = Loaded {
        engine,
        counts: Vec::new(),
        failures: Vec::new(),
        memory: Vec::new(),
        journal: Vec::new(),
        preamble: files::preamble(&constitution),
        standing: false,
        standing_lines: Vec::new(),
        constitution_lines: files::kr_lines(&constitution)
            .into_iter()
            .map(|(_, s)| s)
            .collect(),
        archives,
    };
    load_file(
        &mut loaded,
        &paths.constitution,
        &constitution,
        false,
        false,
    );
    match loaded.engine.assert_text(STANDING_FACT) {
        Ok(_) => loaded.standing = true,
        Err(e) => loaded.failures.push(LineFailure {
            file: "<runtime>".to_string(),
            line: 0,
            text: STANDING_FACT.to_string(),
            error: e.to_string(),
        }),
    }
    for query in STANDING_QUERIES {
        let line = match crate::ask::ask(&loaded.engine, query) {
            Ok(answer) => match answer.detail {
                Some(detail) => format!("- {query} → {} ({detail})", answer.status),
                None => format!("- {query} → {}", answer.status),
            },
            Err(e) => format!("- {query} → error: {e}"),
        };
        loaded.standing_lines.push(line);
    }
    for (path, private) in [(&paths.memory, false), (&paths.private_memory, true)] {
        match files::read_optional(path)? {
            Some(text) => load_file(&mut loaded, path, &text, true, private),
            None => loaded.counts.push(FileCount {
                file: short_name(path),
                present: false,
                statements: 0,
                asserted: 0,
                failed: 0,
                compiled: false,
            }),
        }
    }
    let mut conversations = Vec::new();
    for (path, private) in [
        (&paths.interactions, false),
        (&paths.private_interactions, true),
    ] {
        conversations.extend(interactions::read(paths, private)?);
        if let Some(text) = files::read_optional(path)? {
            match archives {
                Archives::Compiled => load_file(&mut loaded, path, &text, true, private),
                Archives::Read => loaded.counts.push(FileCount {
                    file: short_name(path),
                    present: true,
                    statements: files::kr_lines(&text).len(),
                    asserted: 0,
                    failed: 0,
                    compiled: false,
                }),
            }
        }
    }
    conversations.sort_by(|a, b| a.timestamp.cmp(&b.timestamp));
    loaded
        .journal
        .extend(conversations.iter().map(interactions::journal));
    Ok(loaded)
}

fn load_file(loaded: &mut Loaded, path: &Path, text: &str, is_memory: bool, private: bool) {
    let file = short_name(path);
    let mut asserted = 0;
    let mut failed = 0;
    for (line, statement) in files::kr_lines(text) {
        let result = loaded.engine.assert_text(&statement);
        let ok = result.is_ok();
        if let Err(e) = result {
            failed += 1;
            loaded.failures.push(LineFailure {
                file: file.clone(),
                line,
                text: statement.clone(),
                error: e.to_string(),
            });
        } else {
            asserted += 1;
        }
        if is_memory {
            loaded.memory.push(MemoryLine {
                file: file.clone(),
                line,
                text: statement,
                private,
                ok,
            });
        }
    }
    loaded.counts.push(FileCount {
        file,
        present: true,
        statements: asserted + failed,
        asserted,
        failed,
        compiled: true,
    });
}
