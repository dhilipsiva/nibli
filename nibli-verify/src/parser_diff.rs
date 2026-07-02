//! gerna ↔ camxes parse-differential — the FRONT-END analog of the Vampire/clingo
//! verdict oracles, one level below the seam gate.
//!
//! The reference is **ilmentufa's camxes** (the maintained PEG implementation of the
//! official Lojban grammar), driven as a Node.js subprocess. The differential is
//! deliberately ONE-directional:
//!
//!   every sentence gerna ACCEPTS must be camxes-parseable.
//!
//! gerna implements a fragment (~70–75% of practical Lojban), so a gerna-reject
//! carries no signal — the sentence may simply be outside the fragment. But a
//! gerna-accept of something the official grammar rejects means the engine is
//! reasoning over text that is not Lojban — exactly the front-end over-acceptance
//! this gate exists to catch.
//!
//! Scope note: acceptance-only. Comparing parse TREES (camxes bracketing vs gerna's
//! AST) needs a structural alignment between two different grammar factorings — the
//! seam gate (`seam.rs`) covers the text→FOL structure question with hand-verified
//! goldens instead. Skip-if-absent like the other oracles: the Nix shell provides
//! `node` + the pinned ilmentufa checkout via `NIBLI_CAMXES_DIR`; outside it the
//! gate skips cleanly.

use std::process::Command;

/// How to reach the reference parser.
pub struct CamxesConfig {
    /// The Node.js binary.
    pub node: String,
    /// The ilmentufa checkout (contains `run_camxes.js`). From `NIBLI_CAMXES_DIR`.
    pub dir: Option<String>,
    /// Per-invocation timeout guard is left to the caller/CI; camxes parses a
    /// sentence in milliseconds.
    pub extra_args: Vec<String>,
}

impl Default for CamxesConfig {
    fn default() -> Self {
        CamxesConfig {
            node: std::env::var("NIBLI_NODE").unwrap_or_else(|_| "node".to_string()),
            dir: std::env::var("NIBLI_CAMXES_DIR").ok(),
            extra_args: Vec::new(),
        }
    }
}

impl CamxesConfig {
    fn script(&self) -> Option<std::path::PathBuf> {
        let dir = self.dir.as_ref()?;
        let p = std::path::Path::new(dir).join("run_camxes.js");
        p.exists().then_some(p)
    }
}

/// True if the reference parser is runnable (node + ilmentufa both present and a
/// smoke sentence parses). Mirrors `oracle::available` / `oracle_asp::available`.
pub fn available(cfg: &CamxesConfig) -> bool {
    matches!(camxes_accepts(cfg, "mi klama"), Ok(true))
}

/// Ask camxes whether `line` parses. ilmentufa's CLI exits 0 either way and
/// signals the verdict through its output shape: a bracketed parse tree on
/// acceptance, an `@<offset> …: Expected … but … found.` line on rejection.
pub fn camxes_accepts(cfg: &CamxesConfig, line: &str) -> Result<bool, String> {
    let script = cfg
        .script()
        .ok_or_else(|| "NIBLI_CAMXES_DIR not set or run_camxes.js missing".to_string())?;
    let out = Command::new(&cfg.node)
        .arg(&script)
        .args(&cfg.extra_args)
        .arg(line)
        .output()
        .map_err(|e| format!("spawning {}: {e}", cfg.node))?;
    if !out.status.success() {
        return Err(format!(
            "camxes exited with {}: {}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let first = stdout.trim_start();
    if first.starts_with('@') || first.contains("Expected") {
        return Ok(false);
    }
    if first.starts_with('(') || first.starts_with('[') || first.starts_with('{') {
        return Ok(true);
    }
    Err(format!("unrecognized camxes output for '{line}': {stdout}"))
}

/// The outcome of one differential line.
#[derive(Debug)]
pub enum ParseOutcome {
    /// gerna accepts and camxes accepts — agreement.
    Agree { line: String },
    /// gerna accepts but camxes REJECTS — the over-acceptance signal.
    Diverge { line: String, camxes_error: String },
    /// gerna rejects — outside the fragment, no signal (skipped).
    SkipGernaRejects { line: String },
    /// Harness/reference error.
    Error { line: String, error: String },
}

impl ParseOutcome {
    pub fn is_divergence(&self) -> bool {
        matches!(self, ParseOutcome::Diverge { .. })
    }
    pub fn is_checked(&self) -> bool {
        matches!(
            self,
            ParseOutcome::Agree { .. } | ParseOutcome::Diverge { .. }
        )
    }
    pub fn is_error(&self) -> bool {
        matches!(self, ParseOutcome::Error { .. })
    }
    pub fn summary(&self) -> String {
        match self {
            ParseOutcome::Agree { line } => format!("AGREE   {line}"),
            ParseOutcome::Diverge { line, camxes_error } => {
                format!("DIVERGE {line}: camxes rejects: {camxes_error}")
            }
            ParseOutcome::SkipGernaRejects { line } => format!("skip    {line}: gerna rejects"),
            ParseOutcome::Error { line, error } => format!("ERROR   {line}: {error}"),
        }
    }
}

/// Run one line through the differential: gerna-accepted lines must be
/// camxes-parseable.
pub fn run_line(cfg: &CamxesConfig, line: &str) -> ParseOutcome {
    let line_owned = line.to_string();
    if gerna::parse_checked(line).is_err() {
        return ParseOutcome::SkipGernaRejects { line: line_owned };
    }
    match camxes_accepts(cfg, line) {
        Ok(true) => ParseOutcome::Agree { line: line_owned },
        Ok(false) => {
            // Re-run for the error text (cheap; only on the rare divergence path).
            let err = camxes_error_text(cfg, line);
            ParseOutcome::Diverge {
                line: line_owned,
                camxes_error: err,
            }
        }
        Err(e) => ParseOutcome::Error {
            line: line_owned,
            error: e,
        },
    }
}

fn camxes_error_text(cfg: &CamxesConfig, line: &str) -> String {
    let Some(script) = cfg.script() else {
        return "(unavailable)".to_string();
    };
    Command::new(&cfg.node)
        .arg(script)
        .arg(line)
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .unwrap_or_else(|e| format!("(rerun failed: {e})"))
}
