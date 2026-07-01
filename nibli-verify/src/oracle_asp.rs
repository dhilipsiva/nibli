//! The closed-world / stratified-NAF oracle: drive **clingo** (Answer Set Programming) on
//! a `.lp` program and read whether the reified `goal` atom is in the stable model.
//!
//! For a stratified program clingo computes exactly ONE answer set = the perfect model,
//! which coincides with nibli's closed-world stratified semantics (`proofs/Stratification.lean`).
//! The program (see [`crate::asp`]) reifies the query into a 0-ary `goal` shown via
//! `#show goal/0.`, so the two-sided verdict is simply "is `goal` in the model": present ⇒
//! `Entailed`, absent ⇒ `NotEntailed`. This is the oracle for the fragment the classical
//! Vampire gate cannot cover (it has no closed-world assumption).

use std::io::Write;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// How to invoke the ASP solver.
pub struct AspConfig {
    /// Solver binary (overridable via `NIBLI_CLINGO`, e.g. an absolute store path).
    pub binary: String,
    /// Per-invocation wall-clock limit, in seconds (clingo `--time-limit`).
    pub timeout_secs: u32,
}

impl Default for AspConfig {
    fn default() -> Self {
        Self {
            binary: std::env::var("NIBLI_CLINGO").unwrap_or_else(|_| "clingo".to_string()),
            timeout_secs: 10,
        }
    }
}

/// The oracle's closed-world verdict for a `(KB ⊨? query)` problem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AspVerdict {
    /// `goal` is in the (unique) stable model — the KB entails the query.
    Entailed,
    /// `goal` is absent from the stable model — the KB does not entail it.
    NotEntailed,
    /// The solver could not decide (timeout / unsatisfiable / no status).
    Inconclusive(String),
}

/// Is the clingo binary runnable? (Used by the CI gate to skip cleanly when absent.)
pub fn available(cfg: &AspConfig) -> bool {
    Command::new(&cfg.binary)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run clingo on an ASP program and classify whether `goal` holds.
pub fn decide(lp: &str, cfg: &AspConfig) -> Result<AspVerdict, String> {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("nibli_verify_{}_{}.lp", std::process::id(), id));
    {
        let mut f =
            std::fs::File::create(&path).map_err(|e| format!("create {}: {e}", path.display()))?;
        f.write_all(lp.as_bytes())
            .map_err(|e| format!("write {}: {e}", path.display()))?;
    }
    let output = Command::new(&cfg.binary)
        .arg("--models=1")
        .arg(format!("--time-limit={}", cfg.timeout_secs))
        .arg(&path)
        .output();
    let _ = std::fs::remove_file(&path);

    let output = output.map_err(|e| format!("spawn {}: {e}", cfg.binary))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    Ok(classify(&stdout))
}

/// Map clingo's textual output to an [`AspVerdict`]. clingo prints the model atoms on the
/// line after `Answer:` and a status line (`SATISFIABLE` / `UNSATISFIABLE` / `UNKNOWN`).
/// A stratified positive-goal reification always has a stable model, so `UNSATISFIABLE` is
/// unexpected and treated as inconclusive (never a manufactured FALSE).
fn classify(stdout: &str) -> AspVerdict {
    let lines: Vec<&str> = stdout.lines().collect();
    let mut status: Option<&str> = None;
    let mut model_atoms: Option<Vec<String>> = None;

    for (i, line) in lines.iter().enumerate() {
        let t = line.trim();
        // Order matters: "UNSATISFIABLE" contains "SATISFIABLE", so match exact lines.
        if t == "SATISFIABLE" {
            status = Some("SAT");
        } else if t == "UNSATISFIABLE" {
            status = Some("UNSAT");
        } else if t == "UNKNOWN" {
            status = Some("UNKNOWN");
        } else if t.starts_with("Answer:") {
            // The model atoms are the whitespace tokens on the following line (blank if the
            // shown `goal` was not derived). Keep the LAST answer block (only one for --models=1).
            model_atoms = Some(
                lines
                    .get(i + 1)
                    .map(|l| l.split_whitespace().map(str::to_string).collect())
                    .unwrap_or_default(),
            );
        }
    }

    match status {
        Some("SAT") => {
            let has_goal = model_atoms
                .map(|a| a.iter().any(|x| x == "goal"))
                .unwrap_or(false);
            if has_goal {
                AspVerdict::Entailed
            } else {
                AspVerdict::NotEntailed
            }
        }
        Some("UNSAT") => AspVerdict::Inconclusive("unsatisfiable".to_string()),
        Some("UNKNOWN") => AspVerdict::Inconclusive("time-limit/unknown".to_string()),
        _ => AspVerdict::Inconclusive("no clingo status".to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_statuses() {
        // goal in the model → Entailed.
        assert_eq!(
            classify("Answer: 1\ngoal\nSATISFIABLE\n"),
            AspVerdict::Entailed
        );
        // model with a blank shown-atoms line (goal not derived) → NotEntailed.
        assert_eq!(
            classify("Answer: 1\n\nSATISFIABLE\n"),
            AspVerdict::NotEntailed
        );
        // unsat / unknown / empty → inconclusive.
        assert!(matches!(
            classify("UNSATISFIABLE\n"),
            AspVerdict::Inconclusive(_)
        ));
        assert!(matches!(classify("UNKNOWN\n"), AspVerdict::Inconclusive(_)));
        assert!(matches!(classify(""), AspVerdict::Inconclusive(_)));
    }

    #[test]
    fn unsatisfiable_not_confused_with_satisfiable() {
        // Guard the substring trap: "UNSATISFIABLE" must NOT classify as SAT/NotEntailed.
        assert!(matches!(
            classify("Answer: 1\ngoal\nUNSATISFIABLE\n"),
            AspVerdict::Inconclusive(_)
        ));
    }
}
