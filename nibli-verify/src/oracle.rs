//! The classical-entailment oracle: drive Vampire on a TPTP FOF problem and read its
//! SZS status. A problem with the query as a `conjecture` yields `Theorem` when the KB
//! entails it and `CounterSatisfiable` when it does not — exactly the two-sided verdict
//! the differential gate needs.

use std::io::Write;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static COUNTER: AtomicU64 = AtomicU64::new(0);

/// How to invoke the prover.
pub struct OracleConfig {
    /// Prover binary (overridable via `NIBLI_VAMPIRE`, e.g. an absolute store path).
    pub binary: String,
    /// Per-invocation wall-clock limit, in seconds (Vampire `-t`).
    pub timeout_secs: u32,
}

impl Default for OracleConfig {
    fn default() -> Self {
        Self {
            binary: std::env::var("NIBLI_VAMPIRE").unwrap_or_else(|_| "vampire".to_string()),
            timeout_secs: 10,
        }
    }
}

/// The oracle's classical verdict for a `(KB ⊨? query)` problem.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Oracle {
    /// KB classically entails the query (`Theorem`).
    Entailed,
    /// KB does not entail the query (`CounterSatisfiable` / `Satisfiable`).
    NotEntailed,
    /// The prover could not decide (timeout / gave up / no status).
    Inconclusive(String),
}

/// Is the prover binary runnable? (Used by the CI gate to skip cleanly when absent.)
pub fn available(cfg: &OracleConfig) -> bool {
    Command::new(&cfg.binary)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run the prover on a TPTP problem and classify the SZS status.
pub fn decide(tptp: &str, cfg: &OracleConfig) -> Result<Oracle, String> {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!("nibli_verify_{}_{}.p", std::process::id(), id));
    {
        let mut f =
            std::fs::File::create(&path).map_err(|e| format!("create {}: {e}", path.display()))?;
        f.write_all(tptp.as_bytes())
            .map_err(|e| format!("write {}: {e}", path.display()))?;
    }
    let output = Command::new(&cfg.binary)
        .arg("-t")
        .arg(cfg.timeout_secs.to_string())
        .arg(&path)
        .output();
    let _ = std::fs::remove_file(&path);

    let output = output.map_err(|e| format!("spawn {}: {e}", cfg.binary))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    Ok(classify(&stdout))
}

/// Map Vampire's textual output to an [`Oracle`] verdict.
fn classify(stdout: &str) -> Oracle {
    match parse_szs_status(stdout) {
        Some(s) => match s.as_str() {
            // KB entails the conjecture.
            "Theorem" | "Unsatisfiable" | "ContradictoryAxioms" => Oracle::Entailed,
            // KB does not entail it (a countermodel exists).
            "CounterSatisfiable" | "Satisfiable" => Oracle::NotEntailed,
            other => Oracle::Inconclusive(other.to_string()),
        },
        None if stdout.contains("Refutation found") => Oracle::Entailed,
        None => Oracle::Inconclusive("no SZS status".to_string()),
    }
}

/// Extract the token after `SZS status` from a `% SZS status Theorem for foo` line.
fn parse_szs_status(stdout: &str) -> Option<String> {
    for line in stdout.lines() {
        if let Some(rest) = line.split("SZS status").nth(1) {
            if let Some(tok) = rest.split_whitespace().next() {
                return Some(tok.to_string());
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_statuses() {
        assert_eq!(classify("% SZS status Theorem for t"), Oracle::Entailed);
        assert_eq!(
            classify("% SZS status CounterSatisfiable for t"),
            Oracle::NotEntailed
        );
        assert!(matches!(
            classify("% SZS status Timeout for t"),
            Oracle::Inconclusive(_)
        ));
        assert!(matches!(classify("nothing here"), Oracle::Inconclusive(_)));
        // Human-phrase fallback.
        assert_eq!(classify("% Refutation found. Thanks!"), Oracle::Entailed);
    }
}
