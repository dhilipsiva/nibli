//! Decision types for the auth hot path and explain path.

use nibli_types::logic::QueryResult;

/// Engine entailment outcome mapped for API consumers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    True,
    False,
    Unknown,
    ResourceExceeded,
}

impl From<&QueryResult> for Verdict {
    fn from(r: &QueryResult) -> Self {
        match r {
            QueryResult::True => Self::True,
            QueryResult::False => Self::False,
            QueryResult::Unknown(_) => Self::Unknown,
            QueryResult::ResourceExceeded(_) => Self::ResourceExceeded,
        }
    }
}

/// Authorization decision (proofs live only on [`Explained`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decision {
    /// True only when the engine verdict is TRUE (conservative allow).
    pub allowed: bool,
    pub verdict: Verdict,
    pub reason: Option<String>,
    /// Populated by `allowed_fields`; empty on bare `can`.
    pub fields: Vec<String>,
}

impl Decision {
    pub fn from_query(result: &QueryResult, reason: Option<String>) -> Self {
        let verdict = Verdict::from(result);
        Self {
            allowed: matches!(verdict, Verdict::True),
            verdict,
            reason,
            fields: Vec::new(),
        }
    }
}

/// Decision plus optional proof JSON (explain path only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Explained {
    pub decision: Decision,
    pub proof_json: Option<String>,
}
