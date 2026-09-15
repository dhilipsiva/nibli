//! Asking the loaded engine a question, with the proof.

use nibli_engine::NibliEngine;
use nibli_render::{Register, VerdictKind};
use nibli_types::logic::{QueryResult, ResourceKind, UnknownReason};

/// A verdict with its evidence.
#[derive(Debug, Clone)]
pub struct Answer {
    /// The query as asked.
    pub query: String,
    /// `TRUE`, `FALSE`, `UNKNOWN`, or `RESOURCE_EXCEEDED`.
    pub status: String,
    /// The UNKNOWN reason or the resource kind, when any.
    pub detail: Option<String>,
    /// The plain-English `[Why]` line.
    pub why: Option<String>,
    /// The compact proof text.
    pub proof: String,
    /// A FALSE that means "not derivable", not "refuted".
    pub cwa_false: bool,
    /// The verdict rests on negation as failure.
    pub naf_dependent: bool,
    /// The schema-2 proof envelope, when the query certified.
    pub envelope: Option<serde_json::Value>,
}

/// Runs `query` against `engine`.
pub fn ask(engine: &NibliEngine, query: &str) -> Result<Answer, String> {
    let (result, trace) = engine
        .query_text_raw_proof(query)
        .map_err(|e| e.to_string())?;
    let why = nibli_render::summarize_verdict(&verdict_kind_of(&result), &trace, Register::Spec);
    let proof = nibli_render::render_proof_text(&trace, Register::Spec);
    let envelope = engine.certify_text(query).ok().and_then(|envelope| {
        serde_json::from_str::<serde_json::Value>(&nibli_protocol::envelope_to_json(&envelope)).ok()
    });
    Ok(Answer {
        query: query.to_string(),
        status: result.status_label().to_string(),
        detail: result.detail_label().map(str::to_string),
        why,
        proof,
        cwa_false: trace.cwa_false,
        naf_dependent: trace.naf_dependent,
        envelope,
    })
}

/// The renderer's verdict class, so the `[Why]` line matches the verdict
/// (an UNKNOWN never reads as closed-world non-derivability).
fn verdict_kind_of(result: &QueryResult) -> VerdictKind {
    match result {
        QueryResult::True => VerdictKind::True,
        QueryResult::False => VerdictKind::False,
        QueryResult::Unknown(reason) => VerdictKind::Unknown(Some(match reason {
            UnknownReason::CycleCut => "cycle-cut",
            UnknownReason::IncompleteKnowledge => "incomplete-knowledge",
            UnknownReason::NafDependent => "naf-dependent",
            UnknownReason::BackendUnavailable => "backend-unavailable",
            UnknownReason::NonFinite => "non-finite",
        })),
        QueryResult::ResourceExceeded(kind) => VerdictKind::ResourceExceeded(Some(match kind {
            ResourceKind::Depth => "depth",
            ResourceKind::Fuel => "fuel",
            ResourceKind::Memory => "memory",
        })),
    }
}
