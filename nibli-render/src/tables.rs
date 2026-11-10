//! Render-time spelling of constants from the trace citations and query text.
//! Event content is joined only by the checked, reachable packages in `collapse`.

use nibli_types::logic::ProofTrace;

/// Run `f` with the author's spelling from `trace` and the query's KR active.
pub(crate) fn with_trace_tables<R>(
    trace: &ProofTrace,
    source: Option<&str>,
    f: impl FnOnce() -> R,
) -> R {
    crate::spelling::with_spelling(crate::spelling::table_from(Some(trace), source), f)
}
