//! The render-time tables a proof trace carries: the author's spelling of constants (from the
//! citations and the query text) and the content of every event the trace describes.

use nibli_types::logic::ProofTrace;

/// Run `f` with both tables built from `trace` (and the query's KR when given) active.
pub(crate) fn with_trace_tables<R>(
    trace: &ProofTrace,
    source: Option<&str>,
    f: impl FnOnce() -> R,
) -> R {
    crate::spelling::with_spelling(crate::spelling::table_from(Some(trace), source), || {
        crate::abstraction::with_event_contents(trace, f)
    })
}
