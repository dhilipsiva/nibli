//! Per-thread native compute-backend dispatch for the engine.
//!
//! nibli-reason's per-KB dispatch hook is a bare `fn` pointer (Copy, no capture), so the
//! connection cannot live on the closure. It lives in a `thread_local!` here in
//! the EMBEDDER (keeping nibli-reason global-state-free); the bare `native_eval_fn` /
//! `native_batch_eval_fn` read it. nibli-server runs reasoning in per-thread
//! `spawn_blocking` workers, so the connection is per-worker (pooling, no races).
//!
//! The TCP client itself (connect / dispatch / batch + the JSON-Lines wire types)
//! is shared with nibli-host in `nibli_protocol::compute_client`. This module only
//! holds the thread-local and converts the engine's `LogicalTerm` to `BackendArg`.

use std::cell::RefCell;

use nibli_protocol::compute_client::{BackendArg, BackendClient, BackendRequest};

use crate::{EngineComputeRequest, EngineLogicalTerm};

fn term_to_arg(term: &EngineLogicalTerm) -> BackendArg {
    match term {
        EngineLogicalTerm::Variable(s) => BackendArg::Variable(s.clone()),
        EngineLogicalTerm::Constant(s) => BackendArg::Constant(s.clone()),
        EngineLogicalTerm::Description(s) => BackendArg::Description(s.clone()),
        EngineLogicalTerm::Unspecified => BackendArg::Unspecified,
        EngineLogicalTerm::Number(n) => BackendArg::Number(*n),
    }
}

thread_local! {
    static CLIENT: RefCell<BackendClient> = const { RefCell::new(BackendClient::new()) };
}

/// Point this thread's client at `addr`, dropping any stale connection if the
/// address changed. Called by `NibliEngine::enable_compute_backend`.
pub(crate) fn set_addr(addr: &str) {
    CLIENT.with(|c| c.borrow_mut().set_addr(addr));
}

/// The single-predicate `EvalFn` registered on the KB.
pub(crate) fn native_eval_fn(rel: &str, args: &[EngineLogicalTerm]) -> Result<bool, String> {
    let args: Vec<BackendArg> = args.iter().map(term_to_arg).collect();
    CLIENT.with(|c| c.borrow_mut().dispatch(rel, &args))
}

/// The batch `BatchEvalFn` registered on the KB.
pub(crate) fn native_batch_eval_fn(requests: &[EngineComputeRequest]) -> Vec<Result<bool, String>> {
    let reqs: Vec<BackendRequest> = requests
        .iter()
        .map(|r| BackendRequest {
            relation: r.relation.clone(),
            args: r.args.iter().map(term_to_arg).collect(),
        })
        .collect();
    CLIENT.with(|c| c.borrow_mut().dispatch_batch(&reqs))
}
