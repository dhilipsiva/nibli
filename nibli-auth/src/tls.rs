//! Thread-local warm [`Authorizer`] for multi-threaded async servers.
//!
//! The underlying KB uses `RefCell` and is **`!Send`**, so `Authorizer` cannot
//! live in `axum::State` or `Arc<Mutex<_>>`. Instead each OS thread loads the
//! builtin policy once. Cross-thread durable facts belong in the app DB and are
//! passed per call as `context_kr`.

use std::cell::RefCell;

use crate::{AuthError, Authorizer, Decision, Explained};

thread_local! {
    static AUTH: RefCell<Option<Authorizer>> = const { RefCell::new(None) };
}

/// Run `f` with this thread's warm authorizer (policy loaded on first use).
pub fn with_auth<R>(f: impl FnOnce(&mut Authorizer) -> Result<R, AuthError>) -> Result<R, AuthError> {
    AUTH.with(|cell| {
        let mut slot = cell.borrow_mut();
        if slot.is_none() {
            let mut a = Authorizer::new();
            a.load_policy(None)?;
            *slot = Some(a);
        }
        f(slot.as_mut().expect("authorizer just installed"))
    })
}

/// Drop this thread's authorizer (next call reloads policy). Useful in tests.
pub fn reset_thread_auth() {
    AUTH.with(|cell| {
        *cell.borrow_mut() = None;
    });
}

/// Hot-path can via thread-local authorizer.
pub fn can(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> Result<Decision, AuthError> {
    with_auth(|a| a.can(agent, action, object, context_kr))
}

/// Field mask via thread-local authorizer.
pub fn allowed_fields(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
    candidates: &[&str],
) -> Result<Vec<String>, AuthError> {
    with_auth(|a| a.allowed_fields(agent, action, object, context_kr, candidates))
}

/// Explain (proof) via thread-local authorizer.
pub fn explain(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> Result<Explained, AuthError> {
    with_auth(|a| a.explain(agent, action, object, context_kr))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tls_owner_can_update() {
        reset_thread_auth();
        let d = can("Alice", "update", "Doc1", "owns(Alice, Doc1).").unwrap();
        assert!(d.allowed, "{d:?}");
    }

    #[test]
    fn tls_stranger_denied() {
        reset_thread_auth();
        let d = can("Bob", "update", "Doc1", "owns(Alice, Doc1).").unwrap();
        assert!(!d.allowed, "{d:?}");
    }

    #[test]
    fn tls_admin_with_resource() {
        reset_thread_auth();
        let ctx = "has_role(Carol, \"admin\").\nresource(Doc1).";
        let d = can("Carol", "update", "Doc1", ctx).unwrap();
        assert!(d.allowed, "{d:?}");
    }
}
