//! Thin async-graphql guards (`async-graphql` feature).

use crate::tls;

/// Return `Ok(())` if `agent` may perform `action` on `object`, else a GraphQL error.
pub fn guard_can(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> Result<(), async_graphql::Error> {
    match tls::can(agent, action, object, context_kr) {
        Ok(d) if d.allowed => Ok(()),
        Ok(d) => Err(async_graphql::Error::new(format!(
            "forbidden: verdict={:?} reason={:?}",
            d.verdict, d.reason
        ))),
        Err(e) => Err(async_graphql::Error::new(e.message)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tls::reset_thread_auth;

    #[test]
    fn guard_allows_owner() {
        reset_thread_auth();
        guard_can("Alice", "read", "Doc1", "owns(Alice, Doc1).").unwrap();
    }

    #[test]
    fn guard_denies_stranger() {
        reset_thread_auth();
        assert!(guard_can("Bob", "update", "Doc1", "owns(Alice, Doc1).").is_err());
    }
}
