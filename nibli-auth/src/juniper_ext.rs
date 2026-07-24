//! Thin juniper guards (`juniper` feature).

use crate::tls;

/// Return `Ok(())` if authorized, else a juniper field error.
pub fn ensure_can(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> Result<(), juniper::FieldError> {
    match tls::can(agent, action, object, context_kr) {
        Ok(d) if d.allowed => Ok(()),
        Ok(d) => Err(juniper::FieldError::new(
            format!("forbidden: {:?}", d.verdict),
            graphql_value_null(),
        )),
        Err(e) => Err(juniper::FieldError::new(e.message, graphql_value_null())),
    }
}

fn graphql_value_null() -> juniper::Value {
    juniper::Value::Null
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tls::reset_thread_auth;

    #[test]
    fn ensure_allows_owner() {
        reset_thread_auth();
        ensure_can("Alice", "read", "Doc1", "owns(Alice, Doc1).").unwrap();
    }

    #[test]
    fn ensure_denies_stranger() {
        reset_thread_auth();
        assert!(ensure_can("Bob", "update", "Doc1", "owns(Alice, Doc1).").is_err());
    }
}
