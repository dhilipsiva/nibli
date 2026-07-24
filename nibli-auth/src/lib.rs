//! Built-in authorization over a long-lived nibli session core.
//!
//! - Policy is loaded once (`load_policy`).
//! - Per-call context KR is asserted, queried, then retracted (ephemeral).
//! - Hot path (`can`, `allowed_fields`) never builds proofs; use `explain`.
//! - Session KB is `!Send`; hold one [`Authorizer`] per thread / serial path.
//! - Depends on `nibli-session` (not `nibli-engine`) so the WASM pipeline can
//!   link without `redb` / host-only store.

mod cache;
mod decision;
mod kr;

pub use decision::{Decision, Explained, Verdict};

use cache::{hash_context, CacheKey, DecisionCache};
use nibli_session::CoreSession;
use nibli_types::error::NibliError;

/// Builtin policy version string (also embedded in the policy file header).
pub const POLICY_VERSION: &str = "0.1.0";

/// Builtin authorization rules (`policy/auth-0.1.0.nibli`).
pub const BUILTIN_POLICY: &str = include_str!("../policy/auth-0.1.0.nibli");

/// Auth-layer error (wraps session errors + local state errors).
#[derive(Debug)]
pub struct AuthError {
    pub message: String,
}

impl std::fmt::Display for AuthError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for AuthError {}

impl From<NibliError> for AuthError {
    fn from(e: NibliError) -> Self {
        Self {
            message: e.to_string(),
        }
    }
}

impl AuthError {
    fn msg(s: impl Into<String>) -> Self {
        Self {
            message: s.into(),
        }
    }
}

/// Long-lived authorizer: one session core, policy once, ephemeral context, decision cache.
pub struct Authorizer {
    core: CoreSession,
    policy_version: String,
    policy_loaded: bool,
    cache: DecisionCache,
    /// Fact ids from the last context assert (for clear_ephemeral).
    ephemeral_ids: Vec<u64>,
}

impl Default for Authorizer {
    fn default() -> Self {
        Self::new()
    }
}

impl Authorizer {
    pub fn new() -> Self {
        let core = CoreSession::new();
        core.set_verbose(false);
        Self {
            core,
            policy_version: POLICY_VERSION.to_string(),
            policy_loaded: false,
            cache: DecisionCache::default(),
            ephemeral_ids: Vec::new(),
        }
    }

    /// Assert builtin policy (+ optional overlay KR). Clears the decision cache.
    /// Returns the active policy version string.
    pub fn load_policy(&mut self, extra_kr: Option<&str>) -> Result<String, AuthError> {
        self.clear_ephemeral_inner();
        self.cache.clear();
        // Fresh core so reloads do not stack duplicate rules.
        self.core = CoreSession::new();
        self.core.set_verbose(false);
        self.assert_text_ids(BUILTIN_POLICY)?;
        if let Some(extra) = extra_kr {
            if !extra.trim().is_empty() {
                self.assert_text_ids(extra)?;
            }
        }
        self.policy_loaded = true;
        self.policy_version = POLICY_VERSION.to_string();
        Ok(self.policy_version.clone())
    }

    pub fn policy_version(&self) -> &str {
        &self.policy_version
    }

    pub fn policy_loaded(&self) -> bool {
        self.policy_loaded
    }

    /// Assert durable KR facts (not auto-retracted). Invalidates the decision cache.
    pub fn assert_facts(&mut self, kr: &str) -> Result<Vec<u64>, AuthError> {
        self.ensure_policy()?;
        self.cache.clear();
        self.assert_text_ids(kr)
    }

    pub fn retract(&mut self, id: u64) -> Result<(), AuthError> {
        self.cache.clear();
        self.core.retract_fact(id)?;
        Ok(())
    }

    /// Hot path: is `agent` authorized for `action` on `resource`?
    /// `context_kr` is asserted then retracted (ephemeral).
    pub fn can(
        &mut self,
        agent: &str,
        action: &str,
        resource: &str,
        context_kr: &str,
    ) -> Result<Decision, AuthError> {
        self.ensure_policy()?;
        let key = self.cache_key(agent, action, resource, context_kr);
        if let Some(hit) = self.cache.get(&key) {
            return Ok(hit);
        }
        let decision = self.with_context(context_kr, |auth| {
            let q = kr::authorized_query(agent, action, resource);
            let result = auth.core.query_text(&q)?;
            Ok(Decision::from_query(
                &result,
                Some(result.status_label().to_string()),
            ))
        })?;
        self.cache.insert(key, decision.clone());
        Ok(decision)
    }

    /// Field-level allow list for serializer masking.
    ///
    /// v0.1: if `authorized(agent, action, resource)` is TRUE, return all
    /// `candidates`. Default `action` for masking is typically `"read"`.
    pub fn allowed_fields(
        &mut self,
        agent: &str,
        action: &str,
        resource: &str,
        context_kr: &str,
        candidates: &[&str],
    ) -> Result<Vec<String>, AuthError> {
        let decision = self.can(agent, action, resource, context_kr)?;
        if decision.allowed {
            Ok(candidates.iter().map(|s| (*s).to_string()).collect())
        } else {
            Ok(Vec::new())
        }
    }

    /// Like `can`, but includes a proof JSON string when available.
    pub fn explain(
        &mut self,
        agent: &str,
        action: &str,
        resource: &str,
        context_kr: &str,
    ) -> Result<Explained, AuthError> {
        self.ensure_policy()?;
        self.with_context(context_kr, |auth| {
            let q = kr::authorized_query(agent, action, resource);
            let (result, trace) = auth.core.query_text_with_proof(&q)?;
            let decision = Decision::from_query(&result, Some(result.status_label().to_string()));
            let proof_json = Some(nibli_protocol::proof_trace_to_json(&trace));
            Ok(Explained {
                decision,
                proof_json,
            })
        })
    }

    /// Retract any leftover ephemeral context fact ids.
    pub fn clear_ephemeral(&mut self) -> Result<(), AuthError> {
        self.clear_ephemeral_inner();
        Ok(())
    }

    fn assert_text_ids(&self, kr: &str) -> Result<Vec<u64>, AuthError> {
        let pairs = self.core.assert_text(kr)?;
        Ok(pairs.into_iter().map(|(id, _)| id).collect())
    }

    fn ensure_policy(&self) -> Result<(), AuthError> {
        if self.policy_loaded {
            Ok(())
        } else {
            Err(AuthError::msg(
                "policy not loaded; call load_policy() first",
            ))
        }
    }

    fn cache_key(
        &self,
        agent: &str,
        action: &str,
        resource: &str,
        context_kr: &str,
    ) -> CacheKey {
        CacheKey {
            policy_version: self.policy_version.clone(),
            agent: agent.to_string(),
            action: action.to_string(),
            resource: resource.to_string(),
            context_hash: hash_context(context_kr),
        }
    }

    fn clear_ephemeral_inner(&mut self) {
        for id in self.ephemeral_ids.drain(..) {
            let _ = self.core.retract_fact(id);
        }
    }

    /// Assert context (if any), run `f`, always retract context ids.
    fn with_context<T>(
        &mut self,
        context_kr: &str,
        f: impl FnOnce(&mut Self) -> Result<T, AuthError>,
    ) -> Result<T, AuthError> {
        self.clear_ephemeral_inner();
        if !context_kr.trim().is_empty() {
            match self.assert_text_ids(context_kr) {
                Ok(ids) => self.ephemeral_ids = ids,
                Err(e) => return Err(e),
            }
        }
        let result = f(self);
        self.clear_ephemeral_inner();
        result
    }
}
