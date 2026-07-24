//! Axum extractors and rejection helpers (`axum` feature).
//!
//! Uses [`crate::tls`] so each worker thread keeps a warm policy-loaded
//! authorizer. Prefer per-request `context_kr` for owns/roles (app DB).

use axum::extract::FromRequestParts;
use axum::http::{header::HeaderValue, request::Parts, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::Json;
use serde::Serialize;

use crate::tls;
use crate::{AuthError, Decision};

/// Agent identity extracted from the `X-Agent` request header.
#[derive(Debug, Clone)]
pub struct Agent(pub String);

impl<S> FromRequestParts<S> for Agent
where
    S: Send + Sync,
{
    type Rejection = AuthRejection;

    async fn from_request_parts(parts: &mut Parts, _state: &S) -> Result<Self, Self::Rejection> {
        let raw = parts
            .headers
            .get("x-agent")
            .and_then(|v| v.to_str().ok())
            .map(str::trim)
            .filter(|s| !s.is_empty());
        match raw {
            Some(s) => Ok(Agent(s.to_string())),
            None => Err(AuthRejection::missing_agent()),
        }
    }
}

/// 403/401 rejection with a small JSON body.
#[derive(Debug)]
pub struct AuthRejection {
    status: StatusCode,
    body: AuthErrorBody,
}

#[derive(Debug, Serialize)]
pub struct AuthErrorBody {
    pub allowed: bool,
    pub verdict: String,
    pub reason: Option<String>,
}

impl AuthRejection {
    pub fn missing_agent() -> Self {
        Self {
            status: StatusCode::UNAUTHORIZED,
            body: AuthErrorBody {
                allowed: false,
                verdict: "MISSING_AGENT".into(),
                reason: Some("missing X-Agent header".into()),
            },
        }
    }

    pub fn forbidden(decision: &Decision) -> Self {
        Self {
            status: StatusCode::FORBIDDEN,
            body: AuthErrorBody {
                allowed: decision.allowed,
                verdict: format!("{:?}", decision.verdict).to_uppercase(),
                reason: decision.reason.clone(),
            },
        }
    }

    pub fn from_auth_error(e: AuthError) -> Self {
        Self {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            body: AuthErrorBody {
                allowed: false,
                verdict: "ERROR".into(),
                reason: Some(e.message),
            },
        }
    }
}

impl IntoResponse for AuthRejection {
    fn into_response(self) -> Response {
        (self.status, Json(self.body)).into_response()
    }
}

/// Require `agent` may perform `action` on `object` under `context_kr`.
pub fn require(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> Result<Decision, AuthRejection> {
    match tls::can(agent, action, object, context_kr) {
        Ok(d) if d.allowed => Ok(d),
        Ok(d) => Err(AuthRejection::forbidden(&d)),
        Err(e) => Err(AuthRejection::from_auth_error(e)),
    }
}

/// Field mask after a successful row-level allow (or empty if denied).
pub fn field_mask(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
    candidates: &[&str],
) -> Result<Vec<String>, AuthRejection> {
    tls::allowed_fields(agent, action, object, context_kr, candidates)
        .map_err(AuthRejection::from_auth_error)
}

/// Helper: parse agent from a raw header value (for tests / non-extractor paths).
pub fn agent_from_header(value: Option<&HeaderValue>) -> Result<String, AuthRejection> {
    value
        .and_then(|v| v.to_str().ok())
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .ok_or_else(AuthRejection::missing_agent)
}
