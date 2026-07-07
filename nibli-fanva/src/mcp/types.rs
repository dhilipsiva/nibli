//! Value objects + the error enum for the MCP client. All-target (no I/O), so
//! they are usable and testable on native.

use serde_json::Value;

/// A failure from the MCP client. `Unavailable` is the graceful-degradation path
/// (no proxy configured, or a native build where the transport is a stub) — the
/// translator treats it as "jbotci off", never a hard error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum McpError {
    /// No proxy URL configured, or called on a non-wasm build.
    Unavailable,
    /// Transport failure (fetch/network/CORS, or reading the body).
    Network(String),
    /// A non-success HTTP status. `Display` interprets the common ones (429/403/5xx)
    /// into an actionable message; the rest fall back to the bare code.
    Http(u16),
    /// The session expired (HTTP 404 on a request carrying a session id).
    SessionExpired,
    /// A JSON-RPC error object in the response (`{code, message}`).
    Rpc { code: i64, message: String },
    /// The response body / SSE frame couldn't be parsed as a JSON-RPC response.
    Parse(String),
}

impl std::fmt::Display for McpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            McpError::Unavailable => write!(f, "MCP unavailable (no proxy configured)"),
            McpError::Network(m) => write!(f, "MCP network error: {m}"),
            McpError::Http(c) => match *c {
                429 => write!(f, "jbotci rate-limited (HTTP 429) — wait and retry"),
                403 => write!(
                    f,
                    "jbotci refused the request (HTTP 403) — check the proxy's allowed origin"
                ),
                500..=599 => write!(
                    f,
                    "jbotci had a server error (HTTP {c}) — try again shortly"
                ),
                _ => write!(f, "jbotci returned HTTP {c}"),
            },
            McpError::SessionExpired => write!(f, "MCP session expired"),
            McpError::Rpc { code, message } => write!(f, "MCP error {code}: {message}"),
            McpError::Parse(m) => write!(f, "MCP parse error: {m}"),
        }
    }
}

/// One tool advertised by `tools/list`. `input_schema` is the raw JSON Schema,
/// mapped into each provider's tool format in Phase 3.
#[derive(Clone, Debug, PartialEq)]
pub struct ToolInfo {
    pub name: String,
    pub description: String,
    pub input_schema: Value,
}

/// The outcome of a `tools/call`. A tool-execution failure is `is_error = true`
/// (not an `McpError`) so the LLM can see it and self-correct.
#[derive(Clone, Debug, PartialEq)]
pub struct ToolCallResult {
    pub text: String,
    pub is_error: bool,
    pub structured: Option<Value>,
}

/// The `initialize` result — minimal server identity for logging / smoke checks.
#[derive(Clone, Debug, PartialEq)]
pub struct InitializeResult {
    pub server_name: String,
    pub server_version: String,
    pub protocol_version: String,
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::McpError;

    #[test]
    fn http_status_messages_are_actionable() {
        // A proxy/jbotci 429 (or 5xx / 403) should read as an actionable message, not
        // a bare "MCP HTTP 429" — this is what the tersmu view + tool loop surface.
        assert!(McpError::Http(429).to_string().contains("rate-limited"));
        assert!(McpError::Http(503).to_string().contains("server error"));
        assert!(McpError::Http(500).to_string().contains("server error"));
        assert!(McpError::Http(403).to_string().contains("allowed origin"));
        // An uninterpreted status falls back to the bare code.
        assert!(McpError::Http(418).to_string().contains("418"));
    }
}
