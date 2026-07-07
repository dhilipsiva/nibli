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
    /// A non-success HTTP status the client can't interpret.
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
            McpError::Http(c) => write!(f, "MCP HTTP {c}"),
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
