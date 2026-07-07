//! The MCP client: JSON-RPC over Streamable-HTTP to a configurable proxy, with
//! graceful degradation when no proxy is set. Wire shaping/parsing is the pure
//! [`wire`] module; only [`McpClient::rpc`]'s real body is wasm (gloo-net). On
//! native `rpc` is a stub returning [`McpError::Unavailable`], so the client type,
//! [`McpClient::is_available`], and all parsing are native-testable.
//!
//! jbotci (`https://jbotci.app/mcp`) 403s cross-origin browsers, so `proxy_url`
//! points at an app-owned proxy. An empty URL means "jbotci off": the translator
//! then runs on the local gates only. Wiring these tools into the LLM loop is
//! Phase 3.

use std::cell::{Cell, RefCell};

use serde_json::Value;

pub mod types;
pub mod wire;

pub use types::{InitializeResult, McpError, ToolCallResult, ToolInfo};
pub use wire::PROTOCOL_VERSION;

/// A stateful MCP client pointed at a proxy URL (empty ⇒ jbotci disabled).
pub struct McpClient {
    proxy_url: String,
    /// Echoed on every request once the server issues one. Read only by the wasm
    /// transport; unread on native (stub `rpc`).
    #[cfg_attr(not(target_arch = "wasm32"), allow(dead_code))]
    session_id: RefCell<Option<String>>,
    initialized: Cell<bool>,
    /// Monotonic JSON-RPC request id. Read only by the wasm transport.
    #[cfg_attr(not(target_arch = "wasm32"), allow(dead_code))]
    next_id: Cell<u64>,
    tools: RefCell<Vec<ToolInfo>>,
}

impl McpClient {
    pub fn new(proxy_url: impl Into<String>) -> Self {
        McpClient {
            proxy_url: proxy_url.into(),
            session_id: RefCell::new(None),
            initialized: Cell::new(false),
            next_id: Cell::new(1),
            tools: RefCell::new(Vec::new()),
        }
    }

    /// Whether jbotci tool-use is possible: a non-empty proxy URL. When false, the
    /// translator runs on the local gates only.
    pub fn is_available(&self) -> bool {
        !self.proxy_url.trim().is_empty()
    }

    /// The tools discovered by the most recent [`list_tools`](Self::list_tools)
    /// (empty until then).
    pub fn tools(&self) -> Vec<ToolInfo> {
        self.tools.borrow().clone()
    }

    /// `initialize` + the `notifications/initialized` handshake. Idempotent.
    pub async fn initialize(&self) -> Result<InitializeResult, McpError> {
        if !self.is_available() {
            return Err(McpError::Unavailable);
        }
        let result = self
            .rpc("initialize", wire::initialize_params(), false)
            .await?;
        let info = InitializeResult {
            server_name: result["serverInfo"]["name"]
                .as_str()
                .unwrap_or("")
                .to_string(),
            server_version: result["serverInfo"]["version"]
                .as_str()
                .unwrap_or("")
                .to_string(),
            protocol_version: result["protocolVersion"].as_str().unwrap_or("").to_string(),
        };
        // Best-effort: the server must not send requests before receiving this.
        let _ = self
            .rpc("notifications/initialized", Value::Null, true)
            .await;
        self.initialized.set(true);
        Ok(info)
    }

    async fn ensure_ready(&self) -> Result<(), McpError> {
        if self.initialized.get() {
            return Ok(());
        }
        self.initialize().await.map(|_| ())
    }

    /// `tools/list`, cached for later reuse.
    pub async fn list_tools(&self) -> Result<Vec<ToolInfo>, McpError> {
        self.ensure_ready().await?;
        let result = self.rpc("tools/list", serde_json::json!({}), false).await?;
        let tools = wire::parse_tools_list(&result);
        *self.tools.borrow_mut() = tools.clone();
        Ok(tools)
    }

    /// `tools/call` with the given arguments object.
    pub async fn call_tool(
        &self,
        name: &str,
        arguments: Value,
    ) -> Result<ToolCallResult, McpError> {
        self.ensure_ready().await?;
        let params = serde_json::json!({ "name": name, "arguments": arguments });
        let result = self.rpc("tools/call", params, false).await?;
        Ok(wire::parse_tool_call_result(&result))
    }

    // ── transport ────────────────────────────────────────────────────────────

    /// POST one JSON-RPC message. A notification (no id) expects HTTP 202; a
    /// request returns a JSON-or-SSE body parsed by [`wire::parse_response`].
    #[cfg(target_arch = "wasm32")]
    async fn rpc(
        &self,
        method: &str,
        params: Value,
        is_notification: bool,
    ) -> Result<Value, McpError> {
        use gloo_net::http::Request;

        if !self.is_available() {
            return Err(McpError::Unavailable);
        }
        let msg = if is_notification {
            wire::notification(method, params)
        } else {
            let id = self.next_id.get();
            self.next_id.set(id + 1);
            wire::request(id, method, params)
        };
        // Read the session id to a local BEFORE any await — never hold the borrow.
        let session = self.session_id.borrow().clone();

        let mut builder = Request::post(&self.proxy_url)
            .header("content-type", "application/json")
            .header("accept", "application/json, text/event-stream")
            .header("mcp-protocol-version", wire::PROTOCOL_VERSION);
        if let Some(sid) = &session {
            builder = builder.header("mcp-session-id", sid);
        }
        let req = builder
            .body(msg.to_string())
            .map_err(|e| McpError::Network(e.to_string()))?;
        let resp = req
            .send()
            .await
            .map_err(|e| McpError::Network(e.to_string()))?;

        let status = resp.status();
        if let Some(sid) = resp.headers().get("mcp-session-id") {
            *self.session_id.borrow_mut() = Some(sid);
        }
        if status == 404 && session.is_some() {
            *self.session_id.borrow_mut() = None;
            self.initialized.set(false);
            return Err(McpError::SessionExpired);
        }
        if is_notification {
            return if (200..300).contains(&status) {
                Ok(Value::Null)
            } else {
                Err(McpError::Http(status))
            };
        }
        if !(200..300).contains(&status) {
            return Err(McpError::Http(status));
        }
        let content_type = resp.headers().get("content-type").unwrap_or_default();
        let body = resp
            .text()
            .await
            .map_err(|e| McpError::Network(e.to_string()))?;
        wire::parse_response(&content_type, &body)
    }

    /// Native stub — the real transport is browser-only. Returns `Unavailable` so
    /// native callers/tests degrade cleanly.
    #[cfg(not(target_arch = "wasm32"))]
    async fn rpc(
        &self,
        _method: &str,
        _params: Value,
        _is_notification: bool,
    ) -> Result<Value, McpError> {
        Err(McpError::Unavailable)
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn empty_url_is_unavailable() {
        assert!(!McpClient::new("").is_available());
        assert!(!McpClient::new("   ").is_available());
        assert!(McpClient::new("https://proxy.example/mcp").is_available());
    }

    #[test]
    fn calls_degrade_when_unavailable() {
        let c = McpClient::new("");
        let r = futures::executor::block_on(
            c.call_tool("vlacku", serde_json::json!({ "query": "tavla" })),
        );
        assert_eq!(r.unwrap_err(), McpError::Unavailable);
        assert!(c.tools().is_empty());
    }
}
