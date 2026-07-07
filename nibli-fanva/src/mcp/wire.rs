//! Pure JSON-RPC 2.0 + Streamable-HTTP wire helpers — no I/O, so they build and
//! test on native. The wasm transport in `mod.rs` shapes requests with these and
//! hands raw response bodies back here to parse. Exposed as a `pub` module so the
//! helpers are part of the crate API (and Phase 3 can reuse them).

use serde_json::{Value, json};

use super::types::{McpError, ToolCallResult, ToolInfo};

/// The MCP protocol version this client speaks.
pub const PROTOCOL_VERSION: &str = "2025-06-18";

/// A JSON-RPC 2.0 request envelope (has an `id`, expects a response).
pub fn request(id: u64, method: &str, params: Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params })
}

/// A JSON-RPC 2.0 notification (no `id`; success is HTTP 202). A null `params` is
/// omitted (e.g. `notifications/initialized` takes none).
pub fn notification(method: &str, params: Value) -> Value {
    let mut m = json!({ "jsonrpc": "2.0", "method": method });
    if !params.is_null() {
        m["params"] = params;
    }
    m
}

/// The `initialize` params: our protocol version + client identity.
pub fn initialize_params() -> Value {
    json!({
        "protocolVersion": PROTOCOL_VERSION,
        "capabilities": {},
        "clientInfo": { "name": "nibli-fanva", "version": "0.1.0" },
    })
}

/// Parse a response body into the JSON-RPC `result` value. Handles both an
/// `application/json` single object and a `text/event-stream` (SSE) frame. A
/// JSON-RPC `error` object becomes `McpError::Rpc`.
pub fn parse_response(content_type: &str, body: &str) -> Result<Value, McpError> {
    let json_text = if content_type.contains("text/event-stream") {
        sse_extract(body)
            .ok_or_else(|| McpError::Parse("no JSON-RPC data event in SSE stream".into()))?
    } else {
        body.to_string()
    };
    let v: Value = serde_json::from_str(&json_text)
        .map_err(|e| McpError::Parse(format!("invalid JSON-RPC body: {e}")))?;
    if let Some(err) = v.get("error") {
        let code = err.get("code").and_then(Value::as_i64).unwrap_or(0);
        let message = err
            .get("message")
            .and_then(Value::as_str)
            .unwrap_or("unknown error")
            .to_string();
        return Err(McpError::Rpc { code, message });
    }
    v.get("result")
        .cloned()
        .ok_or_else(|| McpError::Parse("JSON-RPC response missing `result`".into()))
}

/// Pull the JSON payload of the first SSE event that looks like a JSON-RPC
/// response. Events are blank-line separated; `data:` lines within one event are
/// concatenated with newlines. Other SSE fields (`event:`/`id:`/comments) are
/// ignored.
pub fn sse_extract(body: &str) -> Option<String> {
    let mut data = String::new();
    for raw in body.lines() {
        let line = raw.strip_suffix('\r').unwrap_or(raw);
        if line.is_empty() {
            if let Some(found) = take_if_jsonrpc(&data) {
                return Some(found);
            }
            data.clear();
        } else if let Some(rest) = line.strip_prefix("data:") {
            if !data.is_empty() {
                data.push('\n');
            }
            data.push_str(rest.strip_prefix(' ').unwrap_or(rest));
        }
    }
    take_if_jsonrpc(&data)
}

/// Return the trimmed text iff it parses as a JSON-RPC response (`result`/`error`).
fn take_if_jsonrpc(data: &str) -> Option<String> {
    let trimmed = data.trim();
    if trimmed.is_empty() {
        return None;
    }
    let v: Value = serde_json::from_str(trimmed).ok()?;
    (v.get("result").is_some() || v.get("error").is_some()).then(|| trimmed.to_string())
}

/// Parse a `tools/list` result into `ToolInfo`s.
pub fn parse_tools_list(result: &Value) -> Vec<ToolInfo> {
    result
        .get("tools")
        .and_then(Value::as_array)
        .map(|arr| {
            arr.iter()
                .filter_map(|t| {
                    let name = t.get("name")?.as_str()?.to_string();
                    let description = t
                        .get("description")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                        .to_string();
                    let input_schema = t.get("inputSchema").cloned().unwrap_or(Value::Null);
                    Some(ToolInfo {
                        name,
                        description,
                        input_schema,
                    })
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Parse a `tools/call` result: join the `text` content blocks, read `isError`
/// and any `structuredContent`.
pub fn parse_tool_call_result(result: &Value) -> ToolCallResult {
    let text = result
        .get("content")
        .and_then(Value::as_array)
        .map(|arr| {
            arr.iter()
                .filter_map(|b| {
                    if b.get("type").and_then(Value::as_str) == Some("text") {
                        b.get("text").and_then(Value::as_str)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
                .join("\n")
        })
        .unwrap_or_default();
    let is_error = result
        .get("isError")
        .and_then(Value::as_bool)
        .unwrap_or(false);
    let structured = result.get("structuredContent").cloned();
    ToolCallResult {
        text,
        is_error,
        structured,
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn builds_request_and_notification_envelopes() {
        let r = request(7, "tools/list", json!({}));
        assert_eq!(r["jsonrpc"], "2.0");
        assert_eq!(r["id"], 7);
        assert_eq!(r["method"], "tools/list");
        let n = notification("notifications/initialized", Value::Null);
        assert_eq!(n["method"], "notifications/initialized");
        assert!(n.get("id").is_none());
        assert!(n.get("params").is_none()); // null params omitted
    }

    #[test]
    fn parses_json_result() {
        let body = r#"{"jsonrpc":"2.0","id":1,"result":{"ok":true}}"#;
        let r = parse_response("application/json", body).unwrap();
        assert_eq!(r["ok"], json!(true));
    }

    #[test]
    fn json_error_becomes_rpc() {
        let body = r#"{"jsonrpc":"2.0","id":1,"error":{"code":-32602,"message":"bad params"}}"#;
        match parse_response("application/json", body) {
            Err(McpError::Rpc { code, message }) => {
                assert_eq!(code, -32602);
                assert_eq!(message, "bad params");
            }
            other => panic!("expected Rpc, got {other:?}"),
        }
    }

    #[test]
    fn parses_sse_result() {
        // A minimal SSE frame carrying the JSON-RPC response.
        let body =
            "event: message\ndata: {\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"ok\":true}}\n\n";
        let r = parse_response("text/event-stream; charset=utf-8", body).unwrap();
        assert_eq!(r["ok"], json!(true));
    }

    #[test]
    fn parses_the_seven_jbotci_tools() {
        let result = json!({
            "tools": [
                {"name":"gentufa","description":"parse grammar","inputSchema":{"type":"object"}},
                {"name":"tersmu","description":"semantics","inputSchema":{"type":"object"}},
                {"name":"vlacku","description":"dictionary","inputSchema":{"type":"object"}},
                {"name":"cukta","description":"CLL","inputSchema":{"type":"object"}},
                {"name":"vlasei","description":"morphology","inputSchema":{"type":"object"}},
                {"name":"jvozba","description":"build lujvo","inputSchema":{"type":"object"}},
                {"name":"gimfihi","description":"coin gismu","inputSchema":{"type":"object"}}
            ]
        });
        let tools = parse_tools_list(&result);
        assert_eq!(tools.len(), 7);
        assert!(tools.iter().any(|t| t.name == "vlacku"));
        assert!(tools.iter().all(|t| !t.input_schema.is_null()));
    }

    #[test]
    fn parses_tool_call_text_and_error_flag() {
        let ok = json!({
            "content": [{"type":"text","text":"tavla place structure"}],
            "isError": false
        });
        let r = parse_tool_call_result(&ok);
        assert_eq!(r.text, "tavla place structure");
        assert!(!r.is_error);

        let err = json!({ "content": [{"type":"text","text":"no such word"}], "isError": true });
        assert!(parse_tool_call_result(&err).is_error);
    }
}
