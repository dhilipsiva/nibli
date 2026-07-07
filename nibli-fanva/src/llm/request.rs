//! Per-provider chat-request builders. Pure functions (no I/O) so they are
//! native-`cargo test`-able. This is the ONLY place an outbound URL is formed —
//! always the provider's own host, never a nibli endpoint. `content-type` is
//! added by the caller (the wasm-only HTTP send).
//!
//! Generalizes `nibli-ui`'s single-`user_msg` `build_request` to a full [`Turn`]
//! conversation, including jbotci tool declarations + tool-call/tool-result turns.
//! Cross-provider subtleties: Gemini names the assistant role `"model"` and puts
//! the system prompt in `systemInstruction`; Anthropic puts `system` at the top
//! level; the OpenAI family uses a leading `system` message and encodes tool-call
//! `arguments` as a STRING.

use serde_json::{Value, json};

use super::types::{LlmConfig, Provider, ToolDecl, Turn};

/// Build `(url, extra_headers, json_body)` for a multi-turn chat completion (no
/// tools). A thin wrapper over [`build_chat_request_tools`].
pub fn build_chat_request(
    cfg: &LlmConfig,
    system: &str,
    turns: &[Turn],
) -> (String, Vec<(&'static str, String)>, Value) {
    build_chat_request_tools(cfg, system, turns, &[])
}

/// Like [`build_chat_request`], additionally declaring `tools` so the model can
/// call them. Tool-call/tool-result turns in `turns` are serialized in each
/// provider's native shape.
pub fn build_chat_request_tools(
    cfg: &LlmConfig,
    system: &str,
    turns: &[Turn],
    tools: &[ToolDecl],
) -> (String, Vec<(&'static str, String)>, Value) {
    let model = cfg.effective_model();
    let key = cfg.api_key.trim().to_string();
    match cfg.provider {
        Provider::Anthropic => {
            let url = "https://api.anthropic.com/v1/messages".to_string();
            let headers = vec![
                ("x-api-key", key),
                ("anthropic-version", "2023-06-01".to_string()),
                (
                    "anthropic-dangerous-direct-browser-access",
                    "true".to_string(),
                ),
            ];
            let messages: Vec<Value> = turns.iter().flat_map(anthropic_msgs).collect();
            // No `temperature` — sampling params 400 on Opus 4.x / Fable.
            let mut body = json!({
                "model": model,
                "max_tokens": cfg.max_tokens,
                "system": system,
                "messages": messages,
            });
            if !tools.is_empty() {
                body["tools"] = Value::Array(tools.iter().map(schema_to_anthropic).collect());
            }
            (url, headers, body)
        }
        Provider::Gemini => {
            let url = format!(
                "https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
            );
            let headers = vec![("x-goog-api-key", key)];
            let contents: Vec<Value> = turns.iter().flat_map(gemini_contents).collect();
            let mut body = json!({
                "systemInstruction": { "parts": [{ "text": system }] },
                "contents": contents,
            });
            if !tools.is_empty() {
                let decls: Vec<Value> = tools.iter().map(schema_to_gemini).collect();
                body["tools"] = json!([{ "functionDeclarations": decls }]);
            }
            (url, headers, body)
        }
        // OpenAI-compatible chat-completions: OpenAI, OpenRouter, and Custom.
        Provider::OpenAi | Provider::OpenRouter | Provider::Custom => {
            let url = match cfg.provider {
                Provider::OpenAi => "https://api.openai.com/v1/chat/completions".to_string(),
                Provider::OpenRouter => "https://openrouter.ai/api/v1/chat/completions".to_string(),
                _ => format!(
                    "{}/chat/completions",
                    cfg.base_url.trim().trim_end_matches('/')
                ),
            };
            let mut headers: Vec<(&'static str, String)> = Vec::new();
            if !key.is_empty() {
                headers.push(("authorization", format!("Bearer {key}")));
            }
            if cfg.provider == Provider::OpenRouter {
                headers.push(("x-title", "nibli".to_string()));
            }
            let mut messages: Vec<Value> = vec![json!({ "role": "system", "content": system })];
            messages.extend(turns.iter().flat_map(openai_msgs));
            let mut body = json!({
                "model": model,
                "max_tokens": cfg.max_tokens,
                "messages": messages,
            });
            if !tools.is_empty() {
                body["tools"] = Value::Array(tools.iter().map(schema_to_openai).collect());
            }
            (url, headers, body)
        }
    }
}

// ── tool-schema mapping (jbotci inputSchema → provider tool) ──────────────────

fn schema_to_anthropic(t: &ToolDecl) -> Value {
    json!({ "name": t.name, "description": t.description, "input_schema": t.input_schema })
}

fn schema_to_openai(t: &ToolDecl) -> Value {
    json!({
        "type": "function",
        "function": { "name": t.name, "description": t.description, "parameters": t.input_schema },
    })
}

fn schema_to_gemini(t: &ToolDecl) -> Value {
    json!({ "name": t.name, "description": t.description, "parameters": t.input_schema })
}

// ── per-turn message serialization (a turn may map to >1 message) ─────────────

fn anthropic_msgs(t: &Turn) -> Vec<Value> {
    match t {
        Turn::User(s) => vec![json!({ "role": "user", "content": s })],
        Turn::Assistant(s) => vec![json!({ "role": "assistant", "content": s })],
        Turn::AssistantTools { text, calls } => {
            let mut content: Vec<Value> = Vec::new();
            if let Some(t) = text {
                content.push(json!({ "type": "text", "text": t }));
            }
            for c in calls {
                content.push(json!({
                    "type": "tool_use", "id": c.id, "name": c.name, "input": c.args,
                }));
            }
            vec![json!({ "role": "assistant", "content": content })]
        }
        // tool_result blocks ride on a `user` message (they come first — this turn
        // holds only results).
        Turn::ToolResults(results) => {
            let content: Vec<Value> = results
                .iter()
                .map(|r| {
                    json!({
                        "type": "tool_result",
                        "tool_use_id": r.id,
                        "content": r.content,
                        "is_error": r.is_error,
                    })
                })
                .collect();
            vec![json!({ "role": "user", "content": content })]
        }
    }
}

fn openai_msgs(t: &Turn) -> Vec<Value> {
    match t {
        Turn::User(s) => vec![json!({ "role": "user", "content": s })],
        Turn::Assistant(s) => vec![json!({ "role": "assistant", "content": s })],
        Turn::AssistantTools { text, calls } => {
            let tool_calls: Vec<Value> = calls
                .iter()
                .map(|c| {
                    json!({
                        "id": c.id,
                        "type": "function",
                        // OpenAI expects `arguments` as a STRING.
                        "function": { "name": c.name, "arguments": c.args.to_string() },
                    })
                })
                .collect();
            let content = text.clone().map(Value::String).unwrap_or(Value::Null);
            vec![json!({ "role": "assistant", "content": content, "tool_calls": tool_calls })]
        }
        // One `tool` message per result.
        Turn::ToolResults(results) => results
            .iter()
            .map(|r| json!({ "role": "tool", "tool_call_id": r.id, "content": r.content }))
            .collect(),
    }
}

fn gemini_contents(t: &Turn) -> Vec<Value> {
    match t {
        // Gemini's assistant role is "model", not "assistant".
        Turn::User(s) => vec![json!({ "role": "user", "parts": [{ "text": s }] })],
        Turn::Assistant(s) => vec![json!({ "role": "model", "parts": [{ "text": s }] })],
        Turn::AssistantTools { text, calls } => {
            let mut parts: Vec<Value> = Vec::new();
            if let Some(t) = text {
                parts.push(json!({ "text": t }));
            }
            for c in calls {
                parts.push(json!({ "functionCall": { "name": c.name, "args": c.args } }));
            }
            vec![json!({ "role": "model", "parts": parts })]
        }
        // functionResponse correlates by NAME (Gemini has no call id).
        Turn::ToolResults(results) => {
            let parts: Vec<Value> = results
                .iter()
                .map(|r| {
                    json!({ "functionResponse": { "name": r.name, "response": { "content": r.content } } })
                })
                .collect();
            vec![json!({ "role": "user", "parts": parts })]
        }
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::super::types::{ToolCall, ToolResult};
    use super::*;

    fn turns() -> Vec<Turn> {
        vec![
            Turn::user("hi"),
            Turn::assistant("bad lojban"),
            Turn::user("fix it"),
        ]
    }

    #[test]
    fn anthropic_shape() {
        let cfg = LlmConfig {
            provider: Provider::Anthropic,
            api_key: "k".into(),
            model: "m".into(),
            base_url: String::new(),
            max_tokens: 512,
        };
        let (url, headers, body) = build_chat_request(&cfg, "SYS", &turns());
        assert!(url.contains("api.anthropic.com"));
        assert_eq!(body["system"].as_str(), Some("SYS")); // top-level system
        assert_eq!(body["max_tokens"].as_u64(), Some(512));
        assert_eq!(body["messages"][0]["role"].as_str(), Some("user"));
        assert_eq!(body["messages"][0]["content"].as_str(), Some("hi"));
        assert_eq!(body["messages"][1]["role"].as_str(), Some("assistant"));
        assert_eq!(body["messages"][2]["content"].as_str(), Some("fix it"));
        assert!(body.get("tools").is_none()); // no tools declared
        assert!(
            headers
                .iter()
                .any(|h| h.0 == "anthropic-dangerous-direct-browser-access")
        );
    }

    #[test]
    fn openai_shape() {
        let cfg = LlmConfig::new(Provider::OpenAi); // empty key ⇒ no auth header
        let (url, headers, body) = build_chat_request(&cfg, "SYS", &turns());
        assert!(url.contains("api.openai.com"));
        assert_eq!(body["messages"][0]["role"].as_str(), Some("system"));
        assert_eq!(body["messages"][0]["content"].as_str(), Some("SYS"));
        assert_eq!(body["messages"][1]["role"].as_str(), Some("user"));
        assert_eq!(body["messages"][3]["content"].as_str(), Some("fix it"));
        assert!(!headers.iter().any(|h| h.0 == "authorization"));
    }

    #[test]
    fn openrouter_adds_title_and_auth() {
        let mut cfg = LlmConfig::new(Provider::OpenRouter);
        cfg.api_key = "k".into();
        let (url, headers, _body) = build_chat_request(&cfg, "SYS", &turns());
        assert!(url.contains("openrouter.ai"));
        assert!(headers.iter().any(|h| h.0 == "x-title"));
        assert!(headers.iter().any(|h| h.0 == "authorization"));
    }

    #[test]
    fn gemini_shape_uses_model_role_and_system_instruction() {
        let mut cfg = LlmConfig::new(Provider::Gemini);
        cfg.api_key = "k".into();
        let (url, headers, body) = build_chat_request(&cfg, "SYS", &turns());
        assert!(url.contains("generativelanguage"));
        assert!(headers.iter().any(|h| h.0 == "x-goog-api-key"));
        assert_eq!(
            body["systemInstruction"]["parts"][0]["text"].as_str(),
            Some("SYS")
        );
        assert_eq!(body["contents"][0]["role"].as_str(), Some("user"));
        assert_eq!(body["contents"][0]["parts"][0]["text"].as_str(), Some("hi"));
        assert_eq!(body["contents"][1]["role"].as_str(), Some("model"));
    }

    #[test]
    fn custom_appends_path_to_base_url() {
        let mut cfg = LlmConfig::new(Provider::Custom);
        cfg.base_url = "http://localhost:11434/v1/".into();
        cfg.model = "llama3".into();
        let (url, _headers, _body) = build_chat_request(&cfg, "SYS", &[Turn::user("hi")]);
        assert_eq!(url, "http://localhost:11434/v1/chat/completions");
    }

    // ── tool-use serialization ──

    fn tool() -> ToolDecl {
        ToolDecl {
            name: "vlacku".into(),
            description: "dictionary".into(),
            input_schema: json!({ "type": "object" }),
        }
    }
    fn call() -> ToolCall {
        ToolCall {
            id: "c1".into(),
            name: "vlacku".into(),
            args: json!({ "query": "tavla" }),
        }
    }
    fn result() -> ToolResult {
        ToolResult {
            id: "c1".into(),
            name: "vlacku".into(),
            content: "x1 talks".into(),
            is_error: false,
        }
    }

    #[test]
    fn anthropic_declares_tools_and_serializes_tool_turns() {
        let cfg = LlmConfig::new(Provider::Anthropic);
        let turns = vec![
            Turn::user("x"),
            Turn::AssistantTools {
                text: None,
                calls: vec![call()],
            },
            Turn::ToolResults(vec![result()]),
        ];
        let (_u, _h, body) = build_chat_request_tools(&cfg, "SYS", &turns, &[tool()]);
        assert_eq!(body["tools"][0]["name"].as_str(), Some("vlacku"));
        assert!(body["tools"][0]["input_schema"].is_object());
        assert_eq!(
            body["messages"][1]["content"][0]["type"].as_str(),
            Some("tool_use")
        );
        assert_eq!(
            body["messages"][1]["content"][0]["name"].as_str(),
            Some("vlacku")
        );
        assert_eq!(body["messages"][2]["role"].as_str(), Some("user"));
        assert_eq!(
            body["messages"][2]["content"][0]["type"].as_str(),
            Some("tool_result")
        );
        assert_eq!(
            body["messages"][2]["content"][0]["tool_use_id"].as_str(),
            Some("c1")
        );
    }

    #[test]
    fn openai_tool_calls_use_stringified_args_and_tool_messages() {
        let cfg = LlmConfig::new(Provider::OpenAi);
        let turns = vec![
            Turn::AssistantTools {
                text: None,
                calls: vec![call()],
            },
            Turn::ToolResults(vec![result()]),
        ];
        let (_u, _h, body) = build_chat_request_tools(&cfg, "SYS", &turns, &[tool()]);
        assert_eq!(body["tools"][0]["type"].as_str(), Some("function"));
        assert_eq!(
            body["tools"][0]["function"]["name"].as_str(),
            Some("vlacku")
        );
        assert_eq!(body["messages"][1]["role"].as_str(), Some("assistant"));
        // arguments MUST be a string
        assert!(body["messages"][1]["tool_calls"][0]["function"]["arguments"].is_string());
        assert_eq!(body["messages"][2]["role"].as_str(), Some("tool"));
        assert_eq!(body["messages"][2]["tool_call_id"].as_str(), Some("c1"));
    }

    #[test]
    fn gemini_function_declarations_and_response_by_name() {
        let cfg = LlmConfig::new(Provider::Gemini);
        let turns = vec![
            Turn::AssistantTools {
                text: None,
                calls: vec![call()],
            },
            Turn::ToolResults(vec![result()]),
        ];
        let (_u, _h, body) = build_chat_request_tools(&cfg, "SYS", &turns, &[tool()]);
        assert_eq!(
            body["tools"][0]["functionDeclarations"][0]["name"].as_str(),
            Some("vlacku")
        );
        assert_eq!(body["contents"][0]["role"].as_str(), Some("model"));
        assert_eq!(
            body["contents"][0]["parts"][0]["functionCall"]["name"].as_str(),
            Some("vlacku")
        );
        assert_eq!(
            body["contents"][1]["parts"][0]["functionResponse"]["name"].as_str(),
            Some("vlacku")
        );
    }
}
