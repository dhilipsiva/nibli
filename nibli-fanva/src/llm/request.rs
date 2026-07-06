//! Per-provider chat-request builders. Pure functions (no I/O) so they are
//! native-`cargo test`-able. This is the ONLY place an outbound URL is formed —
//! always the provider's own host, never a nibli endpoint. `content-type` is
//! added by the caller (the wasm-only HTTP send, a later phase).
//!
//! Generalizes `nibli-ui`'s single-`user_msg` `build_request` to a full [`Turn`]
//! conversation. The one cross-provider subtlety: Gemini names the assistant role
//! `"model"` and carries the system prompt in `systemInstruction`; Anthropic puts
//! `system` at the top level; the OpenAI family uses a leading `system` message.

use serde_json::{Value, json};

use super::types::{LlmConfig, Provider, Turn};

/// Build `(url, extra_headers, json_body)` for a multi-turn chat completion.
pub fn build_chat_request(
    cfg: &LlmConfig,
    system: &str,
    turns: &[Turn],
) -> (String, Vec<(&'static str, String)>, Value) {
    let model = cfg.effective_model();
    let key = cfg.api_key.trim().to_string();
    match cfg.provider {
        Provider::Anthropic => {
            let url = "https://api.anthropic.com/v1/messages".to_string();
            let headers = vec![
                ("x-api-key", key),
                ("anthropic-version", "2023-06-01".to_string()),
                // Opt the API into serving a CORS-enabled browser request.
                (
                    "anthropic-dangerous-direct-browser-access",
                    "true".to_string(),
                ),
            ];
            let messages: Vec<Value> = turns.iter().map(anthropic_msg).collect();
            // No `temperature` — sampling params 400 on Opus 4.x / Fable.
            let body = json!({
                "model": model,
                "max_tokens": cfg.max_tokens,
                "system": system,
                "messages": messages,
            });
            (url, headers, body)
        }
        Provider::Gemini => {
            // Key rides in a header, NOT the `?key=` query param — secrets never
            // belong in a URL.
            let url = format!(
                "https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
            );
            let headers = vec![("x-goog-api-key", key)];
            let contents: Vec<Value> = turns.iter().map(gemini_content).collect();
            let body = json!({
                "systemInstruction": { "parts": [{ "text": system }] },
                "contents": contents,
            });
            (url, headers, body)
        }
        // OpenAI-compatible chat-completions: OpenAI, OpenRouter, and Custom.
        Provider::OpenAi | Provider::OpenRouter | Provider::Custom => {
            let url = match cfg.provider {
                Provider::OpenAi => "https://api.openai.com/v1/chat/completions".to_string(),
                Provider::OpenRouter => "https://openrouter.ai/api/v1/chat/completions".to_string(),
                // Custom: append the standard path to the user's base URL.
                _ => format!(
                    "{}/chat/completions",
                    cfg.base_url.trim().trim_end_matches('/')
                ),
            };
            let mut headers: Vec<(&'static str, String)> = Vec::new();
            // A local OpenAI-compatible server may need no key — omit when blank.
            if !key.is_empty() {
                headers.push(("authorization", format!("Bearer {key}")));
            }
            if cfg.provider == Provider::OpenRouter {
                headers.push(("x-title", "nibli".to_string()));
            }
            let mut messages: Vec<Value> = vec![json!({ "role": "system", "content": system })];
            messages.extend(turns.iter().map(openai_msg));
            let body = json!({
                "model": model,
                "max_tokens": cfg.max_tokens,
                "messages": messages,
            });
            (url, headers, body)
        }
    }
}

fn anthropic_msg(t: &Turn) -> Value {
    match t {
        Turn::User(s) => json!({ "role": "user", "content": s }),
        Turn::Assistant(s) => json!({ "role": "assistant", "content": s }),
    }
}

fn openai_msg(t: &Turn) -> Value {
    match t {
        Turn::User(s) => json!({ "role": "user", "content": s }),
        Turn::Assistant(s) => json!({ "role": "assistant", "content": s }),
    }
}

fn gemini_content(t: &Turn) -> Value {
    match t {
        // Gemini's assistant role is "model", not "assistant".
        Turn::User(s) => json!({ "role": "user", "parts": [{ "text": s }] }),
        Turn::Assistant(s) => json!({ "role": "model", "parts": [{ "text": s }] }),
    }
}

#[cfg(test)]
mod tests {
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
        // system is the first message, then the turns.
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
        // assistant → "model"
        assert_eq!(body["contents"][1]["role"].as_str(), Some("model"));
    }

    #[test]
    fn custom_appends_path_to_base_url() {
        let mut cfg = LlmConfig::new(Provider::Custom);
        cfg.base_url = "http://localhost:11434/v1/".into(); // trailing slash trimmed
        cfg.model = "llama3".into();
        let (url, _headers, _body) = build_chat_request(&cfg, "SYS", &[Turn::user("hi")]);
        assert_eq!(url, "http://localhost:11434/v1/chat/completions");
    }
}
