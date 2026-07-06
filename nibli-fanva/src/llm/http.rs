//! The concrete browser transport for [`Chat`] — wasm-only (gloo-net = fetch).
//!
//! Ports `nibli-ui/src/llm.rs`'s send + status-classification path. Native builds
//! exclude this module (see the `#[cfg]` in `mod.rs`) and use a mock `Chat`, so
//! the agent/gate/provider logic stays offline-testable. This layer only does I/O
//! + error mapping; request shaping and response extraction are the pure,
//! native-tested `build_chat_request` / `extract_text`.

use gloo_net::http::Request;
use serde_json::Value;

use super::types::{LlmConfig, Provider, Turn};
use super::{Chat, ChatError, build_chat_request, extract_text};

/// A [`Chat`] that sends directly to the configured provider from the browser.
/// The BYO key lives in `cfg` (a Dioxus signal upstream) and never leaves for a
/// nibli server — the request goes straight to the provider's own host.
pub struct HttpChat;

impl Chat for HttpChat {
    async fn chat(
        &self,
        cfg: &LlmConfig,
        system: &str,
        turns: &[Turn],
    ) -> Result<String, ChatError> {
        let provider = cfg.provider;
        let (url, headers, body) = build_chat_request(cfg, system, turns);

        // content-type is constant; provider-specific auth/version headers follow.
        let mut builder = Request::post(&url).header("content-type", "application/json");
        for (name, value) in &headers {
            builder = builder.header(name, value);
        }
        let request = builder
            .body(body.to_string())
            .map_err(|e| ChatError(format!("request build failed: {e}")))?;
        let resp = request.send().await.map_err(|e| {
            ChatError(format!(
                "couldn't reach {} — check your connection/endpoint (some providers block direct browser CORS requests): {e}",
                provider.display_name()
            ))
        })?;

        let status = resp.status();
        let raw_body = resp.text().await.unwrap_or_default();
        if !(200..300).contains(&status) {
            return Err(classify_http(provider, status, &raw_body));
        }

        let json: Value = serde_json::from_str(&raw_body).map_err(|_| {
            ChatError(format!(
                "couldn't parse {}'s response",
                provider.display_name()
            ))
        })?;
        // Return the RAW assistant text; the agent applies `clean_lojban_output`.
        extract_text(provider, &json)
            .ok_or_else(|| ChatError(format!("{} returned no text", provider.display_name())))
    }
}

/// Map a non-2xx response to a friendly [`ChatError`], pulling the provider's own
/// error message where present (all five nest it under `error.message`).
fn classify_http(provider: Provider, status: u16, body: &str) -> ChatError {
    let provider_msg = serde_json::from_str::<Value>(body)
        .ok()
        .and_then(|v| v["error"]["message"].as_str().map(|s| s.to_string()));
    let name = provider.display_name();
    let detail = match status {
        401 | 403 => format!("{name} rejected the API key (check the key and model access)"),
        429 => format!("{name} rate-limited the request — wait and retry"),
        400 | 404 | 422 => provider_msg.unwrap_or_else(|| {
            "bad request — check the model id and (for Custom) the base URL".into()
        }),
        500..=599 => format!("{name} had a server error ({status}) — try again shortly"),
        _ => provider_msg.unwrap_or_else(|| format!("{name} returned HTTP {status}")),
    };
    ChatError(detail)
}
