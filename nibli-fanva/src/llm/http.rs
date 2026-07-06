//! The concrete transport for [`Chat`].
//!
//! In the browser (wasm) it sends via gloo-net (fetch) straight to the provider —
//! the BYO key never leaves for a nibli server. On native targets `HttpChat` still
//! exists (so downstream crates like `nibli-ui` type-check for the host toolchain)
//! but its `chat()` returns an error: real sends only happen in the browser, and
//! native tests use a mock `Chat`.
//!
//! Request shaping / response extraction are the pure, native-tested
//! `build_chat_request` / `extract_text`; this layer is only I/O + error mapping.

use super::types::{LlmConfig, Turn};
use super::{Chat, ChatError};

#[cfg(target_arch = "wasm32")]
use super::types::Provider;
#[cfg(target_arch = "wasm32")]
use super::{build_chat_request, extract_text};

/// A [`Chat`] that sends directly to the configured provider from the browser.
/// The BYO key lives in `cfg` (a Dioxus signal upstream) and never leaves for a
/// nibli server — the request goes straight to the provider's own host.
pub struct HttpChat;

impl Chat for HttpChat {
    #[cfg(target_arch = "wasm32")]
    async fn chat(
        &self,
        cfg: &LlmConfig,
        system: &str,
        turns: &[Turn],
    ) -> Result<String, ChatError> {
        use gloo_net::http::Request;
        use serde_json::Value;

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

    // Native stub: `HttpChat` exists for the host toolchain (so `nibli-ui` type-
    // checks under `cargo check --workspace`) but only sends in the browser.
    #[cfg(not(target_arch = "wasm32"))]
    async fn chat(
        &self,
        _cfg: &LlmConfig,
        _system: &str,
        _turns: &[Turn],
    ) -> Result<String, ChatError> {
        Err(ChatError(
            "HttpChat sends only run in the browser (wasm); native code should use a mock Chat"
                .into(),
        ))
    }
}

/// Map a non-2xx response to a friendly [`ChatError`], pulling the provider's own
/// error message where present (all five nest it under `error.message`).
#[cfg(target_arch = "wasm32")]
fn classify_http(provider: Provider, status: u16, body: &str) -> ChatError {
    use serde_json::Value;
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
