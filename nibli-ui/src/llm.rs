//! Client-side, bring-your-own-key LLM translation (English → Lojban).
//!
//! TRANSPARENCY GUARANTEE: this is the entire network surface of the app. The
//! user's API key is held only in a Dioxus signal in `main.rs` (never written to
//! localStorage/sessionStorage/disk) and is passed here per-call. The request
//! goes DIRECTLY from the browser to the chosen provider — nibli has no server and
//! no proxy. Inspect the `build_request` function below and the browser DevTools
//! Network tab: the only outbound call is to the provider's own endpoint.
//!
//! The translation is a DRAFT outside the reasoning firewall — the user reviews
//! the Lojban (and its back-translation) before the deterministic engine reasons
//! over it. LLMs can hallucinate; that is why the UI warns and shows the gloss.

use gloo_net::http::Request;
use serde_json::{Value, json};

/// The proven English→Lojban prompt, recovered verbatim from the (now-deleted)
/// nibli-server Ollama path. Kept intact so translation quality matches.
const LOJBAN_SYSTEM_PROMPT: &str = r#"You are a Lojban translator. Translate the user's English text into grammatically correct Lojban.

Rules:
- Output ONLY the Lojban translation, nothing else. No explanations, no notes.
- Use standard Lojban grammar: [sumti] [selbri] [sumti] structure
- Use gadri: "lo" for veridical descriptions, "le" for non-veridical
- Wrap names in dots as cmevla: "Adam" → ".adam."
- Use "cu" to separate sumti from selbri when needed
- Use tense markers: "pu" (past), "ca" (present), "ba" (future)

Examples:
- "The dog goes to the market" → "lo gerku cu klama lo zarci"
- "I love you" → "mi prami do"
- "Adam sees the cat" → "la .adam. viska lo mlatu"
- "The big dog runs" → "lo barda gerku cu bajra"
- "I ate the food" → "mi pu citka lo cidja""#;

// ── Provider + config ──────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Provider {
    Anthropic,
    OpenAi,
    OpenRouter,
    Gemini,
    /// Any OpenAI-compatible endpoint (Groq, Together, Ollama, LM Studio, …).
    Custom,
}

impl Provider {
    pub const ALL: [Provider; 5] = [
        Provider::Anthropic,
        Provider::OpenAi,
        Provider::OpenRouter,
        Provider::Gemini,
        Provider::Custom,
    ];

    pub fn display_name(self) -> &'static str {
        match self {
            Provider::Anthropic => "Anthropic",
            Provider::OpenAi => "OpenAI",
            Provider::OpenRouter => "OpenRouter",
            Provider::Gemini => "Google Gemini",
            Provider::Custom => "Custom (OpenAI-compatible)",
        }
    }

    /// Short tab label for the segmented picker.
    pub fn short_name(self) -> &'static str {
        match self {
            Provider::Anthropic => "Anthropic",
            Provider::OpenAi => "OpenAI",
            Provider::OpenRouter => "OpenRouter",
            Provider::Gemini => "Gemini",
            Provider::Custom => "Custom",
        }
    }

    pub fn default_model(self) -> &'static str {
        match self {
            Provider::Anthropic => "claude-haiku-4-5",
            Provider::OpenAi => "gpt-4o-mini",
            Provider::OpenRouter => "openai/gpt-4o-mini",
            Provider::Gemini => "gemini-2.0-flash",
            Provider::Custom => "",
        }
    }

    /// Only `Custom` exposes an editable base URL.
    pub fn needs_base_url(self) -> bool {
        matches!(self, Provider::Custom)
    }

    pub fn default_base_url(self) -> &'static str {
        match self {
            Provider::Custom => "http://localhost:11434/v1",
            _ => "",
        }
    }
}

/// In-memory only. Never persisted — see the module docs.
#[derive(Clone, PartialEq)]
pub struct LlmConfig {
    pub provider: Provider,
    pub api_key: String,
    pub model: String,
    /// Used only by `Provider::Custom`.
    pub base_url: String,
}

impl LlmConfig {
    pub fn new(provider: Provider) -> Self {
        LlmConfig {
            provider,
            api_key: String::new(),
            model: provider.default_model().to_string(),
            base_url: provider.default_base_url().to_string(),
        }
    }

    /// Resolve the effective model (fall back to the provider default if blank).
    fn effective_model(&self) -> String {
        let m = self.model.trim();
        if m.is_empty() {
            self.provider.default_model().to_string()
        } else {
            m.to_string()
        }
    }
}

// ── Errors ─────────────────────────────────────────────────────────────────

pub enum TranslateError {
    EmptyInput,
    /// fetch failed before a response — usually network or a CORS rejection.
    Network(Provider, String),
    Auth(Provider),
    /// 400/404/422 — bad model id, malformed endpoint, etc.
    BadRequest(Provider, String),
    RateLimited(Provider),
    Server(Provider, u16),
    Parse(Provider),
    EmptyResult(Provider),
}

impl std::fmt::Display for TranslateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranslateError::EmptyInput => {
                write!(f, "Nothing to translate — type some English first.")
            }
            TranslateError::Network(p, detail) => write!(
                f,
                "Couldn't reach {}. Check your connection and endpoint — some providers block direct browser (CORS) requests. ({detail})",
                p.display_name()
            ),
            TranslateError::Auth(p) => write!(
                f,
                "{} rejected the API key. Check the key is correct and has access to this model.",
                p.display_name()
            ),
            TranslateError::BadRequest(p, msg) => {
                write!(f, "{} rejected the request: {}", p.display_name(), msg)
            }
            TranslateError::RateLimited(p) => {
                write!(
                    f,
                    "{} rate-limited the request — wait a moment and retry.",
                    p.display_name()
                )
            }
            TranslateError::Server(p, code) => {
                write!(
                    f,
                    "{} had a server error ({}). Try again shortly.",
                    p.display_name(),
                    code
                )
            }
            TranslateError::Parse(p) => {
                write!(
                    f,
                    "Couldn't parse {}'s response — unexpected format.",
                    p.display_name()
                )
            }
            TranslateError::EmptyResult(p) => {
                write!(f, "{} returned an empty translation.", p.display_name())
            }
        }
    }
}

// ── Translate ──────────────────────────────────────────────────────────────

/// Translate one block of English into Lojban via the configured provider.
/// Returns the cleaned Lojban (markdown fences stripped, trimmed).
pub async fn translate(cfg: &LlmConfig, english: &str) -> Result<String, TranslateError> {
    let english = english.trim();
    if english.is_empty() {
        return Err(TranslateError::EmptyInput);
    }
    let provider = cfg.provider;
    let user_msg = format!("Translate to Lojban: {english}");
    let (url, headers, body) = build_request(cfg, &user_msg);

    // content-type is constant; provider-specific auth/version headers follow.
    let mut builder = Request::post(&url).header("content-type", "application/json");
    for (name, value) in &headers {
        builder = builder.header(name, value);
    }
    let request = builder
        .body(body.to_string())
        .map_err(|e| TranslateError::Network(provider, e.to_string()))?;
    let resp = request
        .send()
        .await
        .map_err(|e| TranslateError::Network(provider, e.to_string()))?;

    let status = resp.status();
    let raw_body = resp.text().await.unwrap_or_default();

    if !(200..300).contains(&status) {
        return Err(classify_http(provider, status, &raw_body));
    }

    let json: Value =
        serde_json::from_str(&raw_body).map_err(|_| TranslateError::Parse(provider))?;
    let text = extract_text(provider, &json).ok_or(TranslateError::Parse(provider))?;
    let cleaned = clean_lojban_output(&text);
    if cleaned.is_empty() {
        return Err(TranslateError::EmptyResult(provider));
    }
    Ok(cleaned)
}

/// Build (url, extra headers, json body) for the provider. `content-type` is
/// added by the caller. This is the ONLY place an outbound URL is formed — the
/// destination is always the provider's own host, never a nibli endpoint.
fn build_request(cfg: &LlmConfig, user_msg: &str) -> (String, Vec<(&'static str, String)>, Value) {
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
            // No `temperature` — sampling params 400 on Opus 4.x / Fable.
            let body = json!({
                "model": model,
                "max_tokens": 1024,
                "system": LOJBAN_SYSTEM_PROMPT,
                "messages": [{ "role": "user", "content": user_msg }],
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
            let body = json!({
                "systemInstruction": { "parts": [{ "text": LOJBAN_SYSTEM_PROMPT }] },
                "contents": [{ "role": "user", "parts": [{ "text": user_msg }] }],
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
            let body = json!({
                "model": model,
                "max_tokens": 1024,
                "messages": [
                    { "role": "system", "content": LOJBAN_SYSTEM_PROMPT },
                    { "role": "user", "content": user_msg },
                ],
            });
            (url, headers, body)
        }
    }
}

/// Pull the assistant text out of a successful response per provider.
fn extract_text(provider: Provider, json: &Value) -> Option<String> {
    let s = match provider {
        Provider::Anthropic => json["content"][0]["text"].as_str(),
        Provider::Gemini => json["candidates"][0]["content"]["parts"][0]["text"].as_str(),
        Provider::OpenAi | Provider::OpenRouter | Provider::Custom => {
            json["choices"][0]["message"]["content"].as_str()
        }
    };
    s.map(|s| s.to_string())
}

/// Map a non-2xx response to a friendly error, pulling the provider's own error
/// message where present (all five nest it under `error.message`).
fn classify_http(provider: Provider, status: u16, body: &str) -> TranslateError {
    let provider_msg = serde_json::from_str::<Value>(body)
        .ok()
        .and_then(|v| v["error"]["message"].as_str().map(|s| s.to_string()));
    match status {
        401 | 403 => TranslateError::Auth(provider),
        429 => TranslateError::RateLimited(provider),
        400 | 404 | 422 => TranslateError::BadRequest(
            provider,
            provider_msg
                .unwrap_or_else(|| "check the model id and (for Custom) the base URL".to_string()),
        ),
        500..=599 => TranslateError::Server(provider, status),
        _ => TranslateError::BadRequest(
            provider,
            provider_msg.unwrap_or_else(|| format!("HTTP {status}")),
        ),
    }
}

/// Models sometimes wrap output in a ``` / ```lojban code fence or add a trailing
/// newline despite the "output ONLY Lojban" instruction. Strip a single fence
/// pair and trim. (The old server only trimmed; browsers face chattier models.)
fn clean_lojban_output(raw: &str) -> String {
    let mut s = raw.trim();
    if let Some(rest) = s.strip_prefix("```") {
        // Drop the rest of the opening fence line (e.g. "```lojban\n…").
        let rest = rest.splitn(2, '\n').nth(1).unwrap_or("");
        s = rest.trim_end().strip_suffix("```").unwrap_or(rest).trim();
    }
    s.trim().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fence_stripping() {
        assert_eq!(
            clean_lojban_output("```lojban\nmi prami do\n```"),
            "mi prami do"
        );
        assert_eq!(clean_lojban_output("```\nmi prami do\n```"), "mi prami do");
        assert_eq!(clean_lojban_output("  mi prami do  "), "mi prami do");
        assert_eq!(clean_lojban_output("mi prami do"), "mi prami do");
    }

    #[test]
    fn extract_per_provider() {
        let anth = json!({ "content": [{ "type": "text", "text": "mi prami do" }] });
        assert_eq!(
            extract_text(Provider::Anthropic, &anth).as_deref(),
            Some("mi prami do")
        );
        let oai = json!({ "choices": [{ "message": { "content": "mi prami do" } }] });
        assert_eq!(
            extract_text(Provider::OpenAi, &oai).as_deref(),
            Some("mi prami do")
        );
        let gem =
            json!({ "candidates": [{ "content": { "parts": [{ "text": "mi prami do" }] } }] });
        assert_eq!(
            extract_text(Provider::Gemini, &gem).as_deref(),
            Some("mi prami do")
        );
    }
}
