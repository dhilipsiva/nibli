//! Provider selection, per-call config, and the provider-agnostic conversation
//! model. Ported from `nibli-ui/src/llm.rs` (BYO-key, direct-to-provider) and
//! generalized: the single user message becomes a [`Turn`] sequence.

use serde_json::Value;

/// A supported LLM provider. `Custom` is any OpenAI-compatible endpoint
/// (Groq, Together, Ollama, LM Studio, …).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Provider {
    Anthropic,
    OpenAi,
    OpenRouter,
    Gemini,
    Custom,
}

/// UI promotion metadata for a provider we recommend as the easy, free, and
/// browser-direct path (works without a CORS proxy). `None` otherwise.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProviderPromo {
    /// Short badge shown on the picker tab (e.g. "free").
    pub badge: &'static str,
    /// One short line shown under the picker when this provider is selected.
    pub note: &'static str,
    /// "Get a key" signup link for the note.
    pub signup_url: &'static str,
}

impl Provider {
    pub const ALL: [Provider; 5] = [
        Provider::OpenRouter,
        Provider::Gemini,
        Provider::Anthropic,
        Provider::OpenAi,
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

    /// Short tab label for a segmented picker.
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
            Provider::OpenRouter => "meta-llama/llama-3.3-70b-instruct:free",
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

    /// Promotion metadata for the recommended free/easy providers that work
    /// directly from the browser (no CORS proxy needed). `None` otherwise.
    pub fn promo(self) -> Option<ProviderPromo> {
        match self {
            Provider::OpenRouter => Some(ProviderPromo {
                badge: "free",
                note: "Easiest to start \u{2014} free models, no credit card. One key, many models.",
                signup_url: "https://openrouter.ai/keys",
            }),
            Provider::Gemini => Some(ProviderPromo {
                badge: "free",
                note: "Easiest to start \u{2014} generous free tier, no credit card.",
                signup_url: "https://aistudio.google.com/apikey",
            }),
            _ => None,
        }
    }
}

/// In-memory only — never persisted (the key lives in a Dioxus signal in the UI).
#[derive(Clone, PartialEq, Debug)]
pub struct LlmConfig {
    pub provider: Provider,
    pub api_key: String,
    pub model: String,
    /// Used only by `Provider::Custom`.
    pub base_url: String,
    pub max_tokens: u32,
}

impl LlmConfig {
    pub fn new(provider: Provider) -> Self {
        LlmConfig {
            provider,
            api_key: String::new(),
            model: provider.default_model().to_string(),
            base_url: provider.default_base_url().to_string(),
            max_tokens: 1024,
        }
    }

    /// Resolve the effective model (fall back to the provider default if blank).
    pub(crate) fn effective_model(&self) -> String {
        let m = self.model.trim();
        if m.is_empty() {
            self.provider.default_model().to_string()
        } else {
            m.to_string()
        }
    }
}

/// A tool the model may call, advertised in the request. Built from a discovered
/// jbotci `ToolInfo`; `input_schema` is the raw JSON Schema.
#[derive(Clone, PartialEq, Debug)]
pub struct ToolDecl {
    pub name: String,
    pub description: String,
    pub input_schema: Value,
}

/// A normalized tool call the model requested (provider-agnostic). `id` is the
/// provider-assigned id (Anthropic/OpenAI); Gemini has none, so it is synthesized.
#[derive(Clone, PartialEq, Debug)]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub args: Value,
}

/// The result of running a tool, fed back to the model. `name` correlates for
/// Gemini (`functionResponse`); `id` correlates for Anthropic/OpenAI.
#[derive(Clone, PartialEq, Debug)]
pub struct ToolResult {
    pub id: String,
    pub name: String,
    pub content: String,
    pub is_error: bool,
}

/// A model response: optional text and/or tool calls.
#[derive(Clone, PartialEq, Debug, Default)]
pub struct ChatResponse {
    pub text: Option<String>,
    pub tool_calls: Vec<ToolCall>,
}

/// One turn of the conversation. The validate→feedback loop uses `User`/`Assistant`
/// (text); the jbotci tool loop adds `AssistantTools` (the model's tool-call turn)
/// and `ToolResults` (their outcomes).
#[derive(Clone, PartialEq, Debug)]
pub enum Turn {
    User(String),
    Assistant(String),
    AssistantTools {
        text: Option<String>,
        calls: Vec<ToolCall>,
    },
    ToolResults(Vec<ToolResult>),
}

impl Turn {
    pub fn user(s: impl Into<String>) -> Self {
        Turn::User(s.into())
    }
    pub fn assistant(s: impl Into<String>) -> Self {
        Turn::Assistant(s.into())
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn openrouter_first_gemini_second() {
        // The picker renders `Provider::ALL` in order; the two promoted free,
        // browser-direct providers lead, OpenRouter first.
        assert_eq!(Provider::ALL[0], Provider::OpenRouter);
        assert_eq!(Provider::ALL[1], Provider::Gemini);
    }

    #[test]
    fn openrouter_default_model_is_free() {
        // The "free" framing must be honest: OpenRouter's default is a :free model.
        assert!(Provider::OpenRouter.default_model().ends_with(":free"));
        // Gemini's default is a free-tier model (no :free suffix convention).
        assert_eq!(Provider::Gemini.default_model(), "gemini-2.0-flash");
    }

    #[test]
    fn promo_only_for_free_browser_providers() {
        assert!(Provider::OpenRouter.promo().is_some());
        assert!(Provider::Gemini.promo().is_some());
        assert!(Provider::Anthropic.promo().is_none());
        assert!(Provider::OpenAi.promo().is_none());
        assert!(Provider::Custom.promo().is_none());
    }
}
