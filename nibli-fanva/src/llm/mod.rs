//! LLM layer — bring-your-own-key, multi-provider, multi-turn chat.
//!
//! The key lives only in the caller's `LlmConfig` (a Dioxus signal in the UI),
//! and requests go straight to the provider — nibli has no server. Request
//! building ([`build_chat_request`]) and response extraction ([`extract_text`])
//! are pure and native-testable; the concrete gloo-net HTTP send (wasm-only) and
//! jbotci tool-use land in later phases.

pub mod system_prompt;
pub mod types;

mod request;
mod response;

// The concrete transport. `HttpChat` exists on all targets (so downstream native
// checks pass); it only performs real sends under wasm — see `http.rs`.
mod http;
pub use http::HttpChat;

pub use request::{build_chat_request, build_chat_request_tools};
pub use response::{clean_lojban_output, extract_text, parse_chat_response};
pub use system_prompt::system_prompt;
pub use types::{ChatResponse, LlmConfig, Provider, ToolCall, ToolDecl, ToolResult, Turn};

/// The async send seam. The real implementation (wasm-only gloo-net, porting
/// `nibli-ui`'s send path) lands with the HTTP transport; the agent's native
/// tests supply a mock. `#[allow]` because this is an internal trait always used
/// through generics, never as `dyn`.
#[allow(async_fn_in_trait)]
pub trait Chat {
    /// Send the system prompt + conversation, returning the assistant's raw text
    /// (before `clean_lojban_output`).
    async fn chat(
        &self,
        cfg: &LlmConfig,
        system: &str,
        turns: &[Turn],
    ) -> Result<String, ChatError>;
}

/// A transport/provider failure from [`Chat::chat`] — network, auth, rate-limit,
/// or an unparseable response. Distinct from a validation-gate failure: the agent
/// aborts on this rather than retrying.
#[derive(Clone, Debug)]
pub struct ChatError(pub String);

impl std::fmt::Display for ChatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// The tool-use send seam — returns structured text + tool calls and accepts tool
/// declarations. `HttpChat` implements it; the tool-loop tests mock it. `#[allow]`
/// because it is always used through generics, never as `dyn`.
#[allow(async_fn_in_trait)]
pub trait ToolChat {
    async fn chat_tools(
        &self,
        cfg: &LlmConfig,
        system: &str,
        turns: &[Turn],
        tools: &[ToolDecl],
    ) -> Result<ChatResponse, ChatError>;
}
