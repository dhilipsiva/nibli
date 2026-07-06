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

pub use request::build_chat_request;
pub use response::{clean_lojban_output, extract_text};
pub use system_prompt::system_prompt;
pub use types::{LlmConfig, Provider, Turn};
