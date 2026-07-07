//! # nibli-fanva — agentic English→Lojban translator engine
//!
//! An LLM translates English to Lojban; the output is validated by real Lojban
//! compilers; any error is fed back into the conversation and the LLM retries
//! until the Lojban is valid (bounded by an attempt cap). This crate is the
//! engine — the UI shell lives in `nibli-ui`, which surfaces it as an agentic
//! "Translate" mode.
//!
//! ## Validation gate (the "verify" firewall)
//!
//! A candidate must pass three gates before the loop accepts it:
//!   1. **gerna** — `gerna::parse_checked` (grammar; engine-ready) — local.
//!   2. **smuni** — `smuni::compile_from_gerna_ast` (semantics/arity) — local.
//!   3. **official** — a vendored standard `camxes.js` (ilmentufa, MIT) via
//!      JS-interop (official grammar) — local, wasm-only. *(lands in a later phase)*
//!
//! All three are local, so the hot validation path makes no network call. jbotci
//! (`vlacku`/`cukta`/`tersmu`/`gentufa`) is used only as optional LLM tools + the
//! meaning check, reached through an app-owned proxy; when no proxy is configured
//! the translator degrades to the local gates and stays fully serverless.
//!
//! ## Testability
//!
//! The two local gates run on pure Rust nibli crates, so [`gates`] is
//! native-`cargo test`-able. The LLM `chat()` and the MCP client are abstracted
//! behind seams so the agent/provider logic tests with mocks on native, and only
//! the concrete transports are wasm-only.

pub mod agent;
pub mod gates;
pub mod llm;
pub mod mcp;

// Landing in a subsequent phase (see TODO.md):
//   the inner jbotci tool loop threads `mcp` into agent::translate_agentic (Phase 3)
