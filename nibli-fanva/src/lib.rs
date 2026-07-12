//! # nibli-fanva — agentic English→KB formalizer engine
//!
//! An LLM formalizes English into the KB language (KLARO since THE FLIP;
//! legacy Lojban behind the same seam); the output is validated by the real
//! nibli compilers; any error is fed back into the conversation and the LLM
//! retries until the KB text is valid (bounded by an attempt cap). This crate
//! is the engine — the UI shell lives in `nibli-ui`, which surfaces it as the
//! agentic "Formalize" mode ("compile" stays reserved for the deterministic
//! KB→logic step; the LLM step is interpretive formalization behind gates).
//!
//! ## Validation gate (the "verify" firewall)
//!
//! Every entry point takes the KB [`nibli_types::lang::Language`]; a candidate
//! must pass its language's three deterministic gates before the loop accepts it:
//!
//! **KLARO**: 1. **klaro** — `klaro::parse_checked` (grammar + fail-closed
//! alias resolution) — local. 2. **smuni** — `smuni::compile_from_gerna_ast`
//! (semantics/arity) — local. 3. **round-trip** — the candidate's canonical
//! re-spelling (`klaro::render`) must re-compile to the SAME `LogicBuffer`
//! (klaro's fixpoint contract as a per-candidate drift-catcher) — local,
//! native + wasm.
//!
//! **LOJBAN (legacy)**: 1. **gerna** — `gerna::parse_checked`. 2. **smuni**.
//! 3. **official** — a vendored standard `camxes.js` (ilmentufa, MIT) via
//! JS-interop (official grammar) — local, wasm-only, Lojban-only.
//!
//! All gates are local, so the hot validation path makes no network call.
//! jbotci (`vlacku`/`cukta`/`tersmu`/`gentufa`) is Lojban-only tooling, used
//! only as optional LLM tools + the deep-meaning view, reached through an
//! app-owned proxy; callers construct the [`mcp::McpClient`] with an empty
//! proxy in Klaro mode, and when no proxy is configured the loop degrades to
//! the local gates and stays fully serverless.
//!
//! ## Testability
//!
//! The local gates run on pure Rust nibli crates, so [`gates`] is
//! native-`cargo test`-able (including the Klaro round-trip gate). The LLM
//! `chat()` and the MCP client are abstracted behind seams so the
//! agent/provider logic tests with mocks on native, and only the concrete
//! transports are wasm-only.

pub mod agent;
pub mod gates;
pub mod llm;
pub mod mcp;
pub mod tools;
pub mod verify;
