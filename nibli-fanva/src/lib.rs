//! # nibli-fanva — agentic English→KB formalizer engine
//!
//! An LLM formalizes English into the KB language (nibli KR — the klaro
//! crate); the output is validated by the real nibli compilers; any error is
//! fed back into the conversation and the LLM retries until the KB text is
//! valid (bounded by an attempt cap). This crate is the engine — the UI shell
//! lives in `nibli-ui`, which surfaces it as the agentic "Formalize" mode
//! ("compile" stays reserved for the deterministic KB→logic step; the LLM
//! step is interpretive formalization behind gates).
//!
//! ## Validation gate (the "verify" firewall)
//!
//! A candidate must pass three deterministic gates before the loop accepts
//! it: 1. **klaro** — `klaro::parse_checked` (grammar + fail-closed alias
//! resolution) — local. 2. **smuni** — `smuni::compile_from_gerna_ast`
//! (semantics/arity) — local. 3. **round-trip** — the candidate's canonical
//! re-spelling (`klaro::render`) must re-compile to the SAME `LogicBuffer`
//! (klaro's fixpoint contract as a per-candidate drift-catcher) — local,
//! native + wasm.
//!
//! All gates are local, so the hot validation path makes no network call and
//! the loop stays fully serverless. (The legacy Lojban chain — gerna + the
//! wasm-only camxes gate — and the jbotci MCP tool loop retired with the
//! Lojban front-end at THE DROP.)
//!
//! ## Testability
//!
//! The gates run on pure Rust nibli crates, so [`gates`] is
//! native-`cargo test`-able (including the round-trip gate). The LLM
//! `chat()` is abstracted behind a seam so the agent/provider logic tests
//! with mocks on native, and only the concrete transport is wasm-only.

pub mod agent;
pub mod gates;
pub mod llm;
pub mod verify;
