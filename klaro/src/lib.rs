//! Klaro — the non-Lojban surface syntax front-end for nibli (IN PROGRESS).
//!
//! Klaro is a predicate-call language (`goes(me, to: some market).`) that
//! compiles to the same `nibli_types::ast::AstBuffer` the Lojban parser
//! produces, reusing smuni/logji and every soundness gate unchanged. The
//! language is specified in repo-root `SURFACE_SYNTAX.md`; the implementation
//! program is tracked in repo-root `KLARO_TODO.md`.
//!
//! PARSER TECHNOLOGY (user decision, 2026-07-12): pest. `src/klaro.pest` is
//! the EXECUTABLE grammar — the normative form of SURFACE_SYNTAX §15 — so the
//! grammar and the parser cannot drift by construction (the property that
//! motivated the switch from the earlier hand recursive-descent parser).
//! Scannerless keyword-boundary safety (`everyday` never splits into
//! `every day`) is carried by self-guarded keyword rules plus behavioral
//! tests, and the keyword set is pinned both-directions against
//! `klaro-dictionary`'s single-source reserved-word list.
//!
//! Currently implemented ([`ast`], [`parser`], [`resolve`]): the FULL v0.1
//! grammar surface — terms, determiner phrases, predications with
//! positional+named args, the operator chain, tense/deontic prefixes, binary
//! `=`, tanru/`[ ]`/`+` compounds, `.label` place selectors, linked args,
//! `where`/`also` relative clauses (mandatory-`it`), abstractions, `via`
//! tags, block determiners, and `all` prenex — plus the dictionary-driven
//! resolve pass (fail-closed name resolution: alias → identity-gismu →
//! COMPILE ERROR, never an arity-2 guess; place checks; the 3-variable
//! lowering cap; `it`/`slot` position rules).
//!
//! Still to land (subsequent KLARO_TODO bullets): the AstBuffer emitter and
//! the renderer; until the emitter exists this crate has no public compile
//! entry point.

pub mod ast;
pub mod parser;
pub mod resolve;
