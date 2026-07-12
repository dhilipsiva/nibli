//! Klaro — the non-Lojban surface syntax front-end for nibli (IN PROGRESS).
//!
//! Klaro is a predicate-call language (`goes(me, to: some market).`) that
//! compiles to the same `nibli_types::ast::AstBuffer` the Lojban parser
//! produces, reusing smuni/logji and every soundness gate unchanged. The
//! language is specified in repo-root `SURFACE_SYNTAX.md`; the implementation
//! program is tracked in repo-root `KLARO_TODO.md`.
//!
//! Currently implemented:
//! - the LEXER ([`token`], [`lexer`]) — maximal-munch tokens with exact-match
//!   keyword reservation (single-sourced from `klaro-dictionary`'s
//!   reserved-word list) and positioned fail-closed errors;
//! - the PARSER CORE ([`ast`], [`parser`]) — recursive descent to an owned
//!   tree AST: terms, determiner phrases, predications with positional+named
//!   args, the operator chain, tense/deontic prefixes, binary `=`, and
//!   `.`-terminated statements, with the SURFACE_SYNTAX §6 errata enforced as
//!   grammar (`~past P`, `~~P`, prefix/`~` over compound claims all rejected
//!   with targeted positioned errors).
//!
//! Still to land (subsequent KLARO_TODO bullets): parser completion (`all`
//! prenex, block determiners, tanru, `.label` selectors, linked args, `via`
//! tags, rel clauses, abstractions), the resolve pass, the AstBuffer emitter,
//! and the renderer; until the emitter exists this crate has no public
//! compile entry point.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod token;
