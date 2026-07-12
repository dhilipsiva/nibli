//! Klaro — the non-Lojban surface syntax front-end for nibli (IN PROGRESS).
//!
//! Klaro is a predicate-call language (`goes(me, to: some market).`) that
//! compiles to the same `nibli_types::ast::AstBuffer` the Lojban parser
//! produces, reusing smuni/logji and every soundness gate unchanged. The
//! language is specified in repo-root `SURFACE_SYNTAX.md`; the implementation
//! program is tracked in repo-root `KLARO_TODO.md`.
//!
//! Currently implemented: the LEXER ([`token`], [`lexer`]) — maximal-munch
//! tokens with exact-match keyword reservation (single-sourced from
//! `klaro-dictionary`'s reserved-word list) and positioned fail-closed errors.
//! The parser, resolver, AstBuffer emitter, and renderer land in subsequent
//! KLARO_TODO bullets; until `parse_checked` exists this crate has no
//! public compile entry point.

pub mod lexer;
pub mod token;
