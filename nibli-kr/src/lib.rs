//! nibli KR (nibli KR) — the surface-syntax front-end for nibli.
//!
//! nibli KR is a predicate-call language (`goes(me, some market).`) that compiles
//! to the same `nibli_types::ast::AstBuffer` the Lojban parser produces,
//! reusing nibli-semantics/nibli-reason and every soundness gate unchanged. The language is
//! specified in repo-root `NIBLI_KR.md`; the implementation program is
//! tracked in repo-root `TODO.md`.
//!
//! PARSER TECHNOLOGY (user decision, 2026-07-12): pest. `src/nibli_kr.pest` is
//! the EXECUTABLE grammar — the normative form of NIBLI_KR §15 — so the
//! grammar and the parser cannot drift by construction.
//!
//! Pipeline: [`parser`] (pest walker → tree [`ast`], §6/§7 errata as targeted
//! errors) → [`emit`] — THE single validating walk (single-resolution merge,
//! 2026-07-17): every dictionary-driven fail-closed check (name resolution →
//! COMPILE ERROR on unknown words, place checks, linked-args rules,
//! `it`/`slot` position rules, Name↔pronoun collisions) runs at the site that
//! lowers the construct into the `AstBuffer` (`$vars` preserved verbatim,
//! corpus entries to their canonical base with `Converted` swaps). [`resolve`]
//! is the lookup module both emit and lint share. [`parse_checked`] is the
//! engine's fail-closed text→AST seam.

pub mod ast;
pub mod emit;
pub mod lint;
pub mod parser;
pub mod render;
pub mod resolve;

/// The pest PEG grammar source — the normative form of NIBLI_KR §15, embedded so
/// downstream tooling (e.g. the nibli-formalize LLM prompt) can ground on the
/// EXACT accepted syntax, in-sync BY CONSTRUCTION: this is the same file the
/// `#[grammar = "nibli_kr.pest"]` derive consumes, so it can never drift from the
/// parser.
pub const GRAMMAR: &str = include_str!("nibli_kr.pest");

use nibli_types::ast::{AstBuffer, ParseResult};
use nibli_types::error::{NibliError, SyntaxDetail};

fn to_nibli(e: parser::ParseError) -> NibliError {
    NibliError::Syntax(SyntaxDetail {
        message: e.message,
        line: e.line,
        column: e.column,
    })
}

/// FAIL CLOSED: parse + the validating emit walk, or the first (source-order)
/// error. Feed the result to `nibli_semantics::compile_from_ast`.
pub fn parse_checked(text: &str) -> Result<AstBuffer, NibliError> {
    let statements = parser::parse_statements(text).map_err(to_nibli)?;
    emit::emit(text, &statements).map_err(to_nibli)
}

/// Per-statement recovery variant (the `ParseResult` contract): every
/// statement that parses AND emits lands in the buffer (a failing statement's
/// partial nodes roll back); every failure is reported, first error per
/// statement. `errors` non-empty ⇒ the buffer is PARTIAL — callers wanting
/// fail-closed behavior use [`parse_checked`].
pub fn parse_text(text: &str) -> ParseResult {
    let (statements, parse_errors) = parser::parse_text_with_errors(text);
    let (buffer, emit_errors) = emit::emit_recovering(text, &statements);
    let errors = parse_errors
        .into_iter()
        .chain(emit_errors)
        .map(|e| nibli_types::ast::ParseError {
            message: e.message,
            line: e.line,
            column: e.column,
        })
        .collect();
    ParseResult { buffer, errors }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_text_recovers_per_statement_with_rollback() {
        // Bad middle statement: its partial nodes truncate back out; the
        // survivors form a structurally intact buffer (compiles + renders —
        // no dangling indices after the rollback).
        let r = parse_text("dog(Rex). zzq(me). goes(me, some market).");
        assert_eq!(r.errors.len(), 1, "{:?}", r.errors);
        assert!(
            r.errors[0].message.contains("unknown predicate"),
            "{:?}",
            r.errors
        );
        assert_eq!(r.buffer.roots.len(), 2, "two survivors");
        let rendered = render::render(&r.buffer).unwrap();
        assert!(rendered.contains("dog(Rex)"), "{rendered}");
        assert!(rendered.contains("goes(me, some market)"), "{rendered}");
        assert!(!rendered.contains("zzq"), "{rendered}");
        nibli_semantics::compile_from_ast(r.buffer).unwrap();
    }

    #[test]
    fn parse_text_resets_walk_state_after_a_failed_statement() {
        // Statement 1 fails INSIDE a block rel-clause body (mid-walk state
        // set); statement 2's bare `it` must still hit the position rule —
        // a polluted `block_it_var`/`in_clause_body` would let it through.
        let r = parse_text("every dog where zzq(it, you) $d: big($d). big(it).");
        assert_eq!(r.errors.len(), 2, "{:?}", r.errors);
        assert!(
            r.errors[0].message.contains("unknown predicate"),
            "{:?}",
            r.errors
        );
        assert!(
            r.errors[1].message.contains("where/also clause body"),
            "{:?}",
            r.errors
        );
        assert!(r.buffer.roots.is_empty(), "no survivors");
        assert!(r.buffer.sentences.is_empty(), "rollback left nodes behind");
    }
}
