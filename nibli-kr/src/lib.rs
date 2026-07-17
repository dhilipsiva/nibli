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
//! errors) → [`resolve`] (dictionary-driven fail-closed checks: name
//! resolution alias→identity-word→COMPILE ERROR, place checks, the
//! 3-variable lowering cap, `it`/`slot` position rules) → [`emit`]
//! (tree → `AstBuffer`, `$vars` lowered to da/de/di, aliases to word with
//! `Converted` swaps). [`parse_checked`] is the engine's fail-closed
//! text→AST seam.

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

/// FAIL CLOSED: parse + resolve + emit, or the first (source-order) error.
/// Feed the result to `nibli_semantics::compile_from_ast`.
pub fn parse_checked(text: &str) -> Result<AstBuffer, NibliError> {
    let statements = parser::parse_statements(text).map_err(to_nibli)?;
    resolve::resolve(text, &statements).map_err(to_nibli)?;
    emit::emit(text, &statements).map_err(to_nibli)
}

/// Per-statement recovery variant (the `ParseResult` contract): every
/// statement that parses, resolves, AND emits lands in the buffer; every
/// failure is reported. `errors` non-empty ⇒ the buffer is PARTIAL — callers
/// wanting fail-closed behavior use [`parse_checked`].
pub fn parse_text(text: &str) -> ParseResult {
    let (statements, parse_errors) = parser::parse_text_with_errors(text);
    let mut errors: Vec<nibli_types::ast::ParseError> = parse_errors
        .into_iter()
        .map(|e| nibli_types::ast::ParseError {
            message: e.message,
            line: e.line,
            column: e.column,
        })
        .collect();

    let mut good = Vec::new();
    for statement in statements {
        let single = std::slice::from_ref(&statement);
        if let Err(e) = resolve::resolve(text, single) {
            errors.push(nibli_types::ast::ParseError {
                message: e.message,
                line: e.line,
                column: e.column,
            });
            continue;
        }
        good.push(statement);
    }
    match emit::emit(text, &good) {
        Ok(buffer) => ParseResult { buffer, errors },
        Err(e) => {
            errors.push(nibli_types::ast::ParseError {
                message: e.message,
                line: e.line,
                column: e.column,
            });
            ParseResult {
                buffer: AstBuffer {
                    predicates: Vec::new(),
                    arguments: Vec::new(),
                    sentences: Vec::new(),
                    roots: Vec::new(),
                },
                errors,
            }
        }
    }
}
