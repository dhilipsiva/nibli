#[allow(warnings)]
mod bindings;

mod ast;
mod lexer;
mod preprocessor;

use bindings::exports::lojban::nesy::parser::Guest;
use bindings::lojban::nesy::ast_types::{AstBuffer, Bridi, Selbri, Sumti};
use bumpalo::Bump;

use crate::ast::parse_to_ast;
use crate::lexer::tokenize;
use crate::preprocessor::preprocess;

struct ParserComponent;

impl Guest for ParserComponent {
    fn parse_text(input: String) -> Result<AstBuffer, String> {
        // 1. Lexing
        let raw_tokens = tokenize(&input);

        // 2. Preprocessing
        let normalized_tokens = preprocess(raw_tokens.into_iter(), &input);

        let sanitized_input = normalized_tokens
            .iter()
            .filter_map(|t| match t {
                preprocessor::NormalizedToken::Standard(_, s) => Some(*s),
                preprocessor::NormalizedToken::Quoted(s) => Some(*s),
                preprocessor::NormalizedToken::Glued(parts) => Some(parts[0]),
            })
            .collect::<Vec<&str>>()
            .join(" ");

        // 3. Structural Parsing (Arena Allocated)
        let arena = Bump::new();
        let bump_ast = parse_to_ast(&sanitized_input, &arena).map_err(|e| e.to_string())?;

        // 4. Graph Flattening for Zero-Overhead WASM Boundary Crossing
        let mut buffer = AstBuffer {
            selbris: Vec::with_capacity(bump_ast.len() * 2),
            sumtis: Vec::with_capacity(bump_ast.len() * 4),
            sentences: Vec::with_capacity(bump_ast.len()),
        };

        for bridi in bump_ast.iter() {
            let relation_id = flatten_selbri(&bridi.selbri, &mut buffer.selbris);

            let mut term_ids = Vec::with_capacity(bridi.terms.len());
            for term in bridi.terms.iter() {
                term_ids.push(flatten_sumti(term, &mut buffer.selbris, &mut buffer.sumtis));
            }

            buffer.sentences.push(Bridi {
                relation: relation_id,
                terms: term_ids,
            });
        }

        // The Bump arena is instantly dropped here, leaving only the flat buffer to return.
        Ok(buffer)
    }
}

/// Recursively flattens the Selbri tree into linear array indices.
fn flatten_selbri(selbri: &crate::ast::Selbri, selbris: &mut Vec<Selbri>) -> u32 {
    let mapped = match selbri {
        crate::ast::Selbri::Root(r) => Selbri::Root(r.to_string()),
        crate::ast::Selbri::Compound(parts) => {
            Selbri::Compound(parts.iter().map(|s| s.to_string()).collect())
        }
        crate::ast::Selbri::Tanru(modi, head) => {
            let m_id = flatten_selbri(modi, selbris);
            let h_id = flatten_selbri(head, selbris);
            Selbri::Tanru((m_id, h_id))
        }
    };

    let id = selbris.len() as u32;
    selbris.push(mapped);
    id
}

/// Recursively flattens the Sumti tree into linear array indices.
fn flatten_sumti(
    sumti: &crate::ast::Sumti,
    selbris: &mut Vec<Selbri>,
    sumtis: &mut Vec<Sumti>,
) -> u32 {
    let mapped = match sumti {
        crate::ast::Sumti::ProSumti(p) => Sumti::ProSumti(p.to_string()),
        crate::ast::Sumti::Name(n) => Sumti::Name(n.to_string()),
        crate::ast::Sumti::QuotedLiteral(q) => Sumti::QuotedLiteral(q.to_string()),
        crate::ast::Sumti::Description(s) => {
            let s_id = flatten_selbri(s, selbris);
            Sumti::Description(s_id)
        }
    };

    let id = sumtis.len() as u32;
    sumtis.push(mapped);
    id
}

// Bind the implementation to the generated WebAssembly exports
bindings::export!(ParserComponent with_types_in bindings);
