pub mod ast;
#[allow(warnings)]
mod bindings;
pub mod lexer;
pub mod preprocessor;

use bindings::exports::lojban::nesy::parser::Guest;
use bindings::lojban::nesy::ast_types::AstBuffer;
use bumpalo::Bump;

struct ParserComponent;

impl Guest for ParserComponent {
    fn parse_text(input: String) -> Result<AstBuffer, String> {
        let arena = Bump::new();

        // 1. Lex into classification stream
        let raw_tokens = crate::lexer::tokenize(&input);

        // 2. Resolve metalinguistics (si/sa/su/zo/zoi) [cite: 1]
        let normalized = crate::preprocessor::preprocess(raw_tokens.into_iter(), &input);

        // 3. Structural Parse (Zero-Copy from tokens) [cite: 1]
        let ast = crate::ast::parse_tokens_to_ast(&normalized, &arena)?;

        // 4. Flatten AST to linear buffer for WIT [cite: 1]
        Ok(flatten_to_buffer(ast))
    }
}

fn flatten_to_buffer(ast_list: bumpalo::collections::Vec<crate::ast::Bridi>) -> AstBuffer {
    let mut buffer = AstBuffer {
        selbris: Vec::new(),
        sumtis: Vec::new(),
        sentences: Vec::new(),
    };

    for bridi in ast_list {
        let selbri_id = buffer.selbris.len() as u32;
        let selbri_data = match bridi.selbri {
            crate::ast::Selbri::Root(s) => {
                bindings::lojban::nesy::ast_types::Selbri::Root(s.to_string())
            }
            _ => bindings::lojban::nesy::ast_types::Selbri::Root("unknown".to_string()),
        };
        buffer.selbris.push(selbri_data);

        let mut term_ids = Vec::new();
        for term in bridi.terms {
            let sumti_id = buffer.sumtis.len() as u32;
            let sumti_data = match term {
                // Corrected namespace: nesy::ast_types
                crate::ast::Sumti::ProSumti(s) => {
                    bindings::lojban::nesy::ast_types::Sumti::ProSumti(s.to_string())
                }
                crate::ast::Sumti::Description(d_selbri) => {
                    let d_selbri_id = buffer.selbris.len() as u32;
                    let inner_selbri = match *d_selbri {
                        crate::ast::Selbri::Root(s) => {
                            bindings::lojban::nesy::ast_types::Selbri::Root(s.to_string())
                        }
                        _ => bindings::lojban::nesy::ast_types::Selbri::Root("desc".to_string()),
                    };
                    buffer.selbris.push(inner_selbri);
                    bindings::lojban::nesy::ast_types::Sumti::Description(d_selbri_id)
                }
                _ => bindings::lojban::nesy::ast_types::Sumti::Name("unknown".to_string()),
            };
            buffer.sumtis.push(sumti_data);
            term_ids.push(sumti_id);
        }

        buffer
            .sentences
            .push(bindings::lojban::nesy::ast_types::Bridi {
                relation: selbri_id,
                terms: term_ids,
            });
    }

    buffer
}

bindings::export!(ParserComponent with_types_in bindings);
