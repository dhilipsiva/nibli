//! Lojban gerna (grammar/parser) WASM component.
//!
//! Entry point for the `gerna-component` WIT world. Implements the full
//! text-to-flat-buffer pipeline:
//!
//! 1. **Lex** — Logos DFA tokenizer ([`lexer::tokenize`])
//! 2. **Preprocess** — Metalinguistic resolution: si/sa/su/zo/zoi/zei ([`preprocessor::preprocess`])
//! 3. **Parse** — Recursive descent with per-sentence error recovery ([`grammar::parse_tokens_to_ast`])
//! 4. **Flatten** — Tree AST → index-based WIT buffer ([`Flattener`])
//!
//! The arena allocator (`bumpalo::Bump`) is created per `parse_text()` call and
//! freed in one shot after flattening.

/// Lojban AST types (arena-allocated tree nodes).
pub mod ast;
/// Recursive descent parser producing an arena-allocated AST.
pub mod grammar;
/// Logos-based lexer with post-lex compound cmavo correction.
pub mod lexer;
/// Metalinguistic preprocessor (si/sa/su/zo/zoi/zei resolution).
pub mod preprocessor;

use nibli_types::ast as flat;
use nibli_types::error::NibliError;

/// Parse Lojban text through the full pipeline: lex → preprocess → parse → flatten.
pub fn parse_text_native(input: String) -> Result<flat::ParseResult, NibliError> {
        // 1. Lex into morphological classification stream
        let raw_tokens = crate::lexer::tokenize(&input);

        // 2. Resolve metalinguistic operators (si/sa/su/zo/zoi/zei)
        let normalized = crate::preprocessor::preprocess(raw_tokens.into_iter(), &input);

        // 3. Recursive descent parse (with per-sentence error recovery)
        let arena = bumpalo::Bump::new();
        let result = crate::grammar::parse_tokens_to_ast(&normalized, &input, &arena);

        // 4. Convert grammar errors
        let errors: Vec<flat::ParseError> = result
            .errors
            .iter()
            .map(|e| flat::ParseError {
                message: e.message.clone(),
                line: e.line,
                column: e.column,
            })
            .collect();

        // 5. Flatten tree AST → index-based flat buffer
        let buffer = Flattener::flatten(&result.parsed);

        Ok(flat::ParseResult { buffer, errors })
}

// ─── AST → WIT Buffer Flattener ─────────────────────────────────

/// Converts the tree-structured AST into the flat index-based WIT buffer.
/// Each recursive AST node is pushed into the appropriate array and
/// referenced by index from its parent.
///
/// Top-level sentences are recorded in `buffer.roots`.
/// Rel clause bodies and nu abstraction bodies are stored in
/// `buffer.sentences` but are NOT roots.
struct Flattener {
    buffer: flat::AstBuffer,
}

impl Flattener {
    /// Create a new `Flattener` with empty buffers.
    fn new() -> Self {
        Self {
            buffer: flat::AstBuffer {
                selbris: Vec::new(),
                sumtis: Vec::new(),
                sentences: Vec::new(),
                roots: Vec::new(),
            },
        }
    }

    /// Walk the parsed AST and produce a flat index-based `AstBuffer`.
    fn flatten(parsed: &ast::ParsedText<'_>) -> flat::AstBuffer {
        let mut f = Self::new();
        for sentence in &parsed.sentences {
            let root_id = f.push_sentence(sentence);
            f.buffer.roots.push(root_id);
        }
        f.buffer
    }

    // ─── Sentence Flattening ────────────────────────────────
    /// Flatten a sentence node and return its index in `buffer.sentences`.
    fn push_sentence(&mut self, sentence: &ast::Sentence<'_>) -> u32 {
        use flat::{
            Sentence as WasmSentence, SentenceConnective as WasmConn,
        };

        match sentence {
            ast::Sentence::Simple(bridi) => {
                let relation = self.push_selbri(&bridi.selbri);

                let mut head_terms = Vec::new();
                for term in &bridi.head_terms {
                    head_terms.push(self.push_sumti(term));
                }

                let mut tail_terms = Vec::new();
                for term in &bridi.tail_terms {
                    tail_terms.push(self.push_sumti(term));
                }

                let tense = bridi.tense.map(|t| match t {
                    ast::Tense::Pu => flat::Tense::Pu,
                    ast::Tense::Ca => flat::Tense::Ca,
                    ast::Tense::Ba => flat::Tense::Ba,
                });

                let attitudinal = bridi.attitudinal.map(|a| match a {
                    ast::Attitudinal::Ei => flat::Attitudinal::Ei,
                    ast::Attitudinal::Ehe => flat::Attitudinal::Ehe,
                });

                let flat_bridi = flat::Bridi {
                    relation,
                    head_terms,
                    tail_terms,
                    negated: bridi.negated,
                    tense,
                    attitudinal,
                };

                let idx = self.buffer.sentences.len() as u32;
                // Push the flat_bridi wrapped in the Simple enum variant
                self.buffer
                    .sentences
                    .push(flat::Sentence::Simple(
                        flat_bridi,
                    ));
                idx
            }
            ast::Sentence::Connected {
                connective,
                left,
                right,
            } => {
                let l_idx = self.push_sentence(left);
                let r_idx = self.push_sentence(right);

                let conn = match connective {
                    ast::SentenceConnective::GanaiGi => WasmConn::GanaiGi,
                    ast::SentenceConnective::GeGi => WasmConn::GeGi,
                    ast::SentenceConnective::GaGi => WasmConn::GaGi,
                    ast::SentenceConnective::Afterthought {
                        left_negated,
                        connective: c,
                        right_negated,
                    } => {
                        let wit_conn = match c {
                            ast::Connective::Je => flat::Connective::Je,
                            ast::Connective::Ja => flat::Connective::Ja,
                            ast::Connective::Jo => flat::Connective::Jo,
                            ast::Connective::Ju => flat::Connective::Ju,
                        };
                        WasmConn::Afterthought((*left_negated, wit_conn, *right_negated))
                    }
                };

                let idx = self.buffer.sentences.len() as u32;
                self.buffer
                    .sentences
                    .push(WasmSentence::Connected((conn, l_idx, r_idx)));
                idx
            }
        }
    }

    // In the Flattener's top-level loop, ensure you are calling it like this:
    // for sentence in ast.sentences {
    //     let root_id = self.push_sentence(sentence);
    //     self.buffer.roots.push(root_id);
    // }

    // ─── Selbri ──────────────────────────────────────────────

    /// Flatten a selbri node and return its index in `buffer.selbris`.
    fn push_selbri(&mut self, selbri: &ast::Selbri<'_>) -> u32 {
        let wit_selbri = match selbri {
            ast::Selbri::Root(s) => flat::Selbri::Root(s.clone()),

            ast::Selbri::Compound(parts) => flat::Selbri::Compound(parts.clone()),

            ast::Selbri::Tanru(modifier, head) => {
                let m_id = self.push_selbri(modifier);
                let h_id = self.push_selbri(head);
                flat::Selbri::Tanru((m_id, h_id))
            }

            ast::Selbri::Converted(conv, inner) => {
                let inner_id = self.push_selbri(inner);
                let wit_conv = match conv {
                    ast::Conversion::Se => flat::Conversion::Se,
                    ast::Conversion::Te => flat::Conversion::Te,
                    ast::Conversion::Ve => flat::Conversion::Ve,
                    ast::Conversion::Xe => flat::Conversion::Xe,
                };
                flat::Selbri::Converted((wit_conv, inner_id))
            }

            ast::Selbri::Negated(inner) => {
                let inner_id = self.push_selbri(inner);
                flat::Selbri::Negated(inner_id)
            }

            ast::Selbri::Grouped(inner) => {
                let inner_id = self.push_selbri(inner);
                flat::Selbri::Grouped(inner_id)
            }

            ast::Selbri::WithArgs { core, args } => {
                let core_id = self.push_selbri(core);
                let arg_ids: Vec<u32> = args.iter().map(|s| self.push_sumti(s)).collect();
                flat::Selbri::WithArgs((core_id, arg_ids))
            }

            ast::Selbri::Connected {
                left,
                connective,
                right,
            } => {
                let l_id = self.push_selbri(left);
                let r_id = self.push_selbri(right);
                let wit_conn = match connective {
                    ast::Connective::Je => flat::Connective::Je,
                    ast::Connective::Ja => flat::Connective::Ja,
                    ast::Connective::Jo => flat::Connective::Jo,
                    ast::Connective::Ju => flat::Connective::Ju,
                };
                flat::Selbri::Connected((l_id, wit_conn, r_id))
            }
            ast::Selbri::Abstraction(kind, inner_bridi) => {
                // Inner bridi goes into sentences (NOT a root —
                // same pattern as rel clause bodies).
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_sentence(inner_bridi);
                let wit_kind = match kind {
                    ast::AbstractionKind::Nu => flat::AbstractionKind::Nu,
                    ast::AbstractionKind::Duhu => flat::AbstractionKind::Duhu,
                    ast::AbstractionKind::Ka => flat::AbstractionKind::Ka,
                    ast::AbstractionKind::Ni => flat::AbstractionKind::Ni,
                    ast::AbstractionKind::Siho => flat::AbstractionKind::Siho,
                };
                flat::Selbri::Abstraction((wit_kind, body_idx))
            }
        };

        let id = self.buffer.selbris.len() as u32;
        self.buffer.selbris.push(wit_selbri);
        id
    }

    // ─── Sumti ───────────────────────────────────────────────

    /// Flatten a sumti node and return its index in `buffer.sumtis`.
    fn push_sumti(&mut self, sumti: &ast::Sumti<'_>) -> u32 {
        let wit_sumti = match sumti {
            ast::Sumti::ProSumti(s) => flat::Sumti::ProSumti(s.clone()),
            ast::Sumti::Description { gadri, inner } => {
                let inner_id = self.push_selbri(inner);
                let wit_gadri = match gadri {
                    ast::Gadri::Lo => flat::Gadri::Lo,
                    ast::Gadri::Le => flat::Gadri::Le,
                    ast::Gadri::La => flat::Gadri::La,
                    ast::Gadri::RoLo => flat::Gadri::RoLo,
                    ast::Gadri::RoLe => flat::Gadri::RoLe,
                };
                flat::Sumti::Description((wit_gadri, inner_id))
            }
            ast::Sumti::Name(n) => flat::Sumti::Name(n.clone()),
            ast::Sumti::QuotedLiteral(q) => flat::Sumti::QuotedLiteral(q.clone()),
            ast::Sumti::Unspecified => flat::Sumti::Unspecified,
            ast::Sumti::Tagged(tag, inner) => {
                let inner_id = self.push_sumti(inner);
                let wit_tag = match tag {
                    ast::PlaceTag::Fa => flat::PlaceTag::Fa,
                    ast::PlaceTag::Fe => flat::PlaceTag::Fe,
                    ast::PlaceTag::Fi => flat::PlaceTag::Fi,
                    ast::PlaceTag::Fo => flat::PlaceTag::Fo,
                    ast::PlaceTag::Fu => flat::PlaceTag::Fu,
                };
                flat::Sumti::Tagged((wit_tag, inner_id))
            }
            ast::Sumti::ModalTagged(modal, inner) => {
                let inner_id = self.push_sumti(inner);
                let wit_modal = match modal {
                    ast::ModalTag::Fixed(bai) => {
                        let wit_bai = match bai {
                            ast::BaiTag::Ria => flat::BaiTag::Ria,
                            ast::BaiTag::Nii => flat::BaiTag::Nii,
                            ast::BaiTag::Mui => flat::BaiTag::Mui,
                            ast::BaiTag::Kiu => flat::BaiTag::Kiu,
                            ast::BaiTag::Pio => flat::BaiTag::Pio,
                            ast::BaiTag::Bai => flat::BaiTag::Bai,
                        };
                        flat::ModalTag::Fixed(wit_bai)
                    }
                    ast::ModalTag::Fio(selbri) => {
                        let selbri_id = self.push_selbri(selbri);
                        flat::ModalTag::Fio(selbri_id)
                    }
                };
                flat::Sumti::ModalTagged((wit_modal, inner_id))
            }
            ast::Sumti::Restricted { inner, clause } => {
                let inner_id = self.push_sumti(inner);

                // The rel clause body is a sentence — push it as a bridi.
                // It is NOT a root; it lives in `sentences` only for
                // cross-referencing by index from the Restricted variant.
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_sentence(clause.body);

                let wit_kind = match clause.kind {
                    ast::RelClauseKind::Poi => flat::RelClauseKind::Poi,
                    ast::RelClauseKind::Noi => flat::RelClauseKind::Noi,
                    ast::RelClauseKind::Voi => flat::RelClauseKind::Voi,
                };

                flat::Sumti::Restricted((
                    inner_id,
                    flat::RelClause {
                        kind: wit_kind,
                        body_sentence: body_idx,
                    },
                ))
            }

            ast::Sumti::Number(n) => flat::Sumti::Number(*n),

            ast::Sumti::Connected {
                left,
                connective,
                right_negated,
                right,
            } => {
                let left_id = self.push_sumti(left);
                let right_id = self.push_sumti(right);
                let wit_conn = match connective {
                    ast::Connective::Je => flat::Connective::Je,
                    ast::Connective::Ja => flat::Connective::Ja,
                    ast::Connective::Jo => flat::Connective::Jo,
                    ast::Connective::Ju => flat::Connective::Ju,
                };
                flat::Sumti::Connected((left_id, wit_conn, *right_negated, right_id))
            }

            ast::Sumti::QuantifiedDescription {
                count,
                gadri,
                inner,
            } => {
                let inner_id = self.push_selbri(inner);
                let wit_gadri = match gadri {
                    ast::Gadri::Lo => flat::Gadri::Lo,
                    ast::Gadri::Le => flat::Gadri::Le,
                    _ => unreachable!("QuantifiedDescription only uses Lo or Le"),
                };
                flat::Sumti::QuantifiedDescription((*count, wit_gadri, inner_id))
            }
        };

        let id = self.buffer.sumtis.len() as u32;
        self.buffer.sumtis.push(wit_sumti);
        id
    }
}



// Add these tests to parser/src/lib.rs or a new integration test file.
// They test the Flattener, not just the grammar parser.

#[cfg(test)]
#[path = "flattener_tests.rs"]
mod flattener_tests;

#[cfg(test)]
#[path = "pipeline_tests.rs"]
mod pipeline_tests;
