// parser/src/lib.rs
//
// WASM component entry point. Pipeline:
//   1. Lex (Logos DFA)
//   2. Preprocess (metalinguistic resolution)
//   3. Parse (recursive descent)
//   4. Flatten (tree AST → index-based WIT buffer)

pub mod ast;
#[allow(warnings)]
mod bindings;
pub mod grammar;
pub mod lexer;
pub mod preprocessor;

use bindings::exports::lojban::nesy::parser::Guest;
use bindings::lojban::nesy::ast_types as wit;

struct ParserComponent;

impl Guest for ParserComponent {
    fn parse_text(input: String) -> Result<wit::AstBuffer, String> {
        // 1. Lex into morphological classification stream
        let raw_tokens = crate::lexer::tokenize(&input);

        // 2. Resolve metalinguistic operators (si/sa/su/zo/zoi/zei)
        let normalized = crate::preprocessor::preprocess(raw_tokens.into_iter(), &input);

        // 3. Recursive descent parse
        let parsed = crate::grammar::parse_tokens_to_ast(&normalized)?;

        // 4. Flatten tree AST → index-based WIT buffer
        Ok(Flattener::flatten(parsed))
    }
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
    buffer: wit::AstBuffer,
}

impl Flattener {
    fn new() -> Self {
        Self {
            buffer: wit::AstBuffer {
                selbris: Vec::new(),
                sumtis: Vec::new(),
                sentences: Vec::new(),
                roots: Vec::new(),
            },
        }
    }

    fn flatten(parsed: ast::ParsedText) -> wit::AstBuffer {
        let mut f = Self::new();
        for sentence in parsed.sentences {
            let root_id = f.push_sentence(sentence);
            f.buffer.roots.push(root_id);
        }
        // xx       for bridi in parsed.sentences {
        //            f.push_bridi(bridi);
        //            // The top-level sentence is always the LAST entry added by
        //            // push_bridi.  Rel clause bodies and nu abstraction bodies are
        //            // pushed earlier (during recursive push_sumti/push_selbri),
        //            // so they have lower indices.
        //            let root_idx = (f.buffer.sentences.len() - 1) as u32;
        //            f.buffer.roots.push(root_idx);
        //        }
        f.buffer
    }

    // ─── Bridi ───────────────────────────────────────────────

    fn push_bridi(&mut self, bridi: ast::Bridi) {
        let relation = self.push_selbri(bridi.selbri);

        let head_terms: Vec<u32> = bridi
            .head_terms
            .into_iter()
            .map(|s| self.push_sumti(s))
            .collect();

        let tail_terms: Vec<u32> = bridi
            .tail_terms
            .into_iter()
            .map(|s| self.push_sumti(s))
            .collect();
        let tense = bridi.tense.map(|t| match t {
            ast::Tense::Pu => wit::Tense::Pu,
            ast::Tense::Ca => wit::Tense::Ca,
            ast::Tense::Ba => wit::Tense::Ba,
        });

        let flat_bridi = wit::Bridi {
            relation,
            head_terms,
            tail_terms,
            negated: bridi.negated,
            tense,
        };

        self.buffer
            .sentences
            .push(wit::Sentence::Simple(flat_bridi));
    }

    // Add this method to your Flattener struct in parser/src/lib.rs:
    fn push_sentence(&mut self, sentence: ast::Sentence) -> u32 {
        use bindings::lojban::nesy::ast_types::{
            Sentence as WasmSentence, SentenceConnective as WasmConn,
        };

        match sentence {
            ast::Sentence::Simple(bridi) => {
                let relation = self.push_selbri(bridi.selbri);

                let mut head_terms = Vec::new();
                for term in bridi.head_terms {
                    head_terms.push(self.push_sumti(term));
                }

                let mut tail_terms = Vec::new();
                for term in bridi.tail_terms {
                    tail_terms.push(self.push_sumti(term));
                }

                let tense = bridi.tense.map(|t| match t {
                    ast::Tense::Pu => bindings::lojban::nesy::ast_types::Tense::Pu,
                    ast::Tense::Ca => bindings::lojban::nesy::ast_types::Tense::Ca,
                    ast::Tense::Ba => bindings::lojban::nesy::ast_types::Tense::Ba,
                });

                let flat_bridi = bindings::lojban::nesy::ast_types::Bridi {
                    relation,
                    head_terms,
                    tail_terms,
                    negated: bridi.negated,
                    tense,
                };

                let idx = self.buffer.sentences.len() as u32;
                // Push the flat_bridi wrapped in the Simple enum variant
                self.buffer
                    .sentences
                    .push(bindings::lojban::nesy::ast_types::Sentence::Simple(
                        flat_bridi,
                    ));
                idx
            }
            ast::Sentence::Connected {
                connective,
                left,
                right,
            } => {
                let l_idx = self.push_sentence(*left);
                let r_idx = self.push_sentence(*right);

                let conn = match connective {
                    ast::SentenceConnective::GanaiGi => WasmConn::GanaiGi,
                    ast::SentenceConnective::GeGi => WasmConn::GeGi,
                    ast::SentenceConnective::GaGi => WasmConn::GaGi,
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

    fn push_selbri(&mut self, selbri: ast::Selbri) -> u32 {
        let wit_selbri = match selbri {
            ast::Selbri::Root(s) => wit::Selbri::Root(s),

            ast::Selbri::Compound(parts) => wit::Selbri::Compound(parts),

            ast::Selbri::Tanru(modifier, head) => {
                let m_id = self.push_selbri(*modifier);
                let h_id = self.push_selbri(*head);
                wit::Selbri::Tanru((m_id, h_id))
            }

            ast::Selbri::Converted(conv, inner) => {
                let inner_id = self.push_selbri(*inner);
                let wit_conv = match conv {
                    ast::Conversion::Se => wit::Conversion::Se,
                    ast::Conversion::Te => wit::Conversion::Te,
                    ast::Conversion::Ve => wit::Conversion::Ve,
                    ast::Conversion::Xe => wit::Conversion::Xe,
                };
                wit::Selbri::Converted((wit_conv, inner_id))
            }

            ast::Selbri::Negated(inner) => {
                let inner_id = self.push_selbri(*inner);
                wit::Selbri::Negated(inner_id)
            }

            ast::Selbri::Grouped(inner) => {
                let inner_id = self.push_selbri(*inner);
                wit::Selbri::Grouped(inner_id)
            }

            ast::Selbri::WithArgs { core, args } => {
                let core_id = self.push_selbri(*core);
                let arg_ids: Vec<u32> = args.into_iter().map(|s| self.push_sumti(s)).collect();
                wit::Selbri::WithArgs((core_id, arg_ids))
            }

            ast::Selbri::Connected {
                left,
                connective,
                right,
            } => {
                let l_id = self.push_selbri(*left);
                let r_id = self.push_selbri(*right);
                let wit_conn = match connective {
                    ast::Connective::Je => wit::Connective::Je,
                    ast::Connective::Ja => wit::Connective::Ja,
                    ast::Connective::Jo => wit::Connective::Jo,
                    ast::Connective::Ju => wit::Connective::Ju,
                };
                wit::Selbri::Connected((l_id, wit_conn, r_id))
            }
            ast::Selbri::Abstraction(inner_bridi) => {
                // Inner bridi goes into sentences (NOT a root —
                // same pattern as rel clause bodies).
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_sentence(*inner_bridi);
                wit::Selbri::Abstraction(body_idx)
            }
        };

        let id = self.buffer.selbris.len() as u32;
        self.buffer.selbris.push(wit_selbri);
        id
    }

    // ─── Sumti ───────────────────────────────────────────────

    fn push_sumti(&mut self, sumti: ast::Sumti) -> u32 {
        let wit_sumti = match sumti {
            ast::Sumti::ProSumti(s) => wit::Sumti::ProSumti(s),
            ast::Sumti::Description { gadri, inner } => {
                let inner_id = self.push_selbri(*inner);
                let wit_gadri = match gadri {
                    ast::Gadri::Lo => wit::Gadri::Lo,
                    ast::Gadri::Le => wit::Gadri::Le,
                    ast::Gadri::La => wit::Gadri::La,
                    ast::Gadri::RoLo => wit::Gadri::RoLo,
                    ast::Gadri::RoLe => wit::Gadri::RoLe,
                };
                wit::Sumti::Description((wit_gadri, inner_id))
            }
            ast::Sumti::Name(n) => wit::Sumti::Name(n),
            ast::Sumti::QuotedLiteral(q) => wit::Sumti::QuotedLiteral(q),
            ast::Sumti::Unspecified => wit::Sumti::Unspecified,
            ast::Sumti::Tagged(tag, inner) => {
                let inner_id = self.push_sumti(*inner);
                let wit_tag = match tag {
                    ast::PlaceTag::Fa => wit::PlaceTag::Fa,
                    ast::PlaceTag::Fe => wit::PlaceTag::Fe,
                    ast::PlaceTag::Fi => wit::PlaceTag::Fi,
                    ast::PlaceTag::Fo => wit::PlaceTag::Fo,
                    ast::PlaceTag::Fu => wit::PlaceTag::Fu,
                };
                wit::Sumti::Tagged((wit_tag, inner_id))
            }
            ast::Sumti::Restricted { inner, clause } => {
                let inner_id = self.push_sumti(*inner);

                // The rel clause body is a sentence — push it as a bridi.
                // It is NOT a root; it lives in `sentences` only for
                // cross-referencing by index from the Restricted variant.
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_sentence(*clause.body);

                let wit_kind = match clause.kind {
                    ast::RelClauseKind::Poi => wit::RelClauseKind::Poi,
                    ast::RelClauseKind::Noi => wit::RelClauseKind::Noi,
                };

                wit::Sumti::Restricted((
                    inner_id,
                    wit::RelClause {
                        kind: wit_kind,
                        body_sentence: body_idx,
                    },
                ))
            }

            ast::Sumti::Number(n) => wit::Sumti::Number(n),

            ast::Sumti::Connected {
                left,
                connective,
                right_negated,
                right,
            } => {
                let left_id = self.push_sumti(*left);
                let right_id = self.push_sumti(*right);
                let wit_conn = match connective {
                    ast::Connective::Je => wit::Connective::Je,
                    ast::Connective::Ja => wit::Connective::Ja,
                    ast::Connective::Jo => wit::Connective::Jo,
                    ast::Connective::Ju => wit::Connective::Ju,
                };
                wit::Sumti::Connected((left_id, wit_conn, right_negated, right_id))
            }
        };

        let id = self.buffer.sumtis.len() as u32;
        self.buffer.sumtis.push(wit_sumti);
        id
    }
}

bindings::export!(ParserComponent with_types_in bindings);

// Add these tests to parser/src/lib.rs or a new integration test file.
// They test the Flattener, not just the grammar parser.

#[cfg(test)]
mod flattener_tests {
    use crate::ast::*;

    // Re-use the Flattener (it's private, so these tests must live in lib.rs
    // or you must make Flattener pub(crate)).

    use super::Flattener;

    /// Two simple sentences: "klama .i prami"
    /// Both must appear as roots.
    #[test]
    fn test_multi_sentence_produces_two_roots() {
        let parsed = ParsedText {
            sentences: vec![
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("klama".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
            ],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(
            buffer.roots.len(),
            2,
            "expected 2 roots, got {}",
            buffer.roots.len()
        );

        // Roots must point to distinct sentences
        assert_ne!(buffer.roots[0], buffer.roots[1]);
    }

    /// Three sentences — all three must be roots.
    #[test]
    fn test_three_sentences_three_roots() {
        let parsed = ParsedText {
            sentences: vec![
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("klama".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("barda".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
            ],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.roots.len(), 3);
    }

    /// Single sentence with a relative clause.
    /// The rel clause body is in `sentences` but must NOT be a root.
    /// Only 1 root expected.
    #[test]
    fn test_rel_clause_body_is_not_a_root() {
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::Restricted {
                    inner: Box::new(Sumti::Description {
                        gadri: Gadri::Lo,
                        inner: Box::new(Selbri::Root("gerku".into())),
                    }),
                    clause: RelClause {
                        kind: RelClauseKind::Poi,
                        body: Box::new(Sentence::Simple(Bridi {
                            selbri: Selbri::Root("sutra".into()),
                            head_terms: vec![],
                            tail_terms: vec![],
                            negated: false,
                            tense: None,
                        })),
                    },
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        // sentences has 2 entries (rel clause body + top-level), but only 1 root
        assert_eq!(buffer.sentences.len(), 2);
        assert_eq!(buffer.roots.len(), 1);
    }

    /// nu abstraction body must NOT be a root.
    #[test]
    fn test_nu_abstraction_body_is_not_a_root() {
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::Description {
                    gadri: Gadri::Lo,
                    inner: Box::new(Selbri::Abstraction(Box::new(Sentence::Simple(Bridi {
                        selbri: Selbri::Root("klama".into()),
                        head_terms: vec![Sumti::ProSumti("mi".into())],
                        tail_terms: vec![],
                        negated: false,
                        tense: None,
                    })))),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.sentences.len(), 2); // abstraction body + top-level
        assert_eq!(buffer.roots.len(), 1); // only top-level is root
    }

    /// Multi-sentence with rel clauses — roots count must match
    /// sentence count, not total bridi count.
    #[test]
    fn test_multi_sentence_with_rel_clauses() {
        // Sentence 1: lo gerku poi barda cu klama  (1 rel clause body + 1 top-level)
        // Sentence 2: mi prami do                   (1 top-level)
        // Total sentences in buffer: 3, roots: 2
        let parsed = ParsedText {
            sentences: vec![
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("klama".into()),
                    head_terms: vec![Sumti::Restricted {
                        inner: Box::new(Sumti::Description {
                            gadri: Gadri::Lo,
                            inner: Box::new(Selbri::Root("gerku".into())),
                        }),
                        clause: RelClause {
                            kind: RelClauseKind::Poi,
                            body: Box::new(Sentence::Simple(Bridi {
                                selbri: Selbri::Root("barda".into()),
                                head_terms: vec![],
                                tail_terms: vec![],
                                negated: false,
                                tense: None,
                            })),
                        },
                    }],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![Sumti::ProSumti("mi".into())],
                    tail_terms: vec![Sumti::ProSumti("do".into())],
                    negated: false,
                    tense: None,
                }),
            ],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.sentences.len(), 3); // 1 rel body + 2 top-level
        assert_eq!(buffer.roots.len(), 2); // only the 2 top-level sentences
    }
}
