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
    fn parse_text(input: String) -> Result<wit::ParseResult, String> {
        // 1. Lex into morphological classification stream
        let raw_tokens = crate::lexer::tokenize(&input);

        // 2. Resolve metalinguistic operators (si/sa/su/zo/zoi/zei)
        let normalized = crate::preprocessor::preprocess(raw_tokens.into_iter(), &input);

        // 3. Recursive descent parse (with per-sentence error recovery)
        let result = crate::grammar::parse_tokens_to_ast(&normalized, &input);

        // 4. Convert grammar errors to WIT errors
        let errors: Vec<wit::ParseError> = result
            .errors
            .iter()
            .map(|e| wit::ParseError {
                message: e.to_string(),
                line: e.line,
                column: e.column,
            })
            .collect();

        // 5. Flatten tree AST → index-based WIT buffer
        let buffer = Flattener::flatten(result.parsed);

        Ok(wit::ParseResult { buffer, errors })
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
        f.buffer
    }

    // ─── Sentence Flattening ────────────────────────────────
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

                let attitudinal = bridi.attitudinal.map(|a| match a {
                    ast::Attitudinal::Ei => bindings::lojban::nesy::ast_types::Attitudinal::Ei,
                    ast::Attitudinal::Ehe => bindings::lojban::nesy::ast_types::Attitudinal::Ehe,
                });

                let flat_bridi = bindings::lojban::nesy::ast_types::Bridi {
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
                    ast::SentenceConnective::Afterthought {
                        left_negated,
                        connective: c,
                        right_negated,
                    } => {
                        let wit_conn = match c {
                            ast::Connective::Je => wit::Connective::Je,
                            ast::Connective::Ja => wit::Connective::Ja,
                            ast::Connective::Jo => wit::Connective::Jo,
                            ast::Connective::Ju => wit::Connective::Ju,
                        };
                        WasmConn::Afterthought((left_negated, wit_conn, right_negated))
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
            ast::Selbri::Abstraction(kind, inner_bridi) => {
                // Inner bridi goes into sentences (NOT a root —
                // same pattern as rel clause bodies).
                let body_idx = self.buffer.sentences.len() as u32;
                self.push_sentence(*inner_bridi);
                let wit_kind = match kind {
                    ast::AbstractionKind::Nu => wit::AbstractionKind::Nu,
                    ast::AbstractionKind::Duhu => wit::AbstractionKind::Duhu,
                    ast::AbstractionKind::Ka => wit::AbstractionKind::Ka,
                    ast::AbstractionKind::Ni => wit::AbstractionKind::Ni,
                    ast::AbstractionKind::Siho => wit::AbstractionKind::Siho,
                };
                wit::Selbri::Abstraction((wit_kind, body_idx))
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
            ast::Sumti::ModalTagged(modal, inner) => {
                let inner_id = self.push_sumti(*inner);
                let wit_modal = match modal {
                    ast::ModalTag::Fixed(bai) => {
                        let wit_bai = match bai {
                            ast::BaiTag::Ria => wit::BaiTag::Ria,
                            ast::BaiTag::Nii => wit::BaiTag::Nii,
                            ast::BaiTag::Mui => wit::BaiTag::Mui,
                            ast::BaiTag::Kiu => wit::BaiTag::Kiu,
                            ast::BaiTag::Pio => wit::BaiTag::Pio,
                            ast::BaiTag::Bai => wit::BaiTag::Bai,
                        };
                        wit::ModalTag::Fixed(wit_bai)
                    }
                    ast::ModalTag::Fio(selbri) => {
                        let selbri_id = self.push_selbri(*selbri);
                        wit::ModalTag::Fio(selbri_id)
                    }
                };
                wit::Sumti::ModalTagged((wit_modal, inner_id))
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
                    ast::RelClauseKind::Voi => wit::RelClauseKind::Voi,
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

            ast::Sumti::QuantifiedDescription { count, gadri, inner } => {
                let inner_id = self.push_selbri(*inner);
                let wit_gadri = match gadri {
                    ast::Gadri::Lo => wit::Gadri::Lo,
                    ast::Gadri::Le => wit::Gadri::Le,
                    _ => unreachable!("QuantifiedDescription only uses Lo or Le"),
                };
                wit::Sumti::QuantifiedDescription((count, wit_gadri, inner_id))
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
    use crate::bindings::lojban::nesy::ast_types as wit;

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
                    attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
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
                    attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("barda".into()),
                    head_terms: vec![],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
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
                            attitudinal: None,
                        })),
                    },
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
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
                    inner: Box::new(Selbri::Abstraction(AbstractionKind::Nu, Box::new(Sentence::Simple(Bridi {
                        selbri: Selbri::Root("klama".into()),
                        head_terms: vec![Sumti::ProSumti("mi".into())],
                        tail_terms: vec![],
                        negated: false,
                        tense: None,
                        attitudinal: None,
                    })))),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
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
                                attitudinal: None,
                            })),
                        },
                    }],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("prami".into()),
                    head_terms: vec![Sumti::ProSumti("mi".into())],
                    tail_terms: vec![Sumti::ProSumti("do".into())],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                }),
            ],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.sentences.len(), 3); // 1 rel body + 2 top-level
        assert_eq!(buffer.roots.len(), 2); // only the 2 top-level sentences
    }

    /// Abstraction kind is preserved through flattening
    #[test]
    fn test_abstraction_kind_flattening() {
        use crate::bindings::lojban::nesy::ast_types as wit;

        for (kind, wit_kind) in [
            (AbstractionKind::Nu, wit::AbstractionKind::Nu),
            (AbstractionKind::Duhu, wit::AbstractionKind::Duhu),
            (AbstractionKind::Ka, wit::AbstractionKind::Ka),
            (AbstractionKind::Ni, wit::AbstractionKind::Ni),
            (AbstractionKind::Siho, wit::AbstractionKind::Siho),
        ] {
            let parsed = ParsedText {
                sentences: vec![Sentence::Simple(Bridi {
                    selbri: Selbri::Root("barda".into()),
                    head_terms: vec![Sumti::Description {
                        gadri: Gadri::Lo,
                        inner: Box::new(Selbri::Abstraction(kind, Box::new(Sentence::Simple(Bridi {
                            selbri: Selbri::Root("klama".into()),
                            head_terms: vec![Sumti::ProSumti("mi".into())],
                            tail_terms: vec![],
                            negated: false,
                            tense: None,
                            attitudinal: None,
                        })))),
                    }],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                })]
            };

            let buffer = Flattener::flatten(parsed);

            // Find the abstraction selbri
            let abs = buffer.selbris.iter().find(|s| matches!(s, wit::Selbri::Abstraction(_)));
            match abs {
                Some(wit::Selbri::Abstraction((k, _))) => {
                    assert_eq!(*k, wit_kind, "abstraction kind mismatch for {:?}", kind);
                }
                other => panic!("expected Abstraction selbri for {:?}, got {:?}", kind, other),
            }
        }
    }

    /// Sumti::Connected flattens to wit::Sumti::Connected with correct indices
    #[test]
    fn test_connected_sumti_flattening() {
        use crate::bindings::lojban::nesy::ast_types as wit;

        // mi .e do klama → head: [Connected(mi, Je, false, do)], selbri: klama
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: Box::new(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: false,
                    right: Box::new(Sumti::ProSumti("do".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);

        // Should have 1 root sentence
        assert_eq!(buffer.roots.len(), 1);

        // Should have 3 sumtis: mi (0), do (1), Connected(0, Je, false, 1) (2)
        assert_eq!(buffer.sumtis.len(), 3);

        // Check the Connected sumti
        match &buffer.sumtis[2] {
            wit::Sumti::Connected((left_id, conn, negated, right_id)) => {
                assert_eq!(*left_id, 0); // mi
                assert_eq!(*conn, wit::Connective::Je);
                assert!(!negated);
                assert_eq!(*right_id, 1); // do
            }
            other => panic!("expected Connected sumti, got {:?}", other),
        }

        // Verify left and right are correct
        assert!(matches!(&buffer.sumtis[0], wit::Sumti::ProSumti(s) if s == "mi"));
        assert!(matches!(&buffer.sumtis[1], wit::Sumti::ProSumti(s) if s == "do"));

        // The bridi's head_terms should point to the Connected sumti (index 2)
        match &buffer.sentences[buffer.roots[0] as usize] {
            wit::Sentence::Simple(bridi) => {
                assert_eq!(bridi.head_terms, vec![2]);
            }
            other => panic!("expected Simple sentence, got {:?}", other),
        }
    }

    /// Negated sumti connective flattens correctly
    #[test]
    fn test_connected_sumti_negated_flattening() {
        use crate::bindings::lojban::nesy::ast_types as wit;

        // mi .e nai do klama
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: Box::new(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: true,
                    right: Box::new(Sumti::ProSumti("do".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        match &buffer.sumtis[2] {
            wit::Sumti::Connected((_, conn, negated, _)) => {
                assert_eq!(*conn, wit::Connective::Je);
                assert!(negated); // right_negated = true
            }
            other => panic!("expected Connected sumti, got {:?}", other),
        }
    }

    /// Chained connected sumti flattens with correct nesting
    #[test]
    fn test_chained_connected_sumti_flattening() {
        use crate::bindings::lojban::nesy::ast_types as wit;

        // mi .e (do .a di) → right-associative nesting
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: Box::new(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: false,
                    right: Box::new(Sumti::Connected {
                        left: Box::new(Sumti::ProSumti("do".into())),
                        connective: Connective::Ja,
                        right_negated: false,
                        right: Box::new(Sumti::ProSumti("di".into())),
                    }),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);

        // 5 sumtis: mi(0), do(1), di(2), inner Connected(1,Ja,false,2)=3, outer Connected(0,Je,false,3)=4
        assert_eq!(buffer.sumtis.len(), 5);

        // Inner: Connected(do=1, Ja, false, di=2)
        match &buffer.sumtis[3] {
            wit::Sumti::Connected((left, conn, neg, right)) => {
                assert_eq!(*left, 1);
                assert_eq!(*conn, wit::Connective::Ja);
                assert!(!neg);
                assert_eq!(*right, 2);
            }
            other => panic!("expected inner Connected, got {:?}", other),
        }

        // Outer: Connected(mi=0, Je, false, inner=3)
        match &buffer.sumtis[4] {
            wit::Sumti::Connected((left, conn, neg, right)) => {
                assert_eq!(*left, 0);
                assert_eq!(*conn, wit::Connective::Je);
                assert!(!neg);
                assert_eq!(*right, 3);
            }
            other => panic!("expected outer Connected, got {:?}", other),
        }
    }

    #[test]
    fn test_modal_tagged_flattening() {
        // klama ri'a mi → tail_terms: [ModalTagged(Fixed(Ria), ProSumti("mi"))]
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![],
                tail_terms: vec![Sumti::ModalTagged(
                    ModalTag::Fixed(BaiTag::Ria),
                    Box::new(Sumti::ProSumti("mi".into())),
                )],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.roots.len(), 1);
        // sumtis should have 2 entries: inner "mi" and the ModalTagged wrapper
        assert_eq!(buffer.sumtis.len(), 2);
        match &buffer.sumtis[1] {
            wit::Sumti::ModalTagged((modal_tag, inner_id)) => {
                assert!(matches!(modal_tag, wit::ModalTag::Fixed(wit::BaiTag::Ria)));
                assert_eq!(*inner_id, 0); // inner is first sumti
                assert!(matches!(&buffer.sumtis[0], wit::Sumti::ProSumti(s) if s == "mi"));
            }
            other => panic!("expected ModalTagged, got {:?}", other),
        }
    }

    #[test]
    fn test_quantified_description_flattening() {
        // re lo gerku cu barda → QuantifiedDescription(2, Lo, gerku)
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::QuantifiedDescription {
                    count: 2,
                    gadri: Gadri::Lo,
                    inner: Box::new(Selbri::Root("gerku".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.roots.len(), 1);
        assert_eq!(buffer.sumtis.len(), 1);
        match &buffer.sumtis[0] {
            wit::Sumti::QuantifiedDescription((count, gadri, selbri_id)) => {
                assert_eq!(*count, 2);
                assert_eq!(*gadri, wit::Gadri::Lo);
                assert!(matches!(&buffer.selbris[*selbri_id as usize], wit::Selbri::Root(s) if s == "gerku"));
            }
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
    }

    #[test]
    fn test_fio_flattening() {
        // barda fi'o klama mi → tail: [ModalTagged(Fio(Root("klama")), ProSumti("mi"))]
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![],
                tail_terms: vec![Sumti::ModalTagged(
                    ModalTag::Fio(Box::new(Selbri::Root("klama".into()))),
                    Box::new(Sumti::ProSumti("mi".into())),
                )],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(parsed);
        assert_eq!(buffer.sumtis.len(), 2);
        match &buffer.sumtis[1] {
            wit::Sumti::ModalTagged((modal_tag, inner_id)) => {
                match modal_tag {
                    wit::ModalTag::Fio(selbri_id) => {
                        assert!(matches!(&buffer.selbris[*selbri_id as usize], wit::Selbri::Root(s) if s == "klama"));
                    }
                    other => panic!("expected Fio modal tag, got {:?}", other),
                }
                assert_eq!(*inner_id, 0);
            }
            other => panic!("expected ModalTagged, got {:?}", other),
        }
    }
}

/// Full-pipeline tests: raw Lojban text → lex → preprocess → parse.
/// These test the integration of lexer + preprocessor + parser for
/// sumti connectives, verifying that the lexer correctly tokenizes
/// the `.e`, `.a`, `.o`, `.u` patterns.
#[cfg(test)]
mod pipeline_tests {
    use crate::ast::*;
    use crate::grammar::parse_tokens_to_ast;
    use crate::lexer::tokenize;
    use crate::preprocessor::preprocess;

    fn parse(input: &str) -> ParsedText {
        let raw = tokenize(input);
        let normalized = preprocess(raw.into_iter(), input);
        let result = parse_tokens_to_ast(&normalized, input);
        assert!(
            result.errors.is_empty(),
            "unexpected parse errors for {:?}: {:?}",
            input,
            result.errors
        );
        result.parsed
    }

    fn as_bridi(sentence: &Sentence) -> &Bridi {
        match sentence {
            Sentence::Simple(b) => b,
            other => panic!("expected Sentence::Simple, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_e() {
        let p = parse("mi .e do klama");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective,
                right_negated,
                right,
            } => {
                assert_eq!(**left, Sumti::ProSumti("mi".into()));
                assert_eq!(*connective, Connective::Je);
                assert!(!right_negated);
                assert_eq!(**right, Sumti::ProSumti("do".into()));
            }
            other => panic!("expected Connected(.e), got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("klama".into()));
    }

    #[test]
    fn pipeline_sumti_connective_a() {
        let p = parse("mi .a do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected { connective: Connective::Ja, .. } => {}
            other => panic!("expected Connected(.a), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_o() {
        let p = parse("mi .o do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected { connective: Connective::Jo, .. } => {}
            other => panic!("expected Connected(.o), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_u() {
        let p = parse("mi .u do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected { connective: Connective::Ju, .. } => {}
            other => panic!("expected Connected(.u), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_enai() {
        let p = parse("mi .enai do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Je,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.enai), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_anai() {
        let p = parse("mi .anai do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ja,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.anai), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_onai() {
        let p = parse("mi .onai do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Jo,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.onai), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_unai() {
        let p = parse("mi .unai do klama");
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ju,
                right_negated: true,
                ..
            } => {}
            other => panic!("expected Connected(.unai), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_descriptions_connected() {
        let p = parse("lo gerku .e lo mlatu cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(left.as_ref(), Sumti::Description { gadri: Gadri::Lo, .. }));
                assert!(matches!(right.as_ref(), Sumti::Description { gadri: Gadri::Lo, .. }));
            }
            other => panic!("expected Connected descriptions, got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn pipeline_connective_in_tail() {
        let p = parse("mi nelci lo gerku .e lo mlatu");
        let s = as_bridi(&p.sentences[0]);
        match &s.tail_terms[0] {
            Sumti::Connected { connective: Connective::Je, .. } => {}
            other => panic!("expected Connected in tail, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_dot_i_not_connective() {
        let p = parse("mi klama .i do prami");
        assert_eq!(p.sentences.len(), 2);
        assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("klama".into()));
        assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn pipeline_chained_connectives() {
        // mi .e do .e di klama → right-associative nesting
        let p = parse("mi .e do .e di klama");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert_eq!(**left, Sumti::ProSumti("mi".into()));
                assert!(matches!(right.as_ref(), Sumti::Connected { .. }));
            }
            other => panic!("expected outer Connected, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_names_connected() {
        let p = parse("la .djan. .e la .meris. cu klama");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(left.as_ref(), Sumti::Name(_)));
                assert!(matches!(right.as_ref(), Sumti::Name(_)));
            }
            other => panic!("expected Connected names, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_multi_sentence_with_connectives() {
        let p = parse("mi .e do klama .i lo gerku .a lo mlatu cu barda");
        assert_eq!(p.sentences.len(), 2);
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected { connective: Connective::Je, .. } => {}
            other => panic!("sentence 1: expected .e, got {:?}", other),
        }
        match &as_bridi(&p.sentences[1]).head_terms[0] {
            Sumti::Connected { connective: Connective::Ja, .. } => {}
            other => panic!("sentence 2: expected .a, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_connective_both_positions() {
        // mi .e do prami lo gerku .a lo mlatu
        let p = parse("mi .e do prami lo gerku .a lo mlatu");
        let s = as_bridi(&p.sentences[0]);
        assert!(matches!(&s.head_terms[0], Sumti::Connected { connective: Connective::Je, .. }));
        assert!(matches!(&s.tail_terms[0], Sumti::Connected { connective: Connective::Ja, .. }));
    }

    // ─── Abstraction types pipeline tests ──────────────────────────

    #[test]
    fn pipeline_duhu_abstraction() {
        let p = parse("lo du'u mi klama kei cu barda");
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(inner.as_ref(), Selbri::Abstraction(AbstractionKind::Duhu, _)));
            }
            other => panic!("expected Description with Duhu abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_ka_with_ceu() {
        let p = parse("lo ka ce'u melbi kei cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                match inner.as_ref() {
                    Selbri::Abstraction(AbstractionKind::Ka, body) => {
                        match body.as_ref() {
                            Sentence::Simple(inner_bridi) => {
                                assert_eq!(inner_bridi.head_terms[0], Sumti::ProSumti("ce'u".into()));
                            }
                            other => panic!("expected Simple, got {:?}", other),
                        }
                    }
                    other => panic!("expected Ka abstraction, got {:?}", other),
                }
            }
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_ni_abstraction() {
        let p = parse("lo ni mi gleki kei cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(inner.as_ref(), Selbri::Abstraction(AbstractionKind::Ni, _)));
            }
            other => panic!("expected Description with Ni abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_siho_abstraction() {
        let p = parse("lo si'o mi klama kei cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(inner.as_ref(), Selbri::Abstraction(AbstractionKind::Siho, _)));
            }
            other => panic!("expected Description with Siho abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_nu_still_works() {
        let p = parse("lo nu mi klama kei cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(inner.as_ref(), Selbri::Abstraction(AbstractionKind::Nu, _)));
            }
            other => panic!("expected Description with Nu abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_bai_ria() {
        let p = parse("mi klama ri'a lo nu brife");
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), inner) => {
                assert!(matches!(inner.as_ref(), Sumti::Description { .. }));
            }
            other => panic!("expected ModalTagged(Ria, Description), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_fio_klama() {
        let p = parse("mi barda fi'o klama fe'u do");
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fio(selbri), inner) => {
                assert_eq!(**selbri, Selbri::Root("klama".into()));
                assert_eq!(**inner, Sumti::ProSumti("do".into()));
            }
            other => panic!("expected ModalTagged(Fio(klama), do), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_multiple_bai() {
        let p = parse("mi klama ri'a do pi'o lo tanxe");
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.tail_terms.len(), 2);
        assert!(matches!(
            &s.tail_terms[0],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), _)
        ));
        assert!(matches!(
            &s.tail_terms[1],
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Pio), _)
        ));
    }

    // ─── Numeric Quantifier pipeline tests ──────────────────────────

    #[test]
    fn pipeline_re_lo_gerku() {
        let p = parse("re lo gerku cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, gadri, inner } => {
                assert_eq!(*count, 2);
                assert_eq!(*gadri, Gadri::Lo);
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn pipeline_suho_lo_gerku() {
        let p = parse("su'o lo gerku cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { gadri: Gadri::Lo, inner } => {
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Description(Lo), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_no_lo_gerku() {
        let p = parse("no lo gerku cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => {
                assert_eq!(*count, 0);
            }
            other => panic!("expected QuantifiedDescription with count 0, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_multi_digit_quantifier() {
        let p = parse("pa re lo gerku cu barda");
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => {
                assert_eq!(*count, 12); // pa=1, re=2 → 12
            }
            other => panic!("expected QuantifiedDescription with count 12, got {:?}", other),
        }
    }

    // ─── Error recovery tests ──────────────────────────────────────

    use crate::grammar::ParseResult;

    fn parse_result(input: &str) -> ParseResult {
        let raw = tokenize(input);
        let normalized = preprocess(raw.into_iter(), input);
        parse_tokens_to_ast(&normalized, input)
    }

    #[test]
    fn pipeline_error_recovery_skips_bad_sentence() {
        // Middle sentence "ke ke ke" is malformed; first and third are fine
        let r = parse_result("mi klama .i ke ke ke .i do prami mi");
        assert_eq!(r.parsed.sentences.len(), 2);
        assert_eq!(r.errors.len(), 1);
        let s1 = as_bridi(&r.parsed.sentences[0]);
        assert_eq!(s1.selbri, Selbri::Root("klama".into()));
        let s2 = as_bridi(&r.parsed.sentences[1]);
        assert_eq!(s2.selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn pipeline_error_recovery_all_fail() {
        let r = parse_result("ke ke .i ke ke");
        assert_eq!(r.parsed.sentences.len(), 0);
        assert_eq!(r.errors.len(), 2);
    }

    #[test]
    fn pipeline_error_recovery_empty_input() {
        let r = parse_result("");
        assert_eq!(r.parsed.sentences.len(), 0);
        assert_eq!(r.errors.len(), 1);
        assert!(r.errors[0].message.contains("empty input"));
    }

    #[test]
    fn pipeline_error_reports_line_column() {
        // Error on line 2 ("ke ke ke" is malformed)
        let r = parse_result("mi klama\n.i ke ke ke\n.i do prami mi");
        assert_eq!(r.parsed.sentences.len(), 2);
        assert_eq!(r.errors.len(), 1);
        assert_eq!(r.errors[0].line, 2, "error should be on line 2");
        assert!(r.errors[0].column > 0, "column should be positive");
    }

    #[test]
    fn pipeline_error_reports_first_line() {
        let r = parse_result("ke ke ke");
        assert_eq!(r.errors.len(), 1);
        assert_eq!(r.errors[0].line, 1);
    }

    #[test]
    fn pipeline_error_display_format() {
        let r = parse_result("ke ke ke");
        let msg = r.errors[0].to_string();
        // Format should be "line:col: message"
        assert!(msg.contains(':'), "error display should contain line:col separator");
    }
}
