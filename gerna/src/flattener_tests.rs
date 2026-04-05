    use crate::ast::*;
    use nibli_types::ast as flat;
    use bumpalo::Bump;

    // Re-use the Flattener (it's private, so these tests must live in lib.rs
    // or you must make Flattener pub(crate)).

    use super::Flattener;

    /// Two simple sentences: "klama .i prami"
    /// Both must appear as roots.
    #[test]
    fn test_multi_sentence_produces_two_roots() {
        let _arena = Bump::new();
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

        let buffer = Flattener::flatten(&parsed);
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
        let _arena = Bump::new();
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

        let buffer = Flattener::flatten(&parsed);
        assert_eq!(buffer.roots.len(), 3);
    }

    /// Single sentence with a relative clause.
    /// The rel clause body is in `sentences` but must NOT be a root.
    /// Only 1 root expected.
    #[test]
    fn test_rel_clause_body_is_not_a_root() {
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::Restricted {
                    inner: arena.alloc(Sumti::Description {
                        gadri: Gadri::Lo,
                        inner: arena.alloc(Selbri::Root("gerku".into())),
                    }),
                    clause: RelClause {
                        kind: RelClauseKind::Poi,
                        body: arena.alloc(Sentence::Simple(Bridi {
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

        let buffer = Flattener::flatten(&parsed);
        // sentences has 2 entries (rel clause body + top-level), but only 1 root
        assert_eq!(buffer.sentences.len(), 2);
        assert_eq!(buffer.roots.len(), 1);
    }

    /// nu abstraction body must NOT be a root.
    #[test]
    fn test_nu_abstraction_body_is_not_a_root() {
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::Description {
                    gadri: Gadri::Lo,
                    inner: arena.alloc(Selbri::Abstraction(
                        AbstractionKind::Nu,
                        arena.alloc(Sentence::Simple(Bridi {
                            selbri: Selbri::Root("klama".into()),
                            head_terms: vec![Sumti::ProSumti("mi".into())],
                            tail_terms: vec![],
                            negated: false,
                            tense: None,
                            attitudinal: None,
                        })),
                    )),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);
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
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![
                Sentence::Simple(Bridi {
                    selbri: Selbri::Root("klama".into()),
                    head_terms: vec![Sumti::Restricted {
                        inner: arena.alloc(Sumti::Description {
                            gadri: Gadri::Lo,
                            inner: arena.alloc(Selbri::Root("gerku".into())),
                        }),
                        clause: RelClause {
                            kind: RelClauseKind::Poi,
                            body: arena.alloc(Sentence::Simple(Bridi {
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

        let buffer = Flattener::flatten(&parsed);
        assert_eq!(buffer.sentences.len(), 3); // 1 rel body + 2 top-level
        assert_eq!(buffer.roots.len(), 2); // only the 2 top-level sentences
    }

    /// Abstraction kind is preserved through flattening
    #[test]
    fn test_abstraction_kind_flattening() {
        use nibli_types::ast as flat;

        for (kind, wit_kind) in [
            (AbstractionKind::Nu, flat::AbstractionKind::Nu),
            (AbstractionKind::Duhu, flat::AbstractionKind::Duhu),
            (AbstractionKind::Ka, flat::AbstractionKind::Ka),
            (AbstractionKind::Ni, flat::AbstractionKind::Ni),
            (AbstractionKind::Siho, flat::AbstractionKind::Siho),
        ] {
            let arena = Bump::new();
            let parsed = ParsedText {
                sentences: vec![Sentence::Simple(Bridi {
                    selbri: Selbri::Root("barda".into()),
                    head_terms: vec![Sumti::Description {
                        gadri: Gadri::Lo,
                        inner: arena.alloc(Selbri::Abstraction(
                            kind,
                            arena.alloc(Sentence::Simple(Bridi {
                                selbri: Selbri::Root("klama".into()),
                                head_terms: vec![Sumti::ProSumti("mi".into())],
                                tail_terms: vec![],
                                negated: false,
                                tense: None,
                                attitudinal: None,
                            })),
                        )),
                    }],
                    tail_terms: vec![],
                    negated: false,
                    tense: None,
                    attitudinal: None,
                })],
            };

            let buffer = Flattener::flatten(&parsed);

            // Find the abstraction selbri
            let abs = buffer
                .selbris
                .iter()
                .find(|s| matches!(s, flat::Selbri::Abstraction(_)));
            match abs {
                Some(flat::Selbri::Abstraction((k, _))) => {
                    assert_eq!(*k, wit_kind, "abstraction kind mismatch for {:?}", kind);
                }
                other => panic!(
                    "expected Abstraction selbri for {:?}, got {:?}",
                    kind, other
                ),
            }
        }
    }

    /// Sumti::Connected flattens to flat::Sumti::Connected with correct indices
    #[test]
    fn test_connected_sumti_flattening() {
        use nibli_types::ast as flat;

        // mi .e do klama → head: [Connected(mi, Je, false, do)], selbri: klama
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: arena.alloc(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: false,
                    right: arena.alloc(Sumti::ProSumti("do".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);

        // Should have 1 root sentence
        assert_eq!(buffer.roots.len(), 1);

        // Should have 3 sumtis: mi (0), do (1), Connected(0, Je, false, 1) (2)
        assert_eq!(buffer.sumtis.len(), 3);

        // Check the Connected sumti
        match &buffer.sumtis[2] {
            flat::Sumti::Connected((left_id, conn, negated, right_id)) => {
                assert_eq!(*left_id, 0); // mi
                assert_eq!(*conn, flat::Connective::Je);
                assert!(!negated);
                assert_eq!(*right_id, 1); // do
            }
            other => panic!("expected Connected sumti, got {:?}", other),
        }

        // Verify left and right are correct
        assert!(matches!(&buffer.sumtis[0], flat::Sumti::ProSumti(s) if s == "mi"));
        assert!(matches!(&buffer.sumtis[1], flat::Sumti::ProSumti(s) if s == "do"));

        // The bridi's head_terms should point to the Connected sumti (index 2)
        match &buffer.sentences[buffer.roots[0] as usize] {
            flat::Sentence::Simple(bridi) => {
                assert_eq!(bridi.head_terms, vec![2]);
            }
            other => panic!("expected Simple sentence, got {:?}", other),
        }
    }

    /// Negated sumti connective flattens correctly
    #[test]
    fn test_connected_sumti_negated_flattening() {
        use nibli_types::ast as flat;

        // mi .e nai do klama
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: arena.alloc(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: true,
                    right: arena.alloc(Sumti::ProSumti("do".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);
        match &buffer.sumtis[2] {
            flat::Sumti::Connected((_, conn, negated, _)) => {
                assert_eq!(*conn, flat::Connective::Je);
                assert!(negated); // right_negated = true
            }
            other => panic!("expected Connected sumti, got {:?}", other),
        }
    }

    /// Chained connected sumti flattens with correct nesting
    #[test]
    fn test_chained_connected_sumti_flattening() {
        use nibli_types::ast as flat;

        // mi .e (do .a di) → right-associative nesting
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![Sumti::Connected {
                    left: arena.alloc(Sumti::ProSumti("mi".into())),
                    connective: Connective::Je,
                    right_negated: false,
                    right: arena.alloc(Sumti::Connected {
                        left: arena.alloc(Sumti::ProSumti("do".into())),
                        connective: Connective::Ja,
                        right_negated: false,
                        right: arena.alloc(Sumti::ProSumti("di".into())),
                    }),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);

        // 5 sumtis: mi(0), do(1), di(2), inner Connected(1,Ja,false,2)=3, outer Connected(0,Je,false,3)=4
        assert_eq!(buffer.sumtis.len(), 5);

        // Inner: Connected(do=1, Ja, false, di=2)
        match &buffer.sumtis[3] {
            flat::Sumti::Connected((left, conn, neg, right)) => {
                assert_eq!(*left, 1);
                assert_eq!(*conn, flat::Connective::Ja);
                assert!(!neg);
                assert_eq!(*right, 2);
            }
            other => panic!("expected inner Connected, got {:?}", other),
        }

        // Outer: Connected(mi=0, Je, false, inner=3)
        match &buffer.sumtis[4] {
            flat::Sumti::Connected((left, conn, neg, right)) => {
                assert_eq!(*left, 0);
                assert_eq!(*conn, flat::Connective::Je);
                assert!(!neg);
                assert_eq!(*right, 3);
            }
            other => panic!("expected outer Connected, got {:?}", other),
        }
    }

    #[test]
    fn test_modal_tagged_flattening() {
        // klama ri'a mi → tail_terms: [ModalTagged(Fixed(Ria), ProSumti("mi"))]
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("klama".into()),
                head_terms: vec![],
                tail_terms: vec![Sumti::ModalTagged(
                    ModalTag::Fixed(BaiTag::Ria),
                    arena.alloc(Sumti::ProSumti("mi".into())),
                )],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);
        assert_eq!(buffer.roots.len(), 1);
        // sumtis should have 2 entries: inner "mi" and the ModalTagged wrapper
        assert_eq!(buffer.sumtis.len(), 2);
        match &buffer.sumtis[1] {
            flat::Sumti::ModalTagged((modal_tag, inner_id)) => {
                assert!(matches!(modal_tag, flat::ModalTag::Fixed(flat::BaiTag::Ria)));
                assert_eq!(*inner_id, 0); // inner is first sumti
                assert!(matches!(&buffer.sumtis[0], flat::Sumti::ProSumti(s) if s == "mi"));
            }
            other => panic!("expected ModalTagged, got {:?}", other),
        }
    }

    #[test]
    fn test_quantified_description_flattening() {
        // re lo gerku cu barda → QuantifiedDescription(2, Lo, gerku)
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![Sumti::QuantifiedDescription {
                    count: 2,
                    gadri: Gadri::Lo,
                    inner: arena.alloc(Selbri::Root("gerku".into())),
                }],
                tail_terms: vec![],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);
        assert_eq!(buffer.roots.len(), 1);
        assert_eq!(buffer.sumtis.len(), 1);
        match &buffer.sumtis[0] {
            flat::Sumti::QuantifiedDescription((count, gadri, selbri_id)) => {
                assert_eq!(*count, 2);
                assert_eq!(*gadri, flat::Gadri::Lo);
                assert!(
                    matches!(&buffer.selbris[*selbri_id as usize], flat::Selbri::Root(s) if s == "gerku")
                );
            }
            other => panic!("expected QuantifiedDescription, got {:?}", other),
        }
    }

    #[test]
    fn test_fio_flattening() {
        // barda fi'o klama mi → tail: [ModalTagged(Fio(Root("klama")), ProSumti("mi"))]
        let arena = Bump::new();
        let parsed = ParsedText {
            sentences: vec![Sentence::Simple(Bridi {
                selbri: Selbri::Root("barda".into()),
                head_terms: vec![],
                tail_terms: vec![Sumti::ModalTagged(
                    ModalTag::Fio(arena.alloc(Selbri::Root("klama".into()))),
                    arena.alloc(Sumti::ProSumti("mi".into())),
                )],
                negated: false,
                tense: None,
                attitudinal: None,
            })],
        };

        let buffer = Flattener::flatten(&parsed);
        assert_eq!(buffer.sumtis.len(), 2);
        match &buffer.sumtis[1] {
            flat::Sumti::ModalTagged((modal_tag, inner_id)) => {
                match modal_tag {
                    flat::ModalTag::Fio(selbri_id) => {
                        assert!(
                            matches!(&buffer.selbris[*selbri_id as usize], flat::Selbri::Root(s) if s == "klama")
                        );
                    }
                    other => panic!("expected Fio modal tag, got {:?}", other),
                }
                assert_eq!(*inner_id, 0);
            }
            other => panic!("expected ModalTagged, got {:?}", other),
        }
    }
