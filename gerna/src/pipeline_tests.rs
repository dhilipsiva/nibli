    use crate::ast::*;
    use crate::grammar::parse_tokens_to_ast;
    use crate::lexer::tokenize;
    use crate::preprocessor::preprocess;
    use bumpalo::Bump;

    fn parse<'a>(input: &str, arena: &'a Bump) -> ParsedText<'a> {
        let raw = tokenize(input);
        let normalized = preprocess(raw.into_iter(), input);
        let result = parse_tokens_to_ast(&normalized, input, arena);
        assert!(
            result.errors.is_empty(),
            "unexpected parse errors for {:?}: {:?}",
            input,
            result.errors
        );
        result.parsed
    }

    fn as_bridi<'a>(sentence: &'a Sentence<'a>) -> &'a Bridi<'a> {
        match sentence {
            Sentence::Simple(b) => b,
            other => panic!("expected Sentence::Simple, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_e() {
        let arena = Bump::new();
        let p = parse("mi .e do klama", &arena);
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
        let arena = Bump::new();
        let p = parse("mi .a do klama", &arena);
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ja,
                ..
            } => {}
            other => panic!("expected Connected(.a), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_o() {
        let arena = Bump::new();
        let p = parse("mi .o do klama", &arena);
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Jo,
                ..
            } => {}
            other => panic!("expected Connected(.o), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_u() {
        let arena = Bump::new();
        let p = parse("mi .u do klama", &arena);
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ju,
                ..
            } => {}
            other => panic!("expected Connected(.u), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_sumti_connective_enai() {
        let arena = Bump::new();
        let p = parse("mi .enai do klama", &arena);
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
        let arena = Bump::new();
        let p = parse("mi .anai do klama", &arena);
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
        let arena = Bump::new();
        let p = parse("mi .onai do klama", &arena);
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
        let arena = Bump::new();
        let p = parse("mi .unai do klama", &arena);
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
        let arena = Bump::new();
        let p = parse("lo gerku .e lo mlatu cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(
                    *left,
                    Sumti::Description {
                        gadri: Gadri::Lo,
                        ..
                    }
                ));
                assert!(matches!(
                    *right,
                    Sumti::Description {
                        gadri: Gadri::Lo,
                        ..
                    }
                ));
            }
            other => panic!("expected Connected descriptions, got {:?}", other),
        }
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
    }

    #[test]
    fn pipeline_connective_in_tail() {
        let arena = Bump::new();
        let p = parse("mi nelci lo gerku .e lo mlatu", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.tail_terms[0] {
            Sumti::Connected {
                connective: Connective::Je,
                ..
            } => {}
            other => panic!("expected Connected in tail, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_dot_i_not_connective() {
        let arena = Bump::new();
        let p = parse("mi klama .i do prami", &arena);
        assert_eq!(p.sentences.len(), 2);
        assert_eq!(
            as_bridi(&p.sentences[0]).selbri,
            Selbri::Root("klama".into())
        );
        assert_eq!(
            as_bridi(&p.sentences[1]).selbri,
            Selbri::Root("prami".into())
        );
    }

    #[test]
    fn pipeline_chained_connectives() {
        // mi .e do .e di klama → right-associative nesting
        let arena = Bump::new();
        let p = parse("mi .e do .e di klama", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert_eq!(**left, Sumti::ProSumti("mi".into()));
                assert!(matches!(*right, Sumti::Connected { .. }));
            }
            other => panic!("expected outer Connected, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_names_connected() {
        let arena = Bump::new();
        let p = parse("la .djan. .e la .meris. cu klama", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Connected {
                left,
                connective: Connective::Je,
                right,
                ..
            } => {
                assert!(matches!(*left, Sumti::Name(_)));
                assert!(matches!(*right, Sumti::Name(_)));
            }
            other => panic!("expected Connected names, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_multi_sentence_with_connectives() {
        let arena = Bump::new();
        let p = parse("mi .e do klama .i lo gerku .a lo mlatu cu barda", &arena);
        assert_eq!(p.sentences.len(), 2);
        match &as_bridi(&p.sentences[0]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Je,
                ..
            } => {}
            other => panic!("sentence 1: expected .e, got {:?}", other),
        }
        match &as_bridi(&p.sentences[1]).head_terms[0] {
            Sumti::Connected {
                connective: Connective::Ja,
                ..
            } => {}
            other => panic!("sentence 2: expected .a, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_connective_both_positions() {
        // mi .e do prami lo gerku .a lo mlatu
        let arena = Bump::new();
        let p = parse("mi .e do prami lo gerku .a lo mlatu", &arena);
        let s = as_bridi(&p.sentences[0]);
        assert!(matches!(
            &s.head_terms[0],
            Sumti::Connected {
                connective: Connective::Je,
                ..
            }
        ));
        assert!(matches!(
            &s.tail_terms[0],
            Sumti::Connected {
                connective: Connective::Ja,
                ..
            }
        ));
    }

    // ─── Abstraction types pipeline tests ──────────────────────────

    #[test]
    fn pipeline_duhu_abstraction() {
        let arena = Bump::new();
        let p = parse("lo du'u mi klama kei cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.selbri, Selbri::Root("barda".into()));
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(
                    *inner,
                    Selbri::Abstraction(AbstractionKind::Duhu, _)
                ));
            }
            other => panic!(
                "expected Description with Duhu abstraction, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn pipeline_ka_with_ceu() {
        let arena = Bump::new();
        let p = parse("lo ka ce'u melbi kei cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => match *inner {
                Selbri::Abstraction(AbstractionKind::Ka, body) => match *body {
                    Sentence::Simple(inner_bridi) => {
                        assert_eq!(inner_bridi.head_terms[0], Sumti::ProSumti("ce'u".into()));
                    }
                    other => panic!("expected Simple, got {:?}", other),
                },
                other => panic!("expected Ka abstraction, got {:?}", other),
            },
            other => panic!("expected Description, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_ni_abstraction() {
        let arena = Bump::new();
        let p = parse("lo ni mi gleki kei cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(
                    *inner,
                    Selbri::Abstraction(AbstractionKind::Ni, _)
                ));
            }
            other => panic!("expected Description with Ni abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_siho_abstraction() {
        let arena = Bump::new();
        let p = parse("lo si'o mi klama kei cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(
                    *inner,
                    Selbri::Abstraction(AbstractionKind::Siho, _)
                ));
            }
            other => panic!(
                "expected Description with Siho abstraction, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn pipeline_nu_still_works() {
        let arena = Bump::new();
        let p = parse("lo nu mi klama kei cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description { inner, .. } => {
                assert!(matches!(
                    *inner,
                    Selbri::Abstraction(AbstractionKind::Nu, _)
                ));
            }
            other => panic!("expected Description with Nu abstraction, got {:?}", other),
        }
    }

    #[test]
    fn pipeline_bai_ria() {
        let arena = Bump::new();
        let p = parse("mi klama ri'a lo nu brife", &arena);
        let s = as_bridi(&p.sentences[0]);
        assert_eq!(s.head_terms.len(), 1);
        assert_eq!(s.tail_terms.len(), 1);
        match &s.tail_terms[0] {
            Sumti::ModalTagged(ModalTag::Fixed(BaiTag::Ria), inner) => {
                assert!(matches!(*inner, Sumti::Description { .. }));
            }
            other => panic!("expected ModalTagged(Ria, Description), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_fio_klama() {
        let arena = Bump::new();
        let p = parse("mi barda fi'o klama fe'u do", &arena);
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
        let arena = Bump::new();
        let p = parse("mi klama ri'a do pi'o lo tanxe", &arena);
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
        let arena = Bump::new();
        let p = parse("re lo gerku cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription {
                count,
                gadri,
                inner,
            } => {
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
        let arena = Bump::new();
        let p = parse("su'o lo gerku cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::Description {
                gadri: Gadri::Lo,
                inner,
            } => {
                assert_eq!(**inner, Selbri::Root("gerku".into()));
            }
            other => panic!("expected Description(Lo), got {:?}", other),
        }
    }

    #[test]
    fn pipeline_no_lo_gerku() {
        let arena = Bump::new();
        let p = parse("no lo gerku cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => {
                assert_eq!(*count, 0);
            }
            other => panic!(
                "expected QuantifiedDescription with count 0, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn pipeline_multi_digit_quantifier() {
        let arena = Bump::new();
        let p = parse("pa re lo gerku cu barda", &arena);
        let s = as_bridi(&p.sentences[0]);
        match &s.head_terms[0] {
            Sumti::QuantifiedDescription { count, .. } => {
                assert_eq!(*count, 12); // pa=1, re=2 → 12
            }
            other => panic!(
                "expected QuantifiedDescription with count 12, got {:?}",
                other
            ),
        }
    }

    // ─── Error recovery tests ──────────────────────────────────────

    use crate::grammar::ParseResult;

    fn parse_result<'a>(input: &str, arena: &'a Bump) -> ParseResult<'a> {
        let raw = tokenize(input);
        let normalized = preprocess(raw.into_iter(), input);
        parse_tokens_to_ast(&normalized, input, arena)
    }

    #[test]
    fn pipeline_error_recovery_skips_bad_sentence() {
        // Middle sentence "ke ke ke" is malformed; first and third are fine
        let arena = Bump::new();
        let r = parse_result("mi klama .i ke ke ke .i do prami mi", &arena);
        assert_eq!(r.parsed.sentences.len(), 2);
        assert_eq!(r.errors.len(), 1);
        let s1 = as_bridi(&r.parsed.sentences[0]);
        assert_eq!(s1.selbri, Selbri::Root("klama".into()));
        let s2 = as_bridi(&r.parsed.sentences[1]);
        assert_eq!(s2.selbri, Selbri::Root("prami".into()));
    }

    #[test]
    fn pipeline_error_recovery_all_fail() {
        let arena = Bump::new();
        let r = parse_result("ke ke .i ke ke", &arena);
        assert_eq!(r.parsed.sentences.len(), 0);
        assert_eq!(r.errors.len(), 2);
    }

    #[test]
    fn pipeline_error_recovery_empty_input() {
        let arena = Bump::new();
        let r = parse_result("", &arena);
        assert_eq!(r.parsed.sentences.len(), 0);
        assert_eq!(r.errors.len(), 1);
        assert!(r.errors[0].message.contains("empty input"));
    }

    #[test]
    fn pipeline_error_reports_line_column() {
        // Error on line 2 ("ke ke ke" is malformed)
        let arena = Bump::new();
        let r = parse_result("mi klama\n.i ke ke ke\n.i do prami mi", &arena);
        assert_eq!(r.parsed.sentences.len(), 2);
        assert_eq!(r.errors.len(), 1);
        assert_eq!(r.errors[0].line, 2, "error should be on line 2");
        assert!(r.errors[0].column > 0, "column should be positive");
    }

    #[test]
    fn pipeline_error_reports_first_line() {
        let arena = Bump::new();
        let r = parse_result("ke ke ke", &arena);
        assert_eq!(r.errors.len(), 1);
        assert_eq!(r.errors[0].line, 1);
    }

    #[test]
    fn pipeline_error_display_format() {
        let arena = Bump::new();
        let r = parse_result("ke ke ke", &arena);
        let msg = r.errors[0].to_string();
        // Format should be "line:col: message"
        assert!(
            msg.contains(':'),
            "error display should contain line:col separator"
        );
    }

    /// Verify every non-blank, non-comment line in readme.lojban parses cleanly.
    /// This is a regression test: if the parser breaks any readme line, this fails.
    #[test]
    fn pipeline_readme_lojban_all_lines_parse() {
        let readme = include_str!("../../readme.lojban");
        let mut failures = Vec::new();

        for (line_num, line) in readme.lines().enumerate() {
            let trimmed = line.trim();
            // Skip blank lines and # comments
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            let arena = Bump::new();
            let result = parse_result(trimmed, &arena);
            if !result.errors.is_empty() {
                failures.push(format!(
                    "line {}: {:?} → {:?}",
                    line_num + 1,
                    trimmed,
                    result.errors
                ));
            }
        }

        assert!(
            failures.is_empty(),
            "readme.lojban parse failures:\n{}",
            failures.join("\n")
        );
    }
