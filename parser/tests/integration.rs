use parser_test::ast::*;
use parser_test::grammar::parse_tokens_to_ast;
use parser_test::lexer::tokenize;
use parser_test::preprocessor::preprocess;

/// Parse a raw Lojban string through the full pipeline.
fn parse(input: &str) -> ParsedText {
    let raw = tokenize(input);
    let normalized = preprocess(raw.into_iter(), input);
    parse_tokens_to_ast(&normalized).expect(&format!("failed to parse: {:?}", input))
}

fn parse_err(input: &str) -> String {
    let raw = tokenize(input);
    let normalized = preprocess(raw.into_iter(), input);
    parse_tokens_to_ast(&normalized).unwrap_err()
}

/// Helper: extract Bridi from a Sentence::Simple
fn as_bridi(sentence: &Sentence) -> &Bridi {
    match sentence {
        Sentence::Simple(b) => b,
        other => panic!("expected Sentence::Simple, got {:?}", other),
    }
}

// ─── Basic sentences ─────────────────────────────────────────────

#[test]
fn simple_assertion() {
    let p = parse("mi prami do");
    assert_eq!(p.sentences.len(), 1);
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.selbri, Selbri::Root("prami".into()));
    assert_eq!(s.head_terms, vec![Sumti::ProSumti("mi".into())]);
    assert_eq!(s.tail_terms, vec![Sumti::ProSumti("do".into())]);
    assert!(!s.negated);
}

#[test]
fn with_cu_separator() {
    let p = parse("mi cu klama");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
    assert_eq!(s.head_terms.len(), 1);
}

#[test]
fn multiple_tail_sumti() {
    // mi klama do ti ta
    let p = parse("mi klama do ti ta");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.tail_terms.len(), 3);
}

// ─── .i sentence separator ───────────────────────────────────────

#[test]
fn two_sentences() {
    let p = parse("mi prami do .i do prami mi");
    assert_eq!(p.sentences.len(), 2);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("prami".into()));
    assert_eq!(
        as_bridi(&p.sentences[0]).head_terms,
        vec![Sumti::ProSumti("mi".into())]
    );
    assert_eq!(
        as_bridi(&p.sentences[1]).head_terms,
        vec![Sumti::ProSumti("do".into())]
    );
}

#[test]
fn three_sentences() {
    let p = parse("mi prami do .i do nelci mi .i mi klama");
    assert_eq!(p.sentences.len(), 3);
}

// ─── Descriptions (lo/le) ────────────────────────────────────────

#[test]
fn lo_description() {
    let p = parse("mi nelci lo gerku");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.tail_terms.len(), 1);
    match &s.tail_terms[0] {
        Sumti::Description { gadri, inner } => {
            assert_eq!(*gadri, Gadri::Lo);
            assert_eq!(**inner, Selbri::Root("gerku".into()));
        }
        other => panic!("expected Description, got {:?}", other),
    }
}

#[test]
fn le_description() {
    let p = parse("mi nelci le mlatu");
    match &as_bridi(&p.sentences[0]).tail_terms[0] {
        Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::Le),
        other => panic!("expected Description with Le, got {:?}", other),
    }
}

#[test]
fn lo_with_ku() {
    let p = parse("lo gerku ku cu klama");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.head_terms.len(), 1);
    match &s.head_terms[0] {
        Sumti::Description { gadri, inner } => {
            assert_eq!(*gadri, Gadri::Lo);
            assert_eq!(**inner, Selbri::Root("gerku".into()));
        }
        other => panic!("expected Description, got {:?}", other),
    }
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
}

// ─── Names (la + cmevla) ────────────────────────────────────────

#[test]
fn la_name() {
    let p = parse("la .djan. cu klama");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.head_terms, vec![Sumti::Name("djan".into())]);
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
}

// ─── Place tags (fa/fe/fi/fo/fu) ─────────────────────────────────

#[test]
fn explicit_place_tags() {
    let p = parse("fe do fa mi prami");
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.head_terms.len(), 2);
    match &s.head_terms[0] {
        Sumti::Tagged(PlaceTag::Fe, inner) => {
            assert_eq!(**inner, Sumti::ProSumti("do".into()));
        }
        other => panic!("expected Tagged(Fe), got {:?}", other),
    }
    match &s.head_terms[1] {
        Sumti::Tagged(PlaceTag::Fa, inner) => {
            assert_eq!(**inner, Sumti::ProSumti("mi".into()));
        }
        other => panic!("expected Tagged(Fa), got {:?}", other),
    }
}

// ─── Negation (na) ───────────────────────────────────────────────

#[test]
fn bridi_negation() {
    let p = parse("mi na prami do");
    let s = as_bridi(&p.sentences[0]);
    assert!(s.negated);
    assert_eq!(s.selbri, Selbri::Root("prami".into()));
}

// ─── SE conversion ───────────────────────────────────────────────

#[test]
fn se_conversion() {
    let p = parse("do se prami mi");
    let s = as_bridi(&p.sentences[0]);
    match &s.selbri {
        Selbri::Converted(Conversion::Se, inner) => {
            assert_eq!(**inner, Selbri::Root("prami".into()));
        }
        other => panic!("expected Converted(Se), got {:?}", other),
    }
}

#[test]
fn te_conversion() {
    let p = parse("ti te klama do mi");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Converted(Conversion::Te, _) => {}
        other => panic!("expected Converted(Te), got {:?}", other),
    }
}

// ─── Tanru ───────────────────────────────────────────────────────

#[test]
fn simple_tanru() {
    // sutra gerku = fast-type-of dog
    let p = parse("mi sutra gerku");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Tanru(modifier, head) => {
            assert_eq!(**modifier, Selbri::Root("sutra".into()));
            assert_eq!(**head, Selbri::Root("gerku".into()));
        }
        other => panic!("expected Tanru, got {:?}", other),
    }
}

#[test]
fn triple_tanru_right_groups() {
    // barda sutra gerku = barda (sutra gerku) = big fast-dog
    let p = parse("mi barda sutra gerku");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Tanru(a, bc) => {
            assert_eq!(**a, Selbri::Root("barda".into()));
            match bc.as_ref() {
                Selbri::Tanru(b, c) => {
                    assert_eq!(**b, Selbri::Root("sutra".into()));
                    assert_eq!(**c, Selbri::Root("gerku".into()));
                }
                other => panic!("expected inner Tanru, got {:?}", other),
            }
        }
        other => panic!("expected outer Tanru, got {:?}", other),
    }
}

// ─── be/bei (sumti raising) ──────────────────────────────────────

#[test]
fn be_clause() {
    let p = parse("mi nelci be lo gerku");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::WithArgs { core, args } => {
            assert_eq!(**core, Selbri::Root("nelci".into()));
            assert_eq!(args.len(), 1);
        }
        other => panic!("expected WithArgs, got {:?}", other),
    }
}

#[test]
fn be_bei_clause() {
    let p = parse("mi klama be lo zarci bei do");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::WithArgs { core, args } => {
            assert_eq!(**core, Selbri::Root("klama".into()));
            assert_eq!(args.len(), 2);
        }
        other => panic!("expected WithArgs with 2 args, got {:?}", other),
    }
}

// ─── ke/ke'e (grouping) ─────────────────────────────────────────

#[test]
fn ke_grouping() {
    let p = parse("mi ke sutra gerku ke'e");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Grouped(inner) => match inner.as_ref() {
            Selbri::Tanru(_, _) => {}
            other => panic!("expected Tanru inside Grouped, got {:?}", other),
        },
        other => panic!("expected Grouped, got {:?}", other),
    }
}

// ─── Selbri connectives (je/ja/jo/ju) ────────────────────────────

#[test]
fn je_connective() {
    let p = parse("mi barda je xunre");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Connected {
            left,
            connective,
            right,
        } => {
            assert_eq!(**left, Selbri::Root("barda".into()));
            assert_eq!(*connective, Connective::Je);
            assert_eq!(**right, Selbri::Root("xunre".into()));
        }
        other => panic!("expected Connected(je), got {:?}", other),
    }
}

#[test]
fn ja_connective() {
    let p = parse("mi barda ja cmalu");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Connected { connective, .. } => {
            assert_eq!(*connective, Connective::Ja);
        }
        other => panic!("expected Connected(ja), got {:?}", other),
    }
}

// ─── Relative clauses (poi/noi) ──────────────────────────────────

#[test]
fn poi_relative_clause() {
    let p = parse("mi nelci lo gerku poi barda");
    let s = as_bridi(&p.sentences[0]);
    match &s.tail_terms[0] {
        Sumti::Restricted { inner, clause } => {
            assert_eq!(clause.kind, RelClauseKind::Poi);
            match inner.as_ref() {
                Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::Lo),
                other => panic!("expected Description inside Restricted, got {:?}", other),
            }
        }
        other => panic!("expected Restricted, got {:?}", other),
    }
}

// ─── zo'e (explicit unspecified) ─────────────────────────────────

#[test]
fn explicit_unspecified() {
    let p = parse("mi prami zo'e");
    assert_eq!(as_bridi(&p.sentences[0]).tail_terms, vec![Sumti::Unspecified]);
}

// ─── Metalinguistic operators (via preprocessor) ─────────────────

#[test]
fn si_erasure() {
    // "mi klama si prami do" → mi prami do (klama erased by si)
    let p = parse("mi klama si prami do");
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
}

#[test]
fn su_erasure() {
    // "mi klama su do prami mi" → do prami mi (everything before su erased)
    let p = parse("mi klama su do prami mi");
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(
        as_bridi(&p.sentences[0]).head_terms,
        vec![Sumti::ProSumti("do".into())]
    );
}

// ─── Complex combinations ────────────────────────────────────────

#[test]
fn multi_sentence_with_descriptions() {
    let p = parse("mi prami lo gerku .i lo mlatu cu nelci mi");
    assert_eq!(p.sentences.len(), 2);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("nelci".into()));
}

#[test]
fn se_with_tanru() {
    let p = parse("do se sutra klama");
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Converted(Conversion::Se, inner) => match inner.as_ref() {
            Selbri::Tanru(_, _) => {}
            other => panic!("expected Tanru after se, got {:?}", other),
        },
        other => panic!("expected Converted, got {:?}", other),
    }
}

// ─── Sumti connectives (.e/.a/.o/.u + nai) ──────────────────────

#[test]
fn sumti_connective_e_full_pipeline() {
    // mi .e do klama — full text through lex→preprocess→parse
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
fn sumti_connective_a_full_pipeline() {
    let p = parse("mi .a do klama");
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Ja, .. } => {}
        other => panic!("expected Connected(.a), got {:?}", other),
    }
}

#[test]
fn sumti_connective_o_full_pipeline() {
    let p = parse("mi .o do klama");
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Jo, .. } => {}
        other => panic!("expected Connected(.o), got {:?}", other),
    }
}

#[test]
fn sumti_connective_u_full_pipeline() {
    let p = parse("mi .u do klama");
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Ju, .. } => {}
        other => panic!("expected Connected(.u), got {:?}", other),
    }
}

#[test]
fn sumti_connective_enai_full_pipeline() {
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
fn sumti_connective_anai_full_pipeline() {
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
fn sumti_connective_descriptions_full_pipeline() {
    // lo gerku .e lo mlatu cu barda
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
fn sumti_connective_in_tail_full_pipeline() {
    // mi nelci lo gerku .e lo mlatu
    let p = parse("mi nelci lo gerku .e lo mlatu");
    let s = as_bridi(&p.sentences[0]);
    match &s.tail_terms[0] {
        Sumti::Connected { connective: Connective::Je, .. } => {}
        other => panic!("expected Connected in tail, got {:?}", other),
    }
}

#[test]
fn sumti_connective_does_not_eat_dot_i_full_pipeline() {
    // mi klama .i do prami — .i is a sentence separator, NOT a connective
    let p = parse("mi klama .i do prami");
    assert_eq!(p.sentences.len(), 2);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("klama".into()));
    assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("prami".into()));
}

#[test]
fn sumti_connective_chained_full_pipeline() {
    // mi .e do .e di klama → right-associative
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
            // Right is nested: Connected(do, Je, di)
            match right.as_ref() {
                Sumti::Connected {
                    left: inner_left,
                    connective: Connective::Je,
                    right: inner_right,
                    ..
                } => {
                    assert_eq!(**inner_left, Sumti::ProSumti("do".into()));
                    assert_eq!(**inner_right, Sumti::ProSumti("di".into()));
                }
                other => panic!("expected inner Connected, got {:?}", other),
            }
        }
        other => panic!("expected outer Connected, got {:?}", other),
    }
}

#[test]
fn sumti_connective_with_names_full_pipeline() {
    // la .djan. .e la .meris. cu klama
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
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
}

#[test]
fn sumti_connective_with_multi_sentence() {
    // mi .e do klama .i lo gerku .a lo mlatu cu barda
    let p = parse("mi .e do klama .i lo gerku .a lo mlatu cu barda");
    assert_eq!(p.sentences.len(), 2);

    // First sentence: mi .e do klama
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Je, .. } => {}
        other => panic!("sentence 1: expected Connected(.e), got {:?}", other),
    }

    // Second sentence: lo gerku .a lo mlatu cu barda
    match &as_bridi(&p.sentences[1]).head_terms[0] {
        Sumti::Connected { connective: Connective::Ja, .. } => {}
        other => panic!("sentence 2: expected Connected(.a), got {:?}", other),
    }
}
