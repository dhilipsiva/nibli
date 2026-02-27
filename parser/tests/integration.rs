use bumpalo::Bump;
use parser_test::ast::*;
use parser_test::grammar::{parse_tokens_to_ast, ParseResult};
use parser_test::lexer::tokenize;
use parser_test::preprocessor::preprocess;

/// Parse a raw Lojban string through the full pipeline.
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

fn parse_err(input: &str) -> String {
    let arena = Bump::new();
    let raw = tokenize(input);
    let normalized = preprocess(raw.into_iter(), input);
    let result = parse_tokens_to_ast(&normalized, input, &arena);
    assert!(
        !result.errors.is_empty(),
        "expected parse error for {:?}",
        input
    );
    result.errors[0].to_string()
}

/// Parse and return the full result (for testing recovery).
fn parse_result<'a>(input: &str, arena: &'a Bump) -> ParseResult<'a> {
    let raw = tokenize(input);
    let normalized = preprocess(raw.into_iter(), input);
    parse_tokens_to_ast(&normalized, input, arena)
}

/// Helper: extract Bridi from a Sentence::Simple
fn as_bridi<'a>(sentence: &'a Sentence<'a>) -> &'a Bridi<'a> {
    match sentence {
        Sentence::Simple(b) => b,
        other => panic!("expected Sentence::Simple, got {:?}", other),
    }
}

// ─── Basic sentences ─────────────────────────────────────────────

#[test]
fn simple_assertion() {
    let arena = Bump::new();
    let p = parse("mi prami do", &arena);
    assert_eq!(p.sentences.len(), 1);
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.selbri, Selbri::Root("prami".into()));
    assert_eq!(s.head_terms, vec![Sumti::ProSumti("mi".into())]);
    assert_eq!(s.tail_terms, vec![Sumti::ProSumti("do".into())]);
    assert!(!s.negated);
}

#[test]
fn with_cu_separator() {
    let arena = Bump::new();
    let p = parse("mi cu klama", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
    assert_eq!(s.head_terms.len(), 1);
}

#[test]
fn multiple_tail_sumti() {
    // mi klama do ti ta
    let arena = Bump::new();
    let p = parse("mi klama do ti ta", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.tail_terms.len(), 3);
}

// ─── .i sentence separator ───────────────────────────────────────

#[test]
fn two_sentences() {
    let arena = Bump::new();
    let p = parse("mi prami do .i do prami mi", &arena);
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
    let arena = Bump::new();
    let p = parse("mi prami do .i do nelci mi .i mi klama", &arena);
    assert_eq!(p.sentences.len(), 3);
}

// ─── Descriptions (lo/le) ────────────────────────────────────────

#[test]
fn lo_description() {
    let arena = Bump::new();
    let p = parse("mi nelci lo gerku", &arena);
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
    let arena = Bump::new();
    let p = parse("mi nelci le mlatu", &arena);
    match &as_bridi(&p.sentences[0]).tail_terms[0] {
        Sumti::Description { gadri, .. } => assert_eq!(*gadri, Gadri::Le),
        other => panic!("expected Description with Le, got {:?}", other),
    }
}

#[test]
fn lo_with_ku() {
    let arena = Bump::new();
    let p = parse("lo gerku ku cu klama", &arena);
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
    let arena = Bump::new();
    let p = parse("la .djan. cu klama", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert_eq!(s.head_terms, vec![Sumti::Name("djan".into())]);
    assert_eq!(s.selbri, Selbri::Root("klama".into()));
}

// ─── Place tags (fa/fe/fi/fo/fu) ─────────────────────────────────

#[test]
fn explicit_place_tags() {
    let arena = Bump::new();
    let p = parse("fe do fa mi prami", &arena);
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
    let arena = Bump::new();
    let p = parse("mi na prami do", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert!(s.negated);
    assert_eq!(s.selbri, Selbri::Root("prami".into()));
}

#[test]
fn bridi_negation_with_cu() {
    let arena = Bump::new();
    let p = parse("mi cu na prami do", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert!(s.negated);
    assert_eq!(s.selbri, Selbri::Root("prami".into()));
}

#[test]
fn na_before_sumti_errors() {
    // Bare `na` before sumti is invalid — per CLL, bare `na` must
    // immediately precede the selbri. Sentence-initial negation
    // requires `na ku` (a separate grammar production).
    let e = parse_err("na mi citka lo plise");
    assert!(e.contains("na"), "error should mention 'na': {}", e);
}

#[test]
fn bridi_negation_with_tail_description() {
    // mi na citka lo plise → negated bridi with tail description
    let arena = Bump::new();
    let p = parse("mi na citka lo plise", &arena);
    let s = as_bridi(&p.sentences[0]);
    assert!(s.negated);
    assert_eq!(s.selbri, Selbri::Root("citka".into()));
    assert_eq!(s.head_terms, vec![Sumti::ProSumti("mi".into())]);
    assert_eq!(s.tail_terms.len(), 1);
    match &s.tail_terms[0] {
        Sumti::Description { gadri, inner } => {
            assert_eq!(*gadri, Gadri::Lo);
            assert_eq!(**inner, Selbri::Root("plise".into()));
        }
        other => panic!("expected Description, got {:?}", other),
    }
}

// ─── SE conversion ───────────────────────────────────────────────

#[test]
fn se_conversion() {
    let arena = Bump::new();
    let p = parse("do se prami mi", &arena);
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
    let arena = Bump::new();
    let p = parse("ti te klama do mi", &arena);
    match &as_bridi(&p.sentences[0]).selbri {
        Selbri::Converted(Conversion::Te, _) => {}
        other => panic!("expected Converted(Te), got {:?}", other),
    }
}

// ─── Tanru ───────────────────────────────────────────────────────

#[test]
fn simple_tanru() {
    // sutra gerku = fast-type-of dog
    let arena = Bump::new();
    let p = parse("mi sutra gerku", &arena);
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
    let arena = Bump::new();
    let p = parse("mi barda sutra gerku", &arena);
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
    let arena = Bump::new();
    let p = parse("mi nelci be lo gerku", &arena);
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
    let arena = Bump::new();
    let p = parse("mi klama be lo zarci bei do", &arena);
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
    let arena = Bump::new();
    let p = parse("mi ke sutra gerku ke'e", &arena);
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
    let arena = Bump::new();
    let p = parse("mi barda je xunre", &arena);
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
    let arena = Bump::new();
    let p = parse("mi barda ja cmalu", &arena);
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
    let arena = Bump::new();
    let p = parse("mi nelci lo gerku poi barda", &arena);
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
    let arena = Bump::new();
    let p = parse("mi prami zo'e", &arena);
    assert_eq!(as_bridi(&p.sentences[0]).tail_terms, vec![Sumti::Unspecified]);
}

// ─── Metalinguistic operators (via preprocessor) ─────────────────

#[test]
fn si_erasure() {
    // "mi klama si prami do" → mi prami do (klama erased by si)
    let arena = Bump::new();
    let p = parse("mi klama si prami do", &arena);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
}

#[test]
fn su_erasure() {
    // "mi klama su do prami mi" → do prami mi (everything before su erased)
    let arena = Bump::new();
    let p = parse("mi klama su do prami mi", &arena);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(
        as_bridi(&p.sentences[0]).head_terms,
        vec![Sumti::ProSumti("do".into())]
    );
}

#[test]
fn sa_erasure_gadri_class() {
    // "lo gerku cu klama sa lo mlatu cu sutra"
    // sa sees "lo" (LE class) → erases back to previous "lo" → result: "lo mlatu cu sutra"
    let arena = Bump::new();
    let p = parse("lo gerku cu klama sa lo mlatu cu sutra", &arena);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("sutra".into()));
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Description { gadri, inner } => {
            assert_eq!(*gadri, Gadri::Lo);
            assert_eq!(**inner, Selbri::Root("mlatu".into()));
        }
        other => panic!("expected Description, got {:?}", other),
    }
}

#[test]
fn sa_erasure_brivla_class() {
    // "mi klama sa prami do" → erases back to "klama" (Brivla class) → "mi prami do"
    let arena = Bump::new();
    let p = parse("mi klama sa prami do", &arena);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(
        as_bridi(&p.sentences[0]).head_terms,
        vec![Sumti::ProSumti("mi".into())]
    );
    assert_eq!(
        as_bridi(&p.sentences[0]).tail_terms,
        vec![Sumti::ProSumti("do".into())]
    );
}

#[test]
fn sa_erasure_no_match_fallback() {
    // "mi klama sa lo gerku" → no LE-class in output → falls back to single-word erase
    // Removes "klama" → "mi lo gerku" → parses as observative with head=[mi, lo gerku]
    // Actually: "mi" + "lo gerku" → mi is head, "lo gerku" is also head, implicit go'i
    // Let's use a simpler case: "klama sa lo gerku" → no LE before sa → removes "klama"
    // → "lo gerku" → description with implicit go'i
    let arena = Bump::new();
    let p = parse("klama sa lo gerku", &arena);
    // After fallback erase: "lo gerku" → observative with go'i and lo gerku as head term
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("go'i".into()));
}

// ─── Complex combinations ────────────────────────────────────────

#[test]
fn multi_sentence_with_descriptions() {
    let arena = Bump::new();
    let p = parse("mi prami lo gerku .i lo mlatu cu nelci mi", &arena);
    assert_eq!(p.sentences.len(), 2);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("prami".into()));
    assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("nelci".into()));
}

#[test]
fn se_with_tanru() {
    let arena = Bump::new();
    let p = parse("do se sutra klama", &arena);
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
fn sumti_connective_a_full_pipeline() {
    let arena = Bump::new();
    let p = parse("mi .a do klama", &arena);
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Ja, .. } => {}
        other => panic!("expected Connected(.a), got {:?}", other),
    }
}

#[test]
fn sumti_connective_o_full_pipeline() {
    let arena = Bump::new();
    let p = parse("mi .o do klama", &arena);
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Jo, .. } => {}
        other => panic!("expected Connected(.o), got {:?}", other),
    }
}

#[test]
fn sumti_connective_u_full_pipeline() {
    let arena = Bump::new();
    let p = parse("mi .u do klama", &arena);
    match &as_bridi(&p.sentences[0]).head_terms[0] {
        Sumti::Connected { connective: Connective::Ju, .. } => {}
        other => panic!("expected Connected(.u), got {:?}", other),
    }
}

#[test]
fn sumti_connective_enai_full_pipeline() {
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
fn sumti_connective_anai_full_pipeline() {
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
fn sumti_connective_descriptions_full_pipeline() {
    // lo gerku .e lo mlatu cu barda
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
    let arena = Bump::new();
    let p = parse("mi nelci lo gerku .e lo mlatu", &arena);
    let s = as_bridi(&p.sentences[0]);
    match &s.tail_terms[0] {
        Sumti::Connected { connective: Connective::Je, .. } => {}
        other => panic!("expected Connected in tail, got {:?}", other),
    }
}

#[test]
fn sumti_connective_does_not_eat_dot_i_full_pipeline() {
    // mi klama .i do prami — .i is a sentence separator, NOT a connective
    let arena = Bump::new();
    let p = parse("mi klama .i do prami", &arena);
    assert_eq!(p.sentences.len(), 2);
    assert_eq!(as_bridi(&p.sentences[0]).selbri, Selbri::Root("klama".into()));
    assert_eq!(as_bridi(&p.sentences[1]).selbri, Selbri::Root("prami".into()));
}

#[test]
fn sumti_connective_chained_full_pipeline() {
    // mi .e do .e di klama → right-associative
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
    let arena = Bump::new();
    let p = parse("mi .e do klama .i lo gerku .a lo mlatu cu barda", &arena);
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

// ─── Error recovery tests ──────────────────────────────────────

#[test]
fn error_recovery_skips_bad_sentence() {
    // Middle sentence "ke ke ke" is malformed; first and third are fine
    let arena = Bump::new();
    let r = parse_result("mi klama .i ke ke ke .i do prami mi", &arena);
    assert_eq!(r.parsed.sentences.len(), 2);
    assert_eq!(r.errors.len(), 1);
    // First sentence: mi klama
    let s1 = as_bridi(&r.parsed.sentences[0]);
    assert_eq!(s1.selbri, Selbri::Root("klama".into()));
    // Third sentence: do prami mi
    let s2 = as_bridi(&r.parsed.sentences[1]);
    assert_eq!(s2.selbri, Selbri::Root("prami".into()));
}

#[test]
fn error_recovery_all_sentences_fail() {
    // Both sentences are malformed
    let arena = Bump::new();
    let r = parse_result("ke ke .i ke ke", &arena);
    assert_eq!(r.parsed.sentences.len(), 0);
    assert_eq!(r.errors.len(), 2);
}

#[test]
fn error_recovery_empty_input() {
    let arena = Bump::new();
    let r = parse_result("", &arena);
    assert_eq!(r.parsed.sentences.len(), 0);
    assert_eq!(r.errors.len(), 1);
    assert!(r.errors[0].message.contains("empty input"));
}

#[test]
fn error_reports_line_column() {
    // Error on line 2 ("ke ke ke" is malformed)
    let arena = Bump::new();
    let r = parse_result("mi klama\n.i ke ke ke\n.i do prami mi", &arena);
    assert_eq!(r.parsed.sentences.len(), 2);
    assert_eq!(r.errors.len(), 1);
    assert_eq!(r.errors[0].line, 2, "error should be on line 2");
    assert!(r.errors[0].column > 0, "column should be positive");
}

#[test]
fn error_reports_first_line() {
    // Error on line 1
    let arena = Bump::new();
    let r = parse_result("ke ke ke", &arena);
    assert_eq!(r.errors.len(), 1);
    assert_eq!(r.errors[0].line, 1);
}

#[test]
fn error_display_includes_line_column() {
    let arena = Bump::new();
    let r = parse_result("ke ke ke", &arena);
    let msg = r.errors[0].to_string();
    // Format should be "line:col: message"
    assert!(msg.contains(':'), "error display should contain line:col separator");
}
