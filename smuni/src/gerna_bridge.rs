//! Bridge conversions: gerna WIT AST types → smuni WIT AST types.
//!
//! These types are structurally identical (generated from the same WIT `ast-types`
//! interface) but are different Rust types because each crate generates its own bindings.

use crate::bindings::lojban::nibli::ast_types as smuni_ast;
use gerna::bindings::lojban::nibli::ast_types as gerna_ast;

fn convert_place_tag(t: &gerna_ast::PlaceTag) -> smuni_ast::PlaceTag {
    match t {
        gerna_ast::PlaceTag::Fa => smuni_ast::PlaceTag::Fa,
        gerna_ast::PlaceTag::Fe => smuni_ast::PlaceTag::Fe,
        gerna_ast::PlaceTag::Fi => smuni_ast::PlaceTag::Fi,
        gerna_ast::PlaceTag::Fo => smuni_ast::PlaceTag::Fo,
        gerna_ast::PlaceTag::Fu => smuni_ast::PlaceTag::Fu,
    }
}

fn convert_bai_tag(t: &gerna_ast::BaiTag) -> smuni_ast::BaiTag {
    match t {
        gerna_ast::BaiTag::Ria => smuni_ast::BaiTag::Ria,
        gerna_ast::BaiTag::Nii => smuni_ast::BaiTag::Nii,
        gerna_ast::BaiTag::Mui => smuni_ast::BaiTag::Mui,
        gerna_ast::BaiTag::Kiu => smuni_ast::BaiTag::Kiu,
        gerna_ast::BaiTag::Pio => smuni_ast::BaiTag::Pio,
        gerna_ast::BaiTag::Bai => smuni_ast::BaiTag::Bai,
    }
}

fn convert_modal_tag(t: &gerna_ast::ModalTag) -> smuni_ast::ModalTag {
    match t {
        gerna_ast::ModalTag::Fixed(b) => smuni_ast::ModalTag::Fixed(convert_bai_tag(b)),
        gerna_ast::ModalTag::Fio(id) => smuni_ast::ModalTag::Fio(*id),
    }
}

fn convert_conversion(c: &gerna_ast::Conversion) -> smuni_ast::Conversion {
    match c {
        gerna_ast::Conversion::Se => smuni_ast::Conversion::Se,
        gerna_ast::Conversion::Te => smuni_ast::Conversion::Te,
        gerna_ast::Conversion::Ve => smuni_ast::Conversion::Ve,
        gerna_ast::Conversion::Xe => smuni_ast::Conversion::Xe,
    }
}

fn convert_connective(c: &gerna_ast::Connective) -> smuni_ast::Connective {
    match c {
        gerna_ast::Connective::Je => smuni_ast::Connective::Je,
        gerna_ast::Connective::Ja => smuni_ast::Connective::Ja,
        gerna_ast::Connective::Jo => smuni_ast::Connective::Jo,
        gerna_ast::Connective::Ju => smuni_ast::Connective::Ju,
    }
}

fn convert_gadri(g: &gerna_ast::Gadri) -> smuni_ast::Gadri {
    match g {
        gerna_ast::Gadri::Lo => smuni_ast::Gadri::Lo,
        gerna_ast::Gadri::Le => smuni_ast::Gadri::Le,
        gerna_ast::Gadri::La => smuni_ast::Gadri::La,
        gerna_ast::Gadri::RoLo => smuni_ast::Gadri::RoLo,
        gerna_ast::Gadri::RoLe => smuni_ast::Gadri::RoLe,
    }
}

fn convert_abstraction_kind(k: &gerna_ast::AbstractionKind) -> smuni_ast::AbstractionKind {
    match k {
        gerna_ast::AbstractionKind::Nu => smuni_ast::AbstractionKind::Nu,
        gerna_ast::AbstractionKind::Duhu => smuni_ast::AbstractionKind::Duhu,
        gerna_ast::AbstractionKind::Ka => smuni_ast::AbstractionKind::Ka,
        gerna_ast::AbstractionKind::Ni => smuni_ast::AbstractionKind::Ni,
        gerna_ast::AbstractionKind::Siho => smuni_ast::AbstractionKind::Siho,
    }
}

fn convert_rel_clause_kind(k: &gerna_ast::RelClauseKind) -> smuni_ast::RelClauseKind {
    match k {
        gerna_ast::RelClauseKind::Poi => smuni_ast::RelClauseKind::Poi,
        gerna_ast::RelClauseKind::Noi => smuni_ast::RelClauseKind::Noi,
        gerna_ast::RelClauseKind::Voi => smuni_ast::RelClauseKind::Voi,
    }
}

fn convert_tense(t: &gerna_ast::Tense) -> smuni_ast::Tense {
    match t {
        gerna_ast::Tense::Pu => smuni_ast::Tense::Pu,
        gerna_ast::Tense::Ca => smuni_ast::Tense::Ca,
        gerna_ast::Tense::Ba => smuni_ast::Tense::Ba,
    }
}

fn convert_attitudinal(a: &gerna_ast::Attitudinal) -> smuni_ast::Attitudinal {
    match a {
        gerna_ast::Attitudinal::Ei => smuni_ast::Attitudinal::Ei,
        gerna_ast::Attitudinal::Ehe => smuni_ast::Attitudinal::Ehe,
    }
}

fn convert_sentence_connective(
    c: &gerna_ast::SentenceConnective,
) -> smuni_ast::SentenceConnective {
    match c {
        gerna_ast::SentenceConnective::GanaiGi => smuni_ast::SentenceConnective::GanaiGi,
        gerna_ast::SentenceConnective::GeGi => smuni_ast::SentenceConnective::GeGi,
        gerna_ast::SentenceConnective::GaGi => smuni_ast::SentenceConnective::GaGi,
        gerna_ast::SentenceConnective::Afterthought((ln, c, rn)) => {
            smuni_ast::SentenceConnective::Afterthought((*ln, convert_connective(c), *rn))
        }
    }
}

fn convert_selbri(s: &gerna_ast::Selbri) -> smuni_ast::Selbri {
    match s {
        gerna_ast::Selbri::Root(name) => smuni_ast::Selbri::Root(name.clone()),
        gerna_ast::Selbri::Compound(parts) => smuni_ast::Selbri::Compound(parts.clone()),
        gerna_ast::Selbri::Tanru((m, h)) => smuni_ast::Selbri::Tanru((*m, *h)),
        gerna_ast::Selbri::Converted((c, id)) => {
            smuni_ast::Selbri::Converted((convert_conversion(c), *id))
        }
        gerna_ast::Selbri::Negated(id) => smuni_ast::Selbri::Negated(*id),
        gerna_ast::Selbri::Grouped(id) => smuni_ast::Selbri::Grouped(*id),
        gerna_ast::Selbri::WithArgs((core, args)) => {
            smuni_ast::Selbri::WithArgs((*core, args.clone()))
        }
        gerna_ast::Selbri::Connected((l, c, r)) => {
            smuni_ast::Selbri::Connected((*l, convert_connective(c), *r))
        }
        gerna_ast::Selbri::Abstraction((k, sent)) => {
            smuni_ast::Selbri::Abstraction((convert_abstraction_kind(k), *sent))
        }
    }
}

fn convert_rel_clause(rc: &gerna_ast::RelClause) -> smuni_ast::RelClause {
    smuni_ast::RelClause {
        kind: convert_rel_clause_kind(&rc.kind),
        body_sentence: rc.body_sentence,
    }
}

fn convert_sumti(s: &gerna_ast::Sumti) -> smuni_ast::Sumti {
    match s {
        gerna_ast::Sumti::ProSumti(v) => smuni_ast::Sumti::ProSumti(v.clone()),
        gerna_ast::Sumti::Description((g, sid)) => {
            smuni_ast::Sumti::Description((convert_gadri(g), *sid))
        }
        gerna_ast::Sumti::Name(v) => smuni_ast::Sumti::Name(v.clone()),
        gerna_ast::Sumti::QuotedLiteral(v) => smuni_ast::Sumti::QuotedLiteral(v.clone()),
        gerna_ast::Sumti::Unspecified => smuni_ast::Sumti::Unspecified,
        gerna_ast::Sumti::Tagged((t, id)) => {
            smuni_ast::Sumti::Tagged((convert_place_tag(t), *id))
        }
        gerna_ast::Sumti::ModalTagged((mt, id)) => {
            smuni_ast::Sumti::ModalTagged((convert_modal_tag(mt), *id))
        }
        gerna_ast::Sumti::Restricted((id, rc)) => {
            smuni_ast::Sumti::Restricted((*id, convert_rel_clause(rc)))
        }
        gerna_ast::Sumti::Number(n) => smuni_ast::Sumti::Number(*n),
        gerna_ast::Sumti::Connected((l, c, neg, r)) => {
            smuni_ast::Sumti::Connected((*l, convert_connective(c), *neg, *r))
        }
        gerna_ast::Sumti::QuantifiedDescription((count, g, sid)) => {
            smuni_ast::Sumti::QuantifiedDescription((*count, convert_gadri(g), *sid))
        }
    }
}

fn convert_bridi(b: &gerna_ast::Bridi) -> smuni_ast::Bridi {
    smuni_ast::Bridi {
        relation: b.relation,
        head_terms: b.head_terms.clone(),
        tail_terms: b.tail_terms.clone(),
        negated: b.negated,
        tense: b.tense.as_ref().map(convert_tense),
        attitudinal: b.attitudinal.as_ref().map(convert_attitudinal),
    }
}

fn convert_sentence(s: &gerna_ast::Sentence) -> smuni_ast::Sentence {
    match s {
        gerna_ast::Sentence::Simple(b) => smuni_ast::Sentence::Simple(convert_bridi(b)),
        gerna_ast::Sentence::Connected((c, l, r)) => {
            smuni_ast::Sentence::Connected((convert_sentence_connective(c), *l, *r))
        }
    }
}

pub(crate) fn convert_ast_buffer(buf: &gerna_ast::AstBuffer) -> smuni_ast::AstBuffer {
    smuni_ast::AstBuffer {
        selbris: buf.selbris.iter().map(convert_selbri).collect(),
        sumtis: buf.sumtis.iter().map(convert_sumti).collect(),
        sentences: buf.sentences.iter().map(convert_sentence).collect(),
        roots: buf.roots.clone(),
    }
}
