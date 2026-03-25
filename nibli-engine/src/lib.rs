//! Native nibli engine library: calls gerna/smuni/logji directly as Rust crates.
//! No WASM, no Wasmtime — full stack traces for debugging.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashSet;
use std::path::Path;

use nibli_protocol::{
    LogicalTerm as LogicalTermJson, ProofRule as ProofRuleJson, ProofStep as ProofStepJson,
    ProofTrace as ProofTraceJson, humanize_sexp,
};
use nibli_store::{NibliStore, StoredLogicBuffer, StoredLogicNode, StoredLogicalTerm};

// ─── Type aliases for each crate's WIT-generated types ──────────────

mod gerna_ast {
    pub use gerna::bindings::lojban::nibli::ast_types::*;
}
mod gerna_err {
    pub use gerna::bindings::lojban::nibli::error_types::*;
}

mod smuni_ast {
    pub use smuni::bindings::lojban::nibli::ast_types::*;
}
mod smuni_logic {
    pub use smuni::bindings::lojban::nibli::logic_types::*;
}
mod smuni_err {
    pub use smuni::bindings::lojban::nibli::error_types::*;
}

mod logji_logic {
    pub use logji::bindings::lojban::nibli::logic_types::*;
}
mod logji_err {
    pub use logji::bindings::lojban::nibli::error_types::*;
}

use logji::bindings::exports::lojban::nibli::logji::GuestKnowledgeBase;

// ═══════════════════════════════════════════════════════════════════════
// TYPE CONVERSIONS: gerna -> smuni (AstBuffer)
// ═══════════════════════════════════════════════════════════════════════

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

fn convert_sentence_connective(c: &gerna_ast::SentenceConnective) -> smuni_ast::SentenceConnective {
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
        gerna_ast::Sumti::Tagged((t, id)) => smuni_ast::Sumti::Tagged((convert_place_tag(t), *id)),
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

fn convert_ast_buffer(buf: &gerna_ast::AstBuffer) -> smuni_ast::AstBuffer {
    smuni_ast::AstBuffer {
        selbris: buf.selbris.iter().map(convert_selbri).collect(),
        sumtis: buf.sumtis.iter().map(convert_sumti).collect(),
        sentences: buf.sentences.iter().map(convert_sentence).collect(),
        roots: buf.roots.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// TYPE CONVERSIONS: smuni -> logji (LogicBuffer)
// ═══════════════════════════════════════════════════════════════════════

fn convert_logical_term_s2l(t: &smuni_logic::LogicalTerm) -> logji_logic::LogicalTerm {
    match t {
        smuni_logic::LogicalTerm::Variable(v) => logji_logic::LogicalTerm::Variable(v.clone()),
        smuni_logic::LogicalTerm::Constant(c) => logji_logic::LogicalTerm::Constant(c.clone()),
        smuni_logic::LogicalTerm::Description(d) => {
            logji_logic::LogicalTerm::Description(d.clone())
        }
        smuni_logic::LogicalTerm::Unspecified => logji_logic::LogicalTerm::Unspecified,
        smuni_logic::LogicalTerm::Number(n) => logji_logic::LogicalTerm::Number(*n),
    }
}

fn convert_logic_node_s2l(n: &smuni_logic::LogicNode) -> logji_logic::LogicNode {
    match n {
        smuni_logic::LogicNode::Predicate((rel, args)) => logji_logic::LogicNode::Predicate((
            rel.clone(),
            args.iter().map(convert_logical_term_s2l).collect(),
        )),
        smuni_logic::LogicNode::ComputeNode((rel, args)) => logji_logic::LogicNode::ComputeNode((
            rel.clone(),
            args.iter().map(convert_logical_term_s2l).collect(),
        )),
        smuni_logic::LogicNode::AndNode((l, r)) => logji_logic::LogicNode::AndNode((*l, *r)),
        smuni_logic::LogicNode::OrNode((l, r)) => logji_logic::LogicNode::OrNode((*l, *r)),
        smuni_logic::LogicNode::NotNode(id) => logji_logic::LogicNode::NotNode(*id),
        smuni_logic::LogicNode::ExistsNode((v, b)) => {
            logji_logic::LogicNode::ExistsNode((v.clone(), *b))
        }
        smuni_logic::LogicNode::ForAllNode((v, b)) => {
            logji_logic::LogicNode::ForAllNode((v.clone(), *b))
        }
        smuni_logic::LogicNode::PastNode(id) => logji_logic::LogicNode::PastNode(*id),
        smuni_logic::LogicNode::PresentNode(id) => logji_logic::LogicNode::PresentNode(*id),
        smuni_logic::LogicNode::FutureNode(id) => logji_logic::LogicNode::FutureNode(*id),
        smuni_logic::LogicNode::ObligatoryNode(id) => logji_logic::LogicNode::ObligatoryNode(*id),
        smuni_logic::LogicNode::PermittedNode(id) => logji_logic::LogicNode::PermittedNode(*id),
        smuni_logic::LogicNode::CountNode((v, c, b)) => {
            logji_logic::LogicNode::CountNode((v.clone(), *c, *b))
        }
    }
}

fn convert_logic_buffer_s2l(buf: &smuni_logic::LogicBuffer) -> logji_logic::LogicBuffer {
    logji_logic::LogicBuffer {
        nodes: buf.nodes.iter().map(convert_logic_node_s2l).collect(),
        roots: buf.roots.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// COMPUTE NODE TRANSFORM
// ═══════════════════════════════════════════════════════════════════════

fn transform_compute_nodes(buf: &mut smuni_logic::LogicBuffer, compute_preds: &HashSet<String>) {
    let nodes = std::mem::take(&mut buf.nodes);
    buf.nodes = nodes
        .into_iter()
        .map(|node| match &node {
            smuni_logic::LogicNode::Predicate((rel, _)) if compute_preds.contains(rel.as_str()) => {
                let smuni_logic::LogicNode::Predicate(inner) = node else {
                    unreachable!()
                };
                smuni_logic::LogicNode::ComputeNode(inner)
            }
            _ => node,
        })
        .collect();
}

// ═══════════════════════════════════════════════════════════════════════
// ERROR FORMATTING
// ═══════════════════════════════════════════════════════════════════════

enum NibliError {
    Gerna(gerna_err::NibliError),
    Smuni(smuni_err::NibliError),
    Logji(logji_err::NibliError),
}

fn format_gerna_error(e: &gerna_err::NibliError) -> String {
    match e {
        gerna_err::NibliError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        gerna_err::NibliError::Semantic(msg) => format!("[Semantic Error] {}", msg),
        gerna_err::NibliError::Reasoning(msg) => format!("[Reasoning Error] {}", msg),
        gerna_err::NibliError::Backend((kind, msg)) => {
            format!("[Backend Error] {} — {}", kind, msg)
        }
    }
}

fn format_smuni_error(e: &smuni_err::NibliError) -> String {
    match e {
        smuni_err::NibliError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        smuni_err::NibliError::Semantic(msg) => format!("[Semantic Error] {}", msg),
        smuni_err::NibliError::Reasoning(msg) => format!("[Reasoning Error] {}", msg),
        smuni_err::NibliError::Backend((kind, msg)) => {
            format!("[Backend Error] {} — {}", kind, msg)
        }
    }
}

fn format_logji_error(e: &logji_err::NibliError) -> String {
    match e {
        logji_err::NibliError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        logji_err::NibliError::Semantic(msg) => format!("[Semantic Error] {}", msg),
        logji_err::NibliError::Reasoning(msg) => format!("[Reasoning Error] {}", msg),
        logji_err::NibliError::Backend((kind, msg)) => {
            format!("[Backend Error] {} — {}", kind, msg)
        }
    }
}

fn format_error(e: &NibliError) -> String {
    match e {
        NibliError::Gerna(e) => format_gerna_error(e),
        NibliError::Smuni(e) => format_smuni_error(e),
        NibliError::Logji(e) => format_logji_error(e),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE FORMATTING
// ═══════════════════════════════════════════════════════════════════════

fn format_term_display(term: &logji_logic::LogicalTerm) -> String {
    match term {
        logji_logic::LogicalTerm::Constant(s) => s.clone(),
        logji_logic::LogicalTerm::Variable(s) => format!("?{}", s),
        logji_logic::LogicalTerm::Description(s) => format!("lo {}", s),
        logji_logic::LogicalTerm::Number(n) => {
            if *n == (*n as i64) as f64 {
                format!("{}", *n as i64)
            } else {
                format!("{}", n)
            }
        }
        logji_logic::LogicalTerm::Unspecified => "zo'e".to_string(),
    }
}

fn format_rule(rule: &logji_logic::ProofRule, result: bool) -> String {
    let tag = if result { "TRUE" } else { "FALSE" };
    match rule {
        logji_logic::ProofRule::Conjunction => format!("Conjunction -> {}", tag),
        logji_logic::ProofRule::DisjunctionCheck(s) => {
            format!("Disjunction (check: {}) -> {}", s, tag)
        }
        logji_logic::ProofRule::DisjunctionIntro(side) => {
            format!("Disjunction ({}) -> {}", side, tag)
        }
        logji_logic::ProofRule::Negation => format!("Negation -> {}", tag),
        logji_logic::ProofRule::ModalPassthrough(kind) => {
            format!("Modal ({}) -> {}", kind, tag)
        }
        logji_logic::ProofRule::ExistsWitness((var, term)) => {
            format!("Exists: {} = {} -> {}", var, format_term_display(term), tag)
        }
        logji_logic::ProofRule::ExistsFailed => format!("Exists: no witness -> {}", tag),
        logji_logic::ProofRule::ForallVacuous => {
            format!("ForAll: vacuous (empty domain) -> {}", tag)
        }
        logji_logic::ProofRule::ForallVerified(entities) => {
            let names: Vec<String> = entities.iter().map(format_term_display).collect();
            format!("ForAll: verified [{}] -> {}", names.join(", "), tag)
        }
        logji_logic::ProofRule::ForallCounterexample(term) => {
            format!(
                "ForAll: counterexample {} -> {}",
                format_term_display(term),
                tag
            )
        }
        logji_logic::ProofRule::CountResult((expected, actual)) => {
            format!("Count: expected={}, actual={} -> {}", expected, actual, tag)
        }
        logji_logic::ProofRule::PredicateCheck((method, detail)) => {
            format!("{}: {} -> {}", method, humanize_sexp(detail), tag)
        }
        logji_logic::ProofRule::ComputeCheck((method, detail)) => {
            format!("Compute ({}): {} -> {}", method, humanize_sexp(detail), tag)
        }
        logji_logic::ProofRule::Asserted(sexp) => {
            format!("Asserted: {} -> {}", humanize_sexp(sexp), tag)
        }
        logji_logic::ProofRule::Derived((label, sexp)) => {
            format!("Derived ({}): {} -> {}", label, humanize_sexp(sexp), tag)
        }
        logji_logic::ProofRule::ProofRef(sexp) => {
            format!("(proved above): {} -> {}", humanize_sexp(sexp), tag)
        }
    }
}

fn format_proof_node(steps: &[logji_logic::ProofStep], idx: u32, indent: usize, out: &mut String) {
    let step = &steps[idx as usize];
    for _ in 0..indent {
        out.push_str("  ");
    }
    out.push_str(&format_rule(&step.rule, step.holds));
    out.push('\n');
    for &child in &step.children {
        format_proof_node(steps, child, indent + 1, out);
    }
}

fn format_proof_trace(trace: &logji_logic::ProofTrace) -> String {
    let mut out = String::new();
    format_proof_node(&trace.steps, trace.root, 0, &mut out);
    out
}

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE CONVERSION (WIT types → nibli-protocol wire types)
// ═══════════════════════════════════════════════════════════════════════

fn term_to_json(term: &logji_logic::LogicalTerm) -> LogicalTermJson {
    match term {
        logji_logic::LogicalTerm::Constant(s) => LogicalTermJson {
            kind: "constant".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Variable(s) => LogicalTermJson {
            kind: "variable".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Description(s) => LogicalTermJson {
            kind: "description".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Number(n) => LogicalTermJson {
            kind: "number".to_string(),
            value: None,
            number: Some(*n),
        },
        logji_logic::LogicalTerm::Unspecified => LogicalTermJson {
            kind: "unspecified".to_string(),
            value: None,
            number: None,
        },
    }
}

fn rule_to_json(rule: &logji_logic::ProofRule) -> ProofRuleJson {
    match rule {
        logji_logic::ProofRule::Conjunction => ProofRuleJson::Conjunction,
        logji_logic::ProofRule::DisjunctionCheck(s) => {
            ProofRuleJson::DisjunctionCheck { detail: s.clone() }
        }
        logji_logic::ProofRule::DisjunctionIntro(s) => {
            ProofRuleJson::DisjunctionIntro { side: s.clone() }
        }
        logji_logic::ProofRule::Negation => ProofRuleJson::Negation,
        logji_logic::ProofRule::ModalPassthrough(s) => {
            ProofRuleJson::ModalPassthrough { kind: s.clone() }
        }
        logji_logic::ProofRule::ExistsWitness((var, term)) => ProofRuleJson::ExistsWitness {
            var: var.clone(),
            term: term_to_json(term),
        },
        logji_logic::ProofRule::ExistsFailed => ProofRuleJson::ExistsFailed,
        logji_logic::ProofRule::ForallVacuous => ProofRuleJson::ForallVacuous,
        logji_logic::ProofRule::ForallVerified(entities) => ProofRuleJson::ForallVerified {
            entities: entities.iter().map(term_to_json).collect(),
        },
        logji_logic::ProofRule::ForallCounterexample(term) => ProofRuleJson::ForallCounterexample {
            entity: term_to_json(term),
        },
        logji_logic::ProofRule::CountResult((expected, actual)) => ProofRuleJson::CountResult {
            expected: *expected,
            actual: *actual,
        },
        logji_logic::ProofRule::PredicateCheck((method, detail)) => ProofRuleJson::PredicateCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::ComputeCheck((method, detail)) => ProofRuleJson::ComputeCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::Asserted(sexp) => ProofRuleJson::Asserted { sexp: sexp.clone() },
        logji_logic::ProofRule::Derived((label, sexp)) => ProofRuleJson::Derived {
            label: label.clone(),
            sexp: sexp.clone(),
        },
        logji_logic::ProofRule::ProofRef(sexp) => ProofRuleJson::ProofRef { sexp: sexp.clone() },
    }
}

fn proof_trace_to_json(trace: &logji_logic::ProofTrace) -> String {
    let json_trace = ProofTraceJson {
        steps: trace
            .steps
            .iter()
            .map(|step| ProofStepJson {
                rule: rule_to_json(&step.rule),
                holds: step.holds,
                children: step.children.clone(),
            })
            .collect(),
        root: trace.root,
    };
    json_trace.to_json()
}

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════
// STORE CONVERSIONS: logji <-> nibli-store mirror types
// ═══════════════════════════════════════════════════════════════════════

fn term_to_stored(t: &logji_logic::LogicalTerm) -> StoredLogicalTerm {
    match t {
        logji_logic::LogicalTerm::Variable(v) => StoredLogicalTerm::Variable(v.clone()),
        logji_logic::LogicalTerm::Constant(c) => StoredLogicalTerm::Constant(c.clone()),
        logji_logic::LogicalTerm::Description(d) => StoredLogicalTerm::Description(d.clone()),
        logji_logic::LogicalTerm::Unspecified => StoredLogicalTerm::Unspecified,
        logji_logic::LogicalTerm::Number(n) => StoredLogicalTerm::Number(*n),
    }
}

fn term_from_stored(t: &StoredLogicalTerm) -> logji_logic::LogicalTerm {
    match t {
        StoredLogicalTerm::Variable(v) => logji_logic::LogicalTerm::Variable(v.clone()),
        StoredLogicalTerm::Constant(c) => logji_logic::LogicalTerm::Constant(c.clone()),
        StoredLogicalTerm::Description(d) => logji_logic::LogicalTerm::Description(d.clone()),
        StoredLogicalTerm::Unspecified => logji_logic::LogicalTerm::Unspecified,
        StoredLogicalTerm::Number(n) => logji_logic::LogicalTerm::Number(*n),
    }
}

fn node_to_stored(n: &logji_logic::LogicNode) -> StoredLogicNode {
    match n {
        logji_logic::LogicNode::Predicate((rel, args)) => {
            StoredLogicNode::Predicate(rel.clone(), args.iter().map(term_to_stored).collect())
        }
        logji_logic::LogicNode::ComputeNode((rel, args)) => {
            StoredLogicNode::ComputeNode(rel.clone(), args.iter().map(term_to_stored).collect())
        }
        logji_logic::LogicNode::AndNode((l, r)) => StoredLogicNode::And(*l, *r),
        logji_logic::LogicNode::OrNode((l, r)) => StoredLogicNode::Or(*l, *r),
        logji_logic::LogicNode::NotNode(id) => StoredLogicNode::Not(*id),
        logji_logic::LogicNode::ExistsNode((v, b)) => StoredLogicNode::Exists(v.clone(), *b),
        logji_logic::LogicNode::ForAllNode((v, b)) => StoredLogicNode::ForAll(v.clone(), *b),
        logji_logic::LogicNode::PastNode(id) => StoredLogicNode::Past(*id),
        logji_logic::LogicNode::PresentNode(id) => StoredLogicNode::Present(*id),
        logji_logic::LogicNode::FutureNode(id) => StoredLogicNode::Future(*id),
        logji_logic::LogicNode::ObligatoryNode(id) => StoredLogicNode::Obligatory(*id),
        logji_logic::LogicNode::PermittedNode(id) => StoredLogicNode::Permitted(*id),
        logji_logic::LogicNode::CountNode((v, c, b)) => StoredLogicNode::Count(v.clone(), *c, *b),
    }
}

fn node_from_stored(n: &StoredLogicNode) -> logji_logic::LogicNode {
    match n {
        StoredLogicNode::Predicate(rel, args) => logji_logic::LogicNode::Predicate((
            rel.clone(),
            args.iter().map(term_from_stored).collect(),
        )),
        StoredLogicNode::ComputeNode(rel, args) => logji_logic::LogicNode::ComputeNode((
            rel.clone(),
            args.iter().map(term_from_stored).collect(),
        )),
        StoredLogicNode::And(l, r) => logji_logic::LogicNode::AndNode((*l, *r)),
        StoredLogicNode::Or(l, r) => logji_logic::LogicNode::OrNode((*l, *r)),
        StoredLogicNode::Not(id) => logji_logic::LogicNode::NotNode(*id),
        StoredLogicNode::Exists(v, b) => logji_logic::LogicNode::ExistsNode((v.clone(), *b)),
        StoredLogicNode::ForAll(v, b) => logji_logic::LogicNode::ForAllNode((v.clone(), *b)),
        StoredLogicNode::Past(id) => logji_logic::LogicNode::PastNode(*id),
        StoredLogicNode::Present(id) => logji_logic::LogicNode::PresentNode(*id),
        StoredLogicNode::Future(id) => logji_logic::LogicNode::FutureNode(*id),
        StoredLogicNode::Obligatory(id) => logji_logic::LogicNode::ObligatoryNode(*id),
        StoredLogicNode::Permitted(id) => logji_logic::LogicNode::PermittedNode(*id),
        StoredLogicNode::Count(v, c, b) => logji_logic::LogicNode::CountNode((v.clone(), *c, *b)),
    }
}

fn buf_to_stored(buf: &logji_logic::LogicBuffer) -> StoredLogicBuffer {
    StoredLogicBuffer {
        nodes: buf.nodes.iter().map(node_to_stored).collect(),
        roots: buf.roots.clone(),
    }
}

fn buf_from_stored(stored: &StoredLogicBuffer) -> logji_logic::LogicBuffer {
    logji_logic::LogicBuffer {
        nodes: stored.nodes.iter().map(node_from_stored).collect(),
        roots: stored.roots.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

pub struct NibliEngine {
    kb: logji::KnowledgeBase,
    compute_predicates: HashSet<String>,
    store: RefCell<Option<NibliStore>>,
}

impl NibliEngine {
    fn default_compute_predicates() -> HashSet<String> {
        let mut preds = HashSet::new();
        preds.insert("pilji".to_string());
        preds.insert("sumji".to_string());
        preds.insert("dilcu".to_string());
        preds
    }

    /// Create an engine without persistence (existing behavior).
    pub fn new() -> Self {
        println!("Native engine ready");
        NibliEngine {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(None),
        }
    }

    /// Create an engine with disk persistence at the given path.
    /// Replays all persisted facts into the in-memory KB on open.
    pub fn open(db_path: &Path) -> Result<Self, String> {
        let store = NibliStore::open(db_path, "local".to_string())
            .map_err(|e| format!("Store error: {e}"))?;
        let engine = NibliEngine {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(Some(store)),
        };
        engine.replay_from_store()?;
        println!("Native engine ready (persistent: {})", db_path.display());
        Ok(engine)
    }

    /// Replay all persisted facts into the in-memory KB.
    fn replay_from_store(&self) -> Result<(), String> {
        let store = self.store.borrow();
        let store = store.as_ref().unwrap();
        let facts = store
            .all_active_facts()
            .map_err(|e| format!("Store error: {e}"))?;
        for fact in &facts {
            let stored_buf: StoredLogicBuffer = postcard::from_bytes(&fact.payload)
                .map_err(|e| format!("Deserialize error: {e}"))?;
            let buf = buf_from_stored(&stored_buf);
            self.kb
                .assert_fact_with_id(buf, fact.label.clone(), fact.id)
                .map_err(|e| format!("Replay error: {e}"))?;
        }
        if !facts.is_empty() {
            println!("[Store] Replayed {} persisted facts", facts.len());
        }
        Ok(())
    }

    /// Validate Lojban text without asserting — returns Ok if it parses and compiles.
    pub fn validate(&self, text: &str) -> Result<(), String> {
        self.compile_text(text)
            .map(|_| ())
            .map_err(|e| format_error(&e))
    }

    fn compile_text(&self, input: &str) -> Result<logji_logic::LogicBuffer, NibliError> {
        let parse_result =
            gerna::parse_text_native(input.to_string()).map_err(NibliError::Gerna)?;

        if parse_result.buffer.roots.is_empty() && !parse_result.errors.is_empty() {
            let first = &parse_result.errors[0];
            return Err(NibliError::Gerna(gerna_err::NibliError::Syntax(
                gerna_err::SyntaxDetail {
                    message: parse_result
                        .errors
                        .iter()
                        .map(|e| e.message.clone())
                        .collect::<Vec<_>>()
                        .join("; "),
                    line: first.line,
                    column: first.column,
                },
            )));
        }

        if !parse_result.errors.is_empty() {
            let warnings: Vec<String> = parse_result
                .errors
                .iter()
                .map(|e| e.message.clone())
                .collect();
            return Err(NibliError::Gerna(gerna_err::NibliError::Syntax(
                gerna_err::SyntaxDetail {
                    message: format!(
                        "Assertion aborted: {} sentence(s) failed to parse: {}",
                        warnings.len(),
                        warnings.join("; ")
                    ),
                    line: 0,
                    column: 0,
                },
            )));
        }

        let smuni_ast = convert_ast_buffer(&parse_result.buffer);
        let mut smuni_buf = smuni::compile_buffer_native(smuni_ast).map_err(NibliError::Smuni)?;
        transform_compute_nodes(&mut smuni_buf, &self.compute_predicates);
        let logji_buf = convert_logic_buffer_s2l(&smuni_buf);
        Ok(logji_buf)
    }

    /// Reset the knowledge base, clearing all facts and rules.
    pub fn reset(&self) {
        self.kb.reset().ok();
        if let Ok(mut store) = self.store.try_borrow_mut() {
            if let Some(s) = store.as_mut() {
                let _ = s.clear();
            }
        }
    }

    pub fn assert_text(&self, text: &str) -> Result<u64, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let label = text.to_string();
        let mut store = self
            .store
            .try_borrow_mut()
            .map_err(|_| "Store error: persistence state is already borrowed".to_string())?;

        if let Some(s) = store.as_mut() {
            let payload = postcard::to_allocvec(&buf_to_stored(&buf))
                .map_err(|e| format!("Serialize error: {e}"))?;
            let fact_id = s.next_fact_id().map_err(|e| format!("Store error: {e}"))?;
            s.insert_fact(fact_id, label.clone(), payload)
                .map_err(|e| format!("Store error: {e}"))?;
            if let Err(err) = self.kb.assert_fact_with_id(buf, label, fact_id) {
                return match s.delete_fact(fact_id) {
                    Ok(()) => Err(err),
                    Err(rollback_err) => Err(format!("{err}; rollback failed: {rollback_err}")),
                };
            }
            Ok(fact_id)
        } else {
            self.kb
                .assert_fact(buf, label)
                .map_err(|e| format_logji_error(&e))
        }
    }

    pub fn query_text_with_proof(&self, text: &str) -> Result<(bool, String, String), String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let (holds, trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| format_logji_error(&e))?;
        let formatted = format_proof_trace(&trace);
        let json = proof_trace_to_json(&trace);
        Ok((holds, formatted, json))
    }

    /// Check if a Lojban query holds in the KB (simple boolean check).
    pub fn query_holds(&self, text: &str) -> Result<bool, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let (holds, _trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| format_logji_error(&e))?;
        Ok(holds)
    }
}

#[cfg(test)]
mod tests {
    use super::NibliEngine;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn temp_db_path(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("nibli_engine_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{name}.redb"))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    #[test]
    fn persistent_assert_does_not_mutate_kb_when_store_is_unavailable() {
        let path = temp_db_path("atomic_assert_store_busy");
        cleanup(&path);

        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        let _borrow = engine.store.borrow();

        let err = engine
            .assert_text("lo gerku cu barda")
            .expect_err("Store borrow conflict should abort assertion");
        assert!(
            err.contains("Store error"),
            "Expected store error, got: {err}"
        );
        assert!(
            !engine
                .query_holds("lo gerku cu barda")
                .expect("Query should still run"),
            "Failed persistent assertions must not leak into the live KB"
        );

        drop(_borrow);
        let store = engine.store.borrow();
        let facts = store
            .as_ref()
            .unwrap()
            .all_active_facts()
            .expect("Store should remain empty");
        assert!(
            facts.is_empty(),
            "Failed persistent assertions must not leak into the store"
        );

        drop(store);
        cleanup(&path);
    }
}
