//! Nibli native REPL binary: bypasses the WASM layer entirely.
//!
//! Calls gerna (parser), smuni (semantics), and logji (reasoning) directly
//! as Rust library crates. Includes type conversion functions between each
//! crate's WIT-generated types, implements the Session pipeline and REPL loop.
//!
//! This is a debugging/development binary — no external compute backend,
//! no go'i pro-bridi resolution, no WASM fuel/memory limits.

use reedline::{DefaultPrompt, Reedline, Signal};
use std::collections::HashSet;
use std::fmt::Write as FmtWrite;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

// ─── Type aliases for each crate's WIT-generated types ──────────────

// Gerna (parser) types
mod gerna_ast {
    pub use gerna::bindings::lojban::nibli::ast_types::*;
}
mod gerna_err {
    pub use gerna::bindings::lojban::nibli::error_types::*;
}

// Smuni (semantics) types
mod smuni_ast {
    pub use smuni::bindings::lojban::nibli::ast_types::*;
}
mod smuni_logic {
    pub use smuni::bindings::lojban::nibli::logic_types::*;
}
mod smuni_err {
    pub use smuni::bindings::lojban::nibli::error_types::*;
}

// Logji (reasoning) types
mod logji_logic {
    pub use logji::bindings::lojban::nibli::logic_types::*;
}
mod logji_err {
    pub use logji::bindings::lojban::nibli::error_types::*;
}

// The GuestKnowledgeBase trait — needed to call methods on logji::KnowledgeBase
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

/// Transform Predicate nodes into ComputeNode for registered compute predicates.
/// Operates on smuni's LogicBuffer (before conversion to logji types).
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
// ERROR DISPLAY
// ═══════════════════════════════════════════════════════════════════════

/// Unified error type that can hold errors from any pipeline stage.
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
// S-EXPRESSION RECONSTRUCTION (for :debug)
// ═══════════════════════════════════════════════════════════════════════

fn reconstruct_sexp(buffer: &logji_logic::LogicBuffer, node_id: u32) -> String {
    let mut out = String::with_capacity(256);
    write_sexp(&mut out, buffer, node_id);
    out
}

fn write_sexp(out: &mut String, buffer: &logji_logic::LogicBuffer, node_id: u32) {
    match &buffer.nodes[node_id as usize] {
        logji_logic::LogicNode::Predicate((rel, args)) => {
            out.push_str("(Pred \"");
            out.push_str(rel);
            out.push_str("\" ");
            write_term_list(out, args);
            out.push(')');
        }
        logji_logic::LogicNode::ComputeNode((rel, args)) => {
            out.push_str("(Compute \"");
            out.push_str(rel);
            out.push_str("\" ");
            write_term_list(out, args);
            out.push(')');
        }
        logji_logic::LogicNode::AndNode((l, r)) => {
            out.push_str("(And ");
            write_sexp(out, buffer, *l);
            out.push(' ');
            write_sexp(out, buffer, *r);
            out.push(')');
        }
        logji_logic::LogicNode::OrNode((l, r)) => {
            out.push_str("(Or ");
            write_sexp(out, buffer, *l);
            out.push(' ');
            write_sexp(out, buffer, *r);
            out.push(')');
        }
        logji_logic::LogicNode::NotNode(inner) => {
            out.push_str("(Not ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::ExistsNode((v, body)) => {
            out.push_str("(Exists \"");
            out.push_str(v);
            out.push_str("\" ");
            write_sexp(out, buffer, *body);
            out.push(')');
        }
        logji_logic::LogicNode::ForAllNode((v, body)) => {
            out.push_str("(ForAll \"");
            out.push_str(v);
            out.push_str("\" ");
            write_sexp(out, buffer, *body);
            out.push(')');
        }
        logji_logic::LogicNode::PastNode(inner) => {
            out.push_str("(Past ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::PresentNode(inner) => {
            out.push_str("(Present ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::FutureNode(inner) => {
            out.push_str("(Future ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::ObligatoryNode(inner) => {
            out.push_str("(Obligatory ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::PermittedNode(inner) => {
            out.push_str("(Permitted ");
            write_sexp(out, buffer, *inner);
            out.push(')');
        }
        logji_logic::LogicNode::CountNode((v, count, body)) => {
            out.push_str("(Count \"");
            out.push_str(v);
            out.push_str("\" ");
            let _ = write!(out, "{}", count);
            out.push(' ');
            write_sexp(out, buffer, *body);
            out.push(')');
        }
    }
}

fn write_term_list(out: &mut String, args: &[logji_logic::LogicalTerm]) {
    if args.is_empty() {
        out.push_str("(Nil)");
        return;
    }
    out.push_str("(Cons ");
    write_term(out, &args[0]);
    out.push(' ');
    write_term_list(out, &args[1..]);
    out.push(')');
}

fn write_term(out: &mut String, term: &logji_logic::LogicalTerm) {
    match term {
        logji_logic::LogicalTerm::Variable(v) => {
            out.push_str("(Var \"");
            out.push_str(v);
            out.push_str("\")");
        }
        logji_logic::LogicalTerm::Constant(c) => {
            out.push_str("(Const \"");
            out.push_str(c);
            out.push_str("\")");
        }
        logji_logic::LogicalTerm::Description(d) => {
            out.push_str("(Desc \"");
            out.push_str(d);
            out.push_str("\")");
        }
        logji_logic::LogicalTerm::Unspecified => out.push_str("(Zoe)"),
        logji_logic::LogicalTerm::Number(n) => {
            let _ = write!(out, "(Num {})", n);
        }
    }
}

fn debug_sexp(buffer: &logji_logic::LogicBuffer) -> String {
    buffer
        .roots
        .iter()
        .map(|&id| reconstruct_sexp(buffer, id))
        .collect::<Vec<_>>()
        .join("\n")
}

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE DISPLAY
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
            format!("{}: {} -> {}", method, detail, tag)
        }
        logji_logic::ProofRule::ComputeCheck((method, detail)) => {
            format!("Compute ({}): {} -> {}", method, detail, tag)
        }
        logji_logic::ProofRule::Asserted(sexp) => format!("Asserted: {} -> {}", sexp, tag),
        logji_logic::ProofRule::Derived((label, sexp)) => {
            format!("Derived ({}): {} -> {}", label, sexp, tag)
        }
        logji_logic::ProofRule::ProofRef(sexp) => {
            format!("(proved above): {} -> {}", sexp, tag)
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
    format_proof_node(&trace.steps, trace.root, 1, &mut out);
    out
}

// ═══════════════════════════════════════════════════════════════════════
// SESSION: Pipeline orchestration
// ═══════════════════════════════════════════════════════════════════════

struct Session {
    kb: logji::KnowledgeBase,
    compute_predicates: HashSet<String>,
}

impl Session {
    fn new() -> Self {
        let mut compute_preds = HashSet::new();
        compute_preds.insert("pilji".to_string());
        compute_preds.insert("sumji".to_string());
        compute_preds.insert("dilcu".to_string());
        Session {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: compute_preds,
        }
    }

    /// Full pipeline: text -> gerna parse -> convert -> smuni compile -> convert -> logji buffer.
    /// Returns the logji-typed LogicBuffer ready for assertion/query.
    fn compile_text(&self, input: &str) -> Result<logji_logic::LogicBuffer, NibliError> {
        // 1. Parse with gerna
        let parse_result =
            gerna::parse_text_native(input.to_string()).map_err(NibliError::Gerna)?;

        // Check for total parse failure
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

        // Check for partial parse failure (abort assertion to prevent unsound reasoning)
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

        // 2. Convert gerna AstBuffer -> smuni AstBuffer
        let smuni_ast = convert_ast_buffer(&parse_result.buffer);

        // 3. Compile with smuni
        let mut smuni_buf = smuni::compile_buffer_native(smuni_ast).map_err(NibliError::Smuni)?;

        // 4. Transform compute nodes
        transform_compute_nodes(&mut smuni_buf, &self.compute_predicates);

        // 5. Convert smuni LogicBuffer -> logji LogicBuffer
        let logji_buf = convert_logic_buffer_s2l(&smuni_buf);

        Ok(logji_buf)
    }

    fn assert_text(&self, input: &str) -> Result<u64, NibliError> {
        let buf = self.compile_text(input)?;
        self.kb
            .assert_fact(buf, input.to_string())
            .map_err(NibliError::Logji)
    }

    fn query_text(&self, input: &str) -> Result<bool, NibliError> {
        let buf = self.compile_text(input)?;
        self.kb.query_entailment(buf).map_err(NibliError::Logji)
    }

    fn query_find_text(
        &self,
        input: &str,
    ) -> Result<Vec<Vec<logji_logic::WitnessBinding>>, NibliError> {
        let buf = self.compile_text(input)?;
        self.kb.query_find(buf).map_err(NibliError::Logji)
    }

    fn query_text_with_proof(
        &self,
        input: &str,
    ) -> Result<(bool, logji_logic::ProofTrace), NibliError> {
        let buf = self.compile_text(input)?;
        self.kb
            .query_entailment_with_proof(buf)
            .map_err(NibliError::Logji)
    }

    fn compile_debug(&self, input: &str) -> Result<String, NibliError> {
        let buf = self.compile_text(input)?;
        Ok(debug_sexp(&buf))
    }

    fn reset(&self) -> Result<(), NibliError> {
        self.kb.reset().map_err(NibliError::Logji)
    }

    fn list_facts(&self) -> Result<Vec<logji_logic::FactSummary>, NibliError> {
        self.kb.list_facts().map_err(NibliError::Logji)
    }

    fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.kb.retract_fact(id).map_err(NibliError::Logji)
    }

    fn assert_fact_direct(
        &self,
        relation: String,
        args: Vec<logji_logic::LogicalTerm>,
    ) -> Result<u64, NibliError> {
        let label = format!(":assert {}", relation);
        let nodes = vec![logji_logic::LogicNode::Predicate((relation, args))];
        let buf = logji_logic::LogicBuffer {
            nodes,
            roots: vec![0],
        };
        self.kb.assert_fact(buf, label).map_err(NibliError::Logji)
    }

    fn register_compute_predicate(&mut self, name: String) {
        self.compute_predicates.insert(name);
    }
}

// ═══════════════════════════════════════════════════════════════════════
// DIRECT ASSERTION PARSER
// ═══════════════════════════════════════════════════════════════════════

/// Parse a `:assert` command string into (relation, args).
/// Numbers are detected automatically; everything else is treated as a Constant.
fn parse_assert_args(input: &str) -> Result<(String, Vec<logji_logic::LogicalTerm>), String> {
    let parts: Vec<&str> = input.split_whitespace().collect();
    if parts.is_empty() {
        return Err("Usage: :assert <relation> <arg1> <arg2> ...".to_string());
    }
    let relation = parts[0].to_string();
    let args = parts[1..]
        .iter()
        .map(|&s| {
            if let Ok(n) = s.parse::<f64>() {
                logji_logic::LogicalTerm::Number(n)
            } else {
                logji_logic::LogicalTerm::Constant(s.to_string())
            }
        })
        .collect();
    Ok((relation, args))
}

// ═══════════════════════════════════════════════════════════════════════
// MAIN + REPL LOOP
// ═══════════════════════════════════════════════════════════════════════

fn run_test_book() {
    eprintln!("[test-book] Starting book example test...");
    let mut session = Session::new();

    let commands = vec![
        (".i lo prenu cu ponse lo datni", "assert1"),
        (
            ".i ro lo prenu poi ponse lo datni cu bilga lo nu curmi",
            "assert2",
        ),
        ("?! lo prenu cu bilga lo nu curmi", "proof-query"),
    ];

    for (input, label) in &commands {
        eprintln!("\n[test-book] === {label}: {input} ===");
        let trimmed = input.trim();

        if let Some(text) = trimmed.strip_prefix("?!") {
            let text = text.trim();
            eprintln!("[test-book] Calling query_text_with_proof...");
            match session.query_text_with_proof(text) {
                Ok((holds, trace)) => {
                    println!("Result: {}", if holds { "TRUE" } else { "FALSE" });
                    println!("{}", format_proof_trace(&trace));
                }
                Err(e) => println!("Error: {}", format_error(&e)),
            }
        } else {
            match session.assert_text(trimmed) {
                Ok(fact_id) => println!("[Fact #{fact_id}] Asserted."),
                Err(e) => println!("Error: {}", format_error(&e)),
            }
        }
    }
    eprintln!("[test-book] Done.");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--test-book") {
        run_test_book();
        return;
    }

    println!("==================================================");
    println!(" Nibli Native REPL - Direct Rust (no WASM)        ");
    println!("==================================================");

    let mut session = Session::new();

    let mut line_editor = Reedline::create();
    let prompt = DefaultPrompt::default();

    println!(
        "Commands: :quit :reset :load <file> :facts :retract <id> :debug <text> :compute <name> :assert <rel> <args..> :help"
    );
    println!(
        "Prefix '?' for queries, '?!' for proof trace, '??' for find, plain text for assertions.\n"
    );

    loop {
        let sig = line_editor.read_line(&prompt);
        match sig {
            Ok(Signal::Success(buffer)) => {
                let input = buffer.trim();
                if input.is_empty() {
                    continue;
                }

                // ── Exact-match commands ──
                match input {
                    ":quit" | ":q" => break,
                    ":reset" | ":r" => {
                        match session.reset() {
                            Ok(()) => println!("[Reset] Knowledge base cleared."),
                            Err(e) => println!("{}", format_error(&e)),
                        }
                        continue;
                    }
                    ":facts" => {
                        match session.list_facts() {
                            Ok(facts) => {
                                if facts.is_empty() {
                                    println!("[Facts] Knowledge base is empty.");
                                } else {
                                    println!("[Facts] {} active fact(s):", facts.len());
                                    for f in &facts {
                                        let roots_label =
                                            if f.root_count == 1 { "root" } else { "roots" };
                                        println!(
                                            "  #{}: {} ({} {})",
                                            f.id, f.label, f.root_count, roots_label
                                        );
                                    }
                                }
                            }
                            Err(e) => println!("{}", format_error(&e)),
                        }
                        continue;
                    }
                    ":help" | ":h" => {
                        println!("  <text>              Assert Lojban as fact");
                        println!("  ? <text>            Query entailment (true/false)");
                        println!("  ?! <text>           Query with proof trace");
                        println!("  ?? <text>           Find witnesses (answer variables)");
                        println!("  :debug <text>       Show compiled logic tree");
                        println!("  :load <filepath>    Load a .lojban file (assert each line)");
                        println!("  :compute <name>     Register predicate for compute dispatch");
                        println!("  :assert <rel> <args..> Assert a ground fact directly");
                        println!("  :retract <id>       Retract a fact by ID (rebuilds KB)");
                        println!("  :facts              List all active facts in the KB");
                        println!("  :reset              Clear all facts (fresh KB)");
                        println!("  :quit               Exit");
                        continue;
                    }
                    _ => {}
                }

                // ── Prefix-match commands ──
                if let Some(debug_text) = input.strip_prefix(":debug ") {
                    let text = debug_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :debug <lojban text>");
                        continue;
                    }
                    match session.compile_debug(text) {
                        Ok(sexp) => println!("[Logic] {}", sexp),
                        Err(e) => println!("{}", format_error(&e)),
                    }
                } else if let Some(compute_name) = input.strip_prefix(":compute ") {
                    let name = compute_name.trim();
                    if name.is_empty() {
                        println!("[Host] Usage: :compute <predicate-name>");
                        continue;
                    }
                    session.register_compute_predicate(name.to_string());
                    println!("[Compute] Registered '{}' for compute dispatch", name);
                } else if let Some(assert_args) = input.strip_prefix(":assert ") {
                    let text = assert_args.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: :assert <relation> <arg1> <arg2> ...");
                        continue;
                    }
                    match parse_assert_args(text) {
                        Ok((relation, args)) => {
                            let display_args: Vec<String> = args
                                .iter()
                                .map(|a| match a {
                                    logji_logic::LogicalTerm::Number(n) => format!("{}", n),
                                    logji_logic::LogicalTerm::Constant(s) => s.clone(),
                                    _ => "?".to_string(),
                                })
                                .collect();
                            match session.assert_fact_direct(relation.clone(), args) {
                                Ok(fact_id) => println!(
                                    "[Fact #{}] {}({}) asserted.",
                                    fact_id,
                                    relation,
                                    display_args.join(", ")
                                ),
                                Err(e) => println!("{}", format_error(&e)),
                            }
                        }
                        Err(e) => println!("[Error] {}", e),
                    }
                } else if let Some(retract_arg) = input.strip_prefix(":retract ") {
                    let arg = retract_arg.trim();
                    match arg.parse::<u64>() {
                        Ok(id) => match session.retract_fact(id) {
                            Ok(()) => println!("[Retract] Fact #{} retracted. KB rebuilt.", id),
                            Err(e) => println!("{}", format_error(&e)),
                        },
                        Err(_) => println!("[Host] Usage: :retract <fact-id>"),
                    }
                } else if let Some(load_arg) = input.strip_prefix(":load ") {
                    let filepath = load_arg.trim();
                    if filepath.is_empty() {
                        println!("[Host] Usage: :load <filepath>");
                        continue;
                    }
                    let path = Path::new(filepath);
                    if !path.exists() {
                        println!("[Load] File not found: {}", filepath);
                        continue;
                    }
                    let file = match File::open(path) {
                        Ok(f) => f,
                        Err(e) => {
                            println!("[Load] Cannot open file: {}", e);
                            continue;
                        }
                    };
                    let reader = BufReader::new(file);
                    let mut asserted = 0u32;
                    let mut skipped = 0u32;
                    let mut errors = 0u32;
                    for (line_num, line_result) in reader.lines().enumerate() {
                        let line = match line_result {
                            Ok(l) => l,
                            Err(e) => {
                                println!("[Load] Read error at line {}: {}", line_num + 1, e);
                                errors += 1;
                                continue;
                            }
                        };
                        let trimmed = line.trim();
                        if trimmed.is_empty() || trimmed.starts_with('#') {
                            skipped += 1;
                            continue;
                        }
                        match session.assert_text(trimmed) {
                            Ok(fact_id) => {
                                println!("[Fact #{}] {}", fact_id, trimmed);
                                asserted += 1;
                            }
                            Err(e) => {
                                println!("[Load] line {}: {}", line_num + 1, format_error(&e));
                                errors += 1;
                            }
                        }
                    }
                    println!(
                        "[Load] Done: {} asserted, {} skipped, {} errors",
                        asserted, skipped, errors
                    );
                } else if let Some(find_text) = input.strip_prefix("??") {
                    let text = find_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?? <lojban query with ma>");
                        continue;
                    }
                    match session.query_find_text(text) {
                        Ok(binding_sets) => {
                            if binding_sets.is_empty() {
                                println!("[Find] No witnesses found.");
                            } else {
                                for bindings in &binding_sets {
                                    let parts: Vec<String> = bindings
                                        .iter()
                                        .map(|b| {
                                            format!(
                                                "{} = {}",
                                                b.variable,
                                                format_term_display(&b.term)
                                            )
                                        })
                                        .collect();
                                    println!("[Find] {}", parts.join(", "));
                                }
                            }
                        }
                        Err(e) => println!("{}", format_error(&e)),
                    }
                } else if let Some(proof_text) = input.strip_prefix("?!") {
                    let text = proof_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ?! <lojban query>");
                        continue;
                    }
                    match session.query_text_with_proof(text) {
                        Ok((result, trace)) => {
                            let tag = if result { "TRUE" } else { "FALSE" };
                            println!("[Proof] {}", tag);
                            print!("{}", format_proof_trace(&trace));
                        }
                        Err(e) => println!("{}", format_error(&e)),
                    }
                } else if let Some(query_text) = input.strip_prefix('?') {
                    let text = query_text.trim();
                    if text.is_empty() {
                        println!("[Host] Usage: ? <lojban query>");
                        continue;
                    }
                    match session.query_text(text) {
                        Ok(true) => println!("[Query] TRUE"),
                        Ok(false) => println!("[Query] FALSE"),
                        Err(e) => println!("{}", format_error(&e)),
                    }
                } else {
                    // Bare text: assertion
                    match session.assert_text(input) {
                        Ok(fact_id) => println!("[Fact #{}] Asserted.", fact_id),
                        Err(e) => println!("{}", format_error(&e)),
                    }
                }
            }
            Ok(Signal::CtrlD) | Ok(Signal::CtrlC) => break,
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}
