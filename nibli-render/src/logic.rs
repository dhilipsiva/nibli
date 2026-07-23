//! IR -> English back-translation.
//!
//! Walks the flat `LogicBuffer`, regroups Neo-Davidsonian role predicates
//! (`dog(ev) ∧ gerku_x1(ev, x) ∧ gerku_x2(ev, zo'e)`) back into one place-frame
//! per event, fills the curated English template, and renders the surrounding
//! quantifier / connective structure. The output is structure-exposing: quantifier
//! scope stays visible ("For every X, if X is a dog, then X is an animal").

use std::collections::HashMap;

use nibli_lexicon::get_gloss;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

use crate::frame::{deontic_content_phrase, fill_template, frame_template};
use crate::register::Register;
use crate::term::{role_base, role_index};

/// Abstraction-type scaffolding predicates (event/fact/property/…) that only
/// exist to host a nested duty content — never surface as "Y is event".
fn is_abstraction_scaffold(rel: &str) -> bool {
    matches!(rel, "event" | "fact" | "property" | "amount" | "concept")
}

/// Deontic head predicates whose x1 is the duty/content and x2 the obligated party.
fn is_deontic_duty_rel(rel: &str) -> bool {
    matches!(rel, "obligated" | "obliged")
}

/// Render a compiled `LogicBuffer` as readable English.
///
/// Each root becomes one sentence (capitalized, terminated with `.`).
pub fn render_logic_buffer(buf: &LogicBuffer, register: Register) -> String {
    let mut ctx = Ctx::new(register);
    let sentences: Vec<String> = buf
        .roots
        .iter()
        .map(|&root| capitalize_terminate(&render_node(buf, root, &mut ctx)))
        .filter(|s| !s.is_empty())
        .collect();
    sentences.join(" ")
}

/// Render a compiled `LogicBuffer` as an indented, one-node-per-line structural
/// tree with functional term notation — the `[Logic]` half of `:debug`.
///
/// Unlike [`render_logic_buffer`] (which regroups Neo-Davidsonian role predicates
/// into event place-frames and flattens And/Exists for readable English), this
/// shows every node verbatim, so the reader sees the exact compiled FOL shape.
/// The tree is always structural; `_register` is accepted only for signature
/// symmetry with [`render_logic_buffer`] and is ignored. No LISP S-expression is
/// ever emitted — terms render functionally (`dog(_ev0)`, `tenfa_x1(_ev0, 1024)`).
pub fn render_logic_tree(buf: &LogicBuffer, _register: Register) -> String {
    let mut out = String::with_capacity(256);
    for (i, &root) in buf.roots.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        write_tree(&mut out, buf, root, 0);
    }
    out
}

fn write_tree(out: &mut String, buf: &LogicBuffer, id: u32, depth: usize) {
    for _ in 0..depth {
        out.push_str("  ");
    }
    let Some(node) = buf.nodes.get(id as usize) else {
        out.push_str(&format!("[invalid node {id}]\n"));
        return;
    };
    match node {
        LogicNode::Predicate((rel, args)) => {
            out.push_str(&format!("{rel}({})\n", render_term_list(args)));
        }
        LogicNode::ComputeNode((rel, args)) => {
            out.push_str(&format!("{rel}({}) [compute]\n", render_term_list(args)));
        }
        LogicNode::AndNode((l, r)) => {
            out.push_str("And:\n");
            write_tree(out, buf, *l, depth + 1);
            write_tree(out, buf, *r, depth + 1);
        }
        LogicNode::OrNode((l, r)) => {
            out.push_str("Or:\n");
            write_tree(out, buf, *l, depth + 1);
            write_tree(out, buf, *r, depth + 1);
        }
        LogicNode::NotNode(inner) => {
            out.push_str("\u{00ac}:\n"); // ¬
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::ExistsNode((v, body)) => {
            out.push_str(&format!("\u{2203} {v}:\n")); // ∃
            write_tree(out, buf, *body, depth + 1);
        }
        LogicNode::ForAllNode((v, body)) => {
            out.push_str(&format!("\u{2200} {v}:\n")); // ∀
            write_tree(out, buf, *body, depth + 1);
        }
        LogicNode::PastNode(inner) => {
            out.push_str("Past:\n");
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::PresentNode(inner) => {
            out.push_str("Present:\n");
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::FutureNode(inner) => {
            out.push_str("Future:\n");
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::ObligatoryNode(inner) => {
            out.push_str("Obligatory:\n");
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::PermittedNode(inner) => {
            out.push_str("Permitted:\n");
            write_tree(out, buf, *inner, depth + 1);
        }
        LogicNode::CountNode((v, count, body)) => {
            out.push_str(&format!("Count {v} = {count}:\n"));
            write_tree(out, buf, *body, depth + 1);
        }
    }
}

fn render_term_list(args: &[LogicalTerm]) -> String {
    args.iter()
        .map(render_tree_term)
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_tree_term(t: &LogicalTerm) -> String {
    match t {
        LogicalTerm::Variable(v) => v.clone(),
        LogicalTerm::Constant(c) => c.clone(),
        LogicalTerm::Description(d) => format!("the {d}"),
        LogicalTerm::Unspecified => "something".to_string(),
        LogicalTerm::Number(n) => format_number(*n),
    }
}

struct Ctx {
    #[allow(dead_code)]
    register: Register,
    var_names: HashMap<String, String>,
}

impl Ctx {
    fn new(register: Register) -> Self {
        Ctx {
            register,
            var_names: HashMap::new(),
        }
    }

    /// Stable readable name for a logic variable: X, Y, Z, … by first-seen order.
    fn var_name(&mut self, raw: &str) -> String {
        if let Some(v) = self.var_names.get(raw) {
            return v.clone();
        }
        const LETTERS: &[&str] = &["X", "Y", "Z", "W", "V", "U", "T", "S"];
        let n = self.var_names.len();
        let name = LETTERS
            .get(n)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("X{n}"));
        self.var_names.insert(raw.to_string(), name.clone());
        name
    }
}

fn render_node(buf: &LogicBuffer, id: u32, ctx: &mut Ctx) -> String {
    let Some(node) = buf.nodes.get(id as usize) else {
        return String::new();
    };
    match node {
        LogicNode::ForAllNode((var, body)) => render_forall(buf, var, *body, ctx),
        LogicNode::CountNode((var, count, body)) => {
            let _ = ctx.var_name(var);
            format!(
                "exactly {} things are such that {}",
                count,
                render_node(buf, *body, ctx)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "either {} or {}",
                render_node(buf, *l, ctx),
                render_node(buf, *r, ctx)
            )
        }
        LogicNode::NotNode(inner) => {
            format!("it is not the case that {}", render_node(buf, *inner, ctx))
        }
        LogicNode::PastNode(inner) => format!("in the past, {}", render_node(buf, *inner, ctx)),
        LogicNode::PresentNode(inner) => format!("currently, {}", render_node(buf, *inner, ctx)),
        LogicNode::FutureNode(inner) => format!("in the future, {}", render_node(buf, *inner, ctx)),
        LogicNode::ObligatoryNode(inner) => {
            format!("it is required that {}", render_node(buf, *inner, ctx))
        }
        LogicNode::PermittedNode(inner) => {
            format!("it is permitted that {}", render_node(buf, *inner, ctx))
        }
        // Conjunctions, existentials, and bare predicates all flatten into a set
        // of event frames rendered together.
        LogicNode::AndNode(_)
        | LogicNode::ExistsNode(_)
        | LogicNode::Predicate(_)
        | LogicNode::ComputeNode(_) => render_conjunction(buf, id, ctx),
    }
}

/// A universal: `∀var. body`, where `body` is usually the material conditional
/// `Or(Not(antecedent), consequent)`.
fn render_forall(buf: &LogicBuffer, var: &str, body: u32, ctx: &mut Ctx) -> String {
    let x = ctx.var_name(var); // establish var -> X before rendering the body
    if let Some(LogicNode::OrNode((l, r))) = buf.nodes.get(body as usize)
        && let Some(LogicNode::NotNode(ante)) = buf.nodes.get(*l as usize)
    {
        let antecedent = render_node(buf, *ante, ctx);
        let consequent = render_node(buf, *r, ctx);
        return format!("for every {x}, if {antecedent}, then {consequent}");
    }
    let inner = render_node(buf, body, ctx);
    format!("for every {x}, {inner}")
}

/// Collect every predicate reachable through And/Exists from `id` into event
/// frames, render each, and conjoin them with any non-predicate sub-clauses.
fn render_conjunction(buf: &LogicBuffer, id: u32, ctx: &mut Ctx) -> String {
    let mut preds: Vec<(String, Vec<LogicalTerm>)> = Vec::new();
    let mut extras: Vec<String> = Vec::new();
    collect(buf, id, ctx, &mut preds, &mut extras);

    let mut clauses = build_frames(&preds, ctx);
    clauses.extend(extras);
    join_clauses(&clauses)
}

fn collect(
    buf: &LogicBuffer,
    id: u32,
    ctx: &mut Ctx,
    preds: &mut Vec<(String, Vec<LogicalTerm>)>,
    extras: &mut Vec<String>,
) {
    let Some(node) = buf.nodes.get(id as usize) else {
        return;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            collect(buf, *l, ctx, preds, extras);
            collect(buf, *r, ctx, preds, extras);
        }
        // Existential binders (event vars, witnesses) are transparent for frame
        // collection — descend into the body.
        LogicNode::ExistsNode((_var, body)) => collect(buf, *body, ctx, preds, extras),
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            // The opaque abstraction marker (`__abs_<hash>`) is an internal
            // reasoning artifact, not surface content — never render it.
            if crate::is_internal_relation(rel) {
                return;
            }
            preds.push((rel.clone(), args.clone()));
        }
        // Any logical structure nested inside the conjunction is rendered as its
        // own clause and conjoined.
        _ => extras.push(render_node(buf, id, ctx)),
    }
}

/// One accumulated event frame: the place fillers for a `(event, base-relation)`.
struct FrameAcc {
    base: String,
    /// Role-place index (1-based) -> filler term. Empty for a flat (non-decomposed) fact.
    places: HashMap<usize, LogicalTerm>,
    /// Args of the non-role occurrence (flat fact, or the type predicate's event arg).
    flat_args: Vec<LogicalTerm>,
    has_roles: bool,
}

fn term_key(t: Option<&LogicalTerm>) -> String {
    match t {
        Some(LogicalTerm::Variable(s)) => format!("v:{s}"),
        Some(LogicalTerm::Constant(s)) => format!("c:{s}"),
        Some(LogicalTerm::Description(s)) => format!("d:{s}"),
        Some(LogicalTerm::Number(n)) => format!("n:{n}"),
        Some(LogicalTerm::Unspecified) => "u".to_string(),
        None => "_".to_string(),
    }
}

fn build_frames(preds: &[(String, Vec<LogicalTerm>)], ctx: &mut Ctx) -> Vec<String> {
    let mut order: Vec<(String, String)> = Vec::new();
    let mut map: HashMap<(String, String), FrameAcc> = HashMap::new();

    for (rel, args) in preds {
        if let (Some(base), Some(idx)) = (role_base(rel), role_index(rel)) {
            // Role predicate rel_xN(event, filler).
            let key = (term_key(args.first()), base.to_string());
            let acc = map.entry(key.clone()).or_insert_with(|| {
                order.push(key.clone());
                FrameAcc {
                    base: base.to_string(),
                    places: HashMap::new(),
                    flat_args: Vec::new(),
                    has_roles: false,
                }
            });
            acc.has_roles = true;
            if let Some(filler) = args.get(1) {
                acc.places.insert(idx, filler.clone());
            }
        } else {
            // Type predicate rel(event) or a flat fact rel(a, b, …).
            let key = (term_key(args.first()), rel.clone());
            let acc = map.entry(key.clone()).or_insert_with(|| {
                order.push(key.clone());
                FrameAcc {
                    base: rel.clone(),
                    places: HashMap::new(),
                    flat_args: Vec::new(),
                    has_roles: false,
                }
            });
            if acc.flat_args.is_empty() {
                acc.flat_args = args.clone();
            }
        }
    }

    let accs: Vec<FrameAcc> = order
        .into_iter()
        .filter_map(|key| map.remove(&key))
        .collect();
    let accs = collapse_deontic_event_duties(accs);
    accs.into_iter()
        .map(|acc| render_frame(&acc, ctx))
        .filter(|s| !s.is_empty())
        .collect()
}

/// Collapse `obligated(person, event { P() })` packaging:
///   event(Y) ∧ P(…) ∧ obliged(Y, X)  →  "X is obligated to be P"
/// without the word-salad "Y is event and Y is obligated to X".
fn collapse_deontic_event_duties(accs: Vec<FrameAcc>) -> Vec<FrameAcc> {
    let has_scaffold = accs.iter().any(|a| is_abstraction_scaffold(&a.base));
    let has_deontic = accs.iter().any(|a| is_deontic_duty_rel(&a.base));
    if !has_scaffold || !has_deontic {
        return accs;
    }

    let content: Vec<String> = accs
        .iter()
        .filter(|a| !is_deontic_duty_rel(&a.base) && !is_abstraction_scaffold(&a.base))
        .map(|a| deontic_content_phrase(&a.base))
        .collect();
    if content.is_empty() {
        return accs;
    }
    let content_joined = match content.len() {
        1 => content[0].clone(),
        2 => format!("{} and {}", content[0], content[1]),
        _ => {
            let head = &content[..content.len() - 1];
            format!("{}, and {}", head.join(", "), content[content.len() - 1])
        }
    };

    // One rewritten deontic frame per original deontic (usually one), carrying the
    // obligated party in place 2; place 1 becomes the English content phrase via
    // a synthetic constant so fill_template still works.
    let mut out = Vec::new();
    for acc in &accs {
        if !is_deontic_duty_rel(&acc.base) {
            continue;
        }
        let who = acc
            .places
            .get(&2)
            .cloned()
            .or_else(|| acc.flat_args.get(1).cloned());
        let mut places = HashMap::new();
        places.insert(1, LogicalTerm::Constant(content_joined.clone()));
        if let Some(w) = who {
            places.insert(2, w);
        }
        out.push(FrameAcc {
            base: "obligated".into(),
            places,
            flat_args: Vec::new(),
            has_roles: true,
        });
    }
    // Prefer the collapsed form; if we somehow found no deontic heads, fall back.
    if out.is_empty() { accs } else { out }
}

fn render_frame(acc: &FrameAcc, ctx: &mut Ctx) -> String {
    // Deontic collapse stores the content phrase as place-1 constant and the
    // obligated party as place-2 — render with a dedicated template so we get
    // "X is obligated to be secure" not "X is obligated that be secure".
    if is_deontic_duty_rel(&acc.base) {
        if let (Some(LogicalTerm::Constant(content)), Some(who_term)) =
            (acc.places.get(&1), acc.places.get(&2))
        {
            // Content phrases we synthesized start with "be " / bare verb — use "to".
            if let Some(who) = render_term(who_term, ctx) {
                if content.starts_with("be ")
                    || !content.contains(" is ")
                        && !content.chars().next().is_some_and(|c| c.is_uppercase())
                {
                    return format!("{who} is obligated to {content}");
                }
                return format!("{who} is obligated that {content}");
            }
        }
    }
    let places: Vec<Option<String>> = if acc.has_roles {
        let max_idx = acc.places.keys().copied().max().unwrap_or(0);
        (1..=max_idx)
            .map(|i| acc.places.get(&i).and_then(|t| render_term(t, ctx)))
            .collect()
    } else {
        acc.flat_args.iter().map(|t| render_term(t, ctx)).collect()
    };
    fill_template(&frame_template(&acc.base), &places)
}

/// Render a term as an English noun phrase, or `None` for an unspecified place.
fn render_term(t: &LogicalTerm, ctx: &mut Ctx) -> Option<String> {
    match t {
        LogicalTerm::Constant(s) => Some(display_constant(s)),
        LogicalTerm::Description(s) => Some(format!("the {}", get_gloss(s).unwrap_or(s.as_str()))),
        LogicalTerm::Variable(n) => Some(ctx.var_name(n)),
        LogicalTerm::Number(n) => Some(format_number(*n)),
        LogicalTerm::Unspecified => None,
    }
}

/// Constants arrive lowercased from the IR (`bela`, `highsec`). Title-case the
/// first letter for readable English; leave mixed/upper inputs alone.
fn display_constant(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c)
            if c.is_ascii_lowercase() && s.bytes().all(|b| b.is_ascii_lowercase() || b == b'_') =>
        {
            // highsec → Highsec; snake_case → first letter only (good enough).
            format!("{}{}", c.to_ascii_uppercase(), chars.as_str())
        }
        Some(c) => format!("{c}{}", chars.as_str()),
        None => String::new(),
    }
}

fn format_number(n: f64) -> String {
    if n == (n as i64) as f64 {
        format!("{}", n as i64)
    } else {
        format!("{n}")
    }
}

fn join_clauses(clauses: &[String]) -> String {
    match clauses.len() {
        0 => String::new(),
        1 => clauses[0].clone(),
        2 => format!("{} and {}", clauses[0], clauses[1]),
        _ => {
            let head = &clauses[..clauses.len() - 1];
            format!("{}, and {}", head.join(", "), clauses[clauses.len() - 1])
        }
    }
}

fn capitalize_terminate(s: &str) -> String {
    let s = s.trim();
    if s.is_empty() {
        return String::new();
    }
    let mut chars = s.chars();
    let first = chars.next().unwrap().to_uppercase().to_string();
    let mut out = format!("{first}{}", chars.as_str());
    if !out.ends_with('.') {
        out.push('.');
    }
    out
}
