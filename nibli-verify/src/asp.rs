//! Structural translation of a nibli `LogicBuffer` (the smuni FOL IR) into a **clingo**
//! Answer Set Programming (`.lp`) program, for the stratified-NAF differential oracle.
//!
//! Unlike the TPTP translator ([`crate::tptp`]), which renders the event-decomposed IR
//! verbatim (Vampire Skolemizes the `∃ev` heads itself), ASP rule heads cannot contain
//! existentials — and Skolemizing `∃ev` to a *function* `f(x)` would make clingo's
//! grounding non-terminating on chained taxonomy rules. So this translator **regroups the
//! Neo-Davidsonian event decomposition back to surface atoms**: `∃ev. rel(ev) ∧
//! rel_x1(ev,a1) ∧ … ∧ rel_xN(ev,aN)` collapses to the function-free surface atom
//! `rel(a1,…,aN)`. That is sound for this fragment because an event variable has no
//! cross-atom identity here — it only ties the roles of one atom together. Eliminating it
//! keeps the Herbrand base finite, so grounding terminates.
//!
//! The result is function-free stratified **Datalog + negation-as-failure**, whose unique
//! stable/perfect model matches nibli's closed-world stratified semantics (see
//! `proofs/Stratification.lean`). Callers MUST gate each case with
//! [`crate::filter::buffer_asp_mappable`] first; a non-classical node reaching the
//! translator is a filter bug and is surfaced as an `Err`, never silently mistranslated.

use std::collections::{BTreeMap, HashMap, HashSet};

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

/// A regrouped surface atom `rel(a1, …, aN)` — the event decomposition collapsed away.
struct SurfaceAtom {
    rel: String,
    args: Vec<AspTerm>,
}

impl SurfaceAtom {
    fn render(&self) -> String {
        if self.args.is_empty() {
            self.rel.clone()
        } else {
            let a: Vec<String> = self.args.iter().map(AspTerm::render).collect();
            format!("{}({})", self.rel, a.join(", "))
        }
    }
}

/// An ASP term: an uppercase variable (`V0`, `V1`, …) or a lowercase constant.
enum AspTerm {
    Var(String),
    Const(String),
}

impl AspTerm {
    fn render(&self) -> String {
        match self {
            AspTerm::Var(v) => v.clone(),
            AspTerm::Const(c) => c.clone(),
        }
    }
}

/// A body literal: a positive atom `a(..)` or a default-negation literal `not a(..)`.
enum BodyLit {
    Pos(SurfaceAtom),
    Naf(SurfaceAtom),
}

impl BodyLit {
    fn render(&self) -> String {
        match self {
            BodyLit::Pos(a) => a.render(),
            BodyLit::Naf(a) => format!("not {}", a.render()),
        }
    }
}

/// Render a full clingo `.lp` program: every KB buffer root as a fact/rule, and the query
/// reified into a 0-ary `goal` atom shown via `#show goal/0.`. clingo then reports whether
/// `goal` is in the (unique, for a stratified program) stable model — the entailment test.
pub fn render_program(kb: &[LogicBuffer], query: &LogicBuffer) -> Result<String, String> {
    let mut out = String::new();
    for buf in kb {
        for &root in &buf.roots {
            for line in translate_root(buf, root)? {
                out.push_str(&line);
                out.push('\n');
            }
        }
    }

    // Query → goal reification. The query's event groups become the body of a rule deriving
    // the 0-ary `goal`; entailment = `goal` present in the stable model.
    let mut vars = VarMap::new();
    let mut body: Vec<BodyLit> = Vec::new();
    for &root in &query.roots {
        collect_query_body(query, root, &mut vars, &mut body)?;
    }
    if body.is_empty() {
        return Err("query buffer has no goal atoms".to_string());
    }
    let body_str = body
        .iter()
        .map(BodyLit::render)
        .collect::<Vec<_>>()
        .join(", ");
    out.push_str(&format!("goal :- {body_str}.\n"));
    out.push_str("#show goal/0.\n");
    Ok(out)
}

/// Translate one KB root into 0+ `.lp` lines: a `ForAll` is a rule, an `Exists`/`Predicate`
/// is a ground fact, an `And` is a conjunction of facts.
fn translate_root(buf: &LogicBuffer, root: u32) -> Result<Vec<String>, String> {
    match node_at(buf, root)? {
        LogicNode::ForAllNode((v, body)) => translate_rule(buf, v, *body),
        LogicNode::ExistsNode(_) | LogicNode::Predicate(_) => {
            let mut vars = VarMap::new();
            let atom = regroup_event(buf, root, &mut vars)?;
            fact_line(atom).map(|l| vec![l])
        }
        LogicNode::AndNode(_) => {
            let mut lines = Vec::new();
            for c in flatten_and(buf, root)? {
                let mut vars = VarMap::new();
                let atom = regroup_event(buf, c, &mut vars)?;
                lines.push(fact_line(atom)?);
            }
            Ok(lines)
        }
        other => Err(format!("unexpected KB root node: {other:?}")),
    }
}

/// A fact must be ground (no free variables) — a free-var fact is domain-open and unmappable.
fn fact_line(atom: SurfaceAtom) -> Result<String, String> {
    if atom.args.iter().any(|a| matches!(a, AspTerm::Var(_))) {
        return Err(format!(
            "free-variable fact is domain-open: {}",
            atom.render()
        ));
    }
    Ok(format!("{}.", atom.render()))
}

/// Translate a universal rule `ForAll(v, body)`, where `body` is a right-nested `Or` of
/// `Not(...)` antecedent disjuncts terminating in the consequent matrix (verified against
/// smuni `close_quantifier`). Peel the antecedent, regroup the head, emit `head :- body.`.
fn translate_rule(buf: &LogicBuffer, v: &str, body: u32) -> Result<Vec<String>, String> {
    let mut vars = VarMap::new();
    vars.bind(v); // the universal var → V0

    let mut antecedent: Vec<BodyLit> = Vec::new();
    let mut cur = body;
    loop {
        match node_at(buf, cur)? {
            LogicNode::OrNode((neg, rest)) => {
                peel_antecedent_literal(buf, *neg, &mut vars, &mut antecedent)?;
                cur = *rest;
            }
            _ => break, // the terminal disjunct is the consequent (matrix)
        }
    }
    let head = regroup_event(buf, cur, &mut vars)?;
    check_safety(&head, &antecedent)?;

    let body_str = antecedent
        .iter()
        .map(BodyLit::render)
        .collect::<Vec<_>>()
        .join(", ");
    Ok(vec![format!("{} :- {body_str}.", head.render())])
}

/// Peel one antecedent disjunct `Not(...)`. `Not(∃P)` → positive body atom; `Not(Not(∃R))`
/// (the double negation of a `poi na R` restrictor) → NAF body atom; `Not(And(..))`
/// (a compound `poi` restrictor) → each conjunct, positive or NAF.
fn peel_antecedent_literal(
    buf: &LogicBuffer,
    not_id: u32,
    vars: &mut VarMap,
    out: &mut Vec<BodyLit>,
) -> Result<(), String> {
    let inner = match node_at(buf, not_id)? {
        LogicNode::NotNode(i) => *i,
        other => return Err(format!("antecedent disjunct is not Not(...): {other:?}")),
    };
    match node_at(buf, inner)? {
        // Double negation `Not(Not(∃R))` = a `poi na R` restrictor = a NAF literal.
        LogicNode::NotNode(inner2) => {
            out.push(BodyLit::Naf(regroup_event(buf, *inner2, vars)?));
        }
        // Single negation of a positive restrictor = a positive domain / `poi` literal.
        LogicNode::ExistsNode(_) | LogicNode::Predicate(_) => {
            out.push(BodyLit::Pos(regroup_event(buf, inner, vars)?));
        }
        // Compound restrictor (`poi A poi na B`): flatten; each conjunct is Pos or NAF.
        LogicNode::AndNode(_) => {
            for c in flatten_and(buf, inner)? {
                pos_or_naf(buf, c, vars, out)?;
            }
        }
        other => return Err(format!("unrecognized antecedent literal shape: {other:?}")),
    }
    Ok(())
}

/// A conjunct of a compound restrictor: `Not(∃R)` → NAF, `∃P`/`P` → positive.
fn pos_or_naf(
    buf: &LogicBuffer,
    id: u32,
    vars: &mut VarMap,
    out: &mut Vec<BodyLit>,
) -> Result<(), String> {
    match node_at(buf, id)? {
        LogicNode::NotNode(inner) => out.push(BodyLit::Naf(regroup_event(buf, *inner, vars)?)),
        LogicNode::ExistsNode(_) | LogicNode::Predicate(_) => {
            out.push(BodyLit::Pos(regroup_event(buf, id, vars)?))
        }
        other => return Err(format!("unrecognized restrictor conjunct: {other:?}")),
    }
    Ok(())
}

/// Collect the query body: an event group → positive literal, `Not(group)` (a `na`-query)
/// → NAF literal, `And` → both sides.
fn collect_query_body(
    buf: &LogicBuffer,
    id: u32,
    vars: &mut VarMap,
    out: &mut Vec<BodyLit>,
) -> Result<(), String> {
    match node_at(buf, id)? {
        LogicNode::NotNode(inner) => out.push(BodyLit::Naf(regroup_event(buf, *inner, vars)?)),
        LogicNode::AndNode((l, r)) => {
            collect_query_body(buf, *l, vars, out)?;
            collect_query_body(buf, *r, vars, out)?;
        }
        LogicNode::ExistsNode(_) | LogicNode::Predicate(_) => {
            out.push(BodyLit::Pos(regroup_event(buf, id, vars)?))
        }
        other => return Err(format!("unsupported query node: {other:?}")),
    }
    Ok(())
}

/// Collapse `∃ev. type(ev) ∧ type_x1(ev,a1) ∧ … ∧ type_xN(ev,aN)` to the surface atom
/// `type(a1,…,aN)`. A bare `Predicate` (a 0-role/propositional atom, or `du`) maps directly.
fn regroup_event(buf: &LogicBuffer, id: u32, vars: &mut VarMap) -> Result<SurfaceAtom, String> {
    match node_at(buf, id)? {
        LogicNode::Predicate((rel, args)) => Ok(SurfaceAtom {
            rel: sanitize(rel),
            args: args.iter().map(|t| term(t, vars)).collect(),
        }),
        LogicNode::ExistsNode((ev, body)) => {
            let mut type_pred: Option<String> = None;
            let mut roles: BTreeMap<usize, AspTerm> = BTreeMap::new();
            for c in flatten_and(buf, *body)? {
                let (rel, cargs) = match node_at(buf, c)? {
                    LogicNode::Predicate((rel, cargs)) => (rel, cargs),
                    other => return Err(format!("non-atom conjunct in event group: {other:?}")),
                };
                if cargs.len() == 1 && is_var(&cargs[0], ev) {
                    // Type predicate `type(ev)`.
                    if type_pred.is_some() {
                        return Err(format!("two type predicates in event group: {rel}"));
                    }
                    type_pred = Some(rel.clone());
                } else if cargs.len() == 2 && is_var(&cargs[0], ev) {
                    // Role predicate `type_xk(ev, arg)`.
                    let k = parse_role_slot(rel)?;
                    roles.insert(k, term(&cargs[1], vars));
                } else {
                    return Err(format!("unrecognized conjunct shape in event group: {rel}"));
                }
            }
            let rel = type_pred.ok_or_else(|| "event group has no type predicate".to_string())?;
            // Dense x1..xN; a missing interior slot fills the rigid `zoe` (as for arity padding).
            let n = roles.keys().copied().max().unwrap_or(0);
            let args = (1..=n)
                .map(|k| {
                    roles
                        .remove(&k)
                        .unwrap_or_else(|| AspTerm::Const("zoe".to_string()))
                })
                .collect();
            Ok(SurfaceAtom {
                rel: sanitize(&rel),
                args,
            })
        }
        other => Err(format!(
            "expected event group (Exists/Predicate), got {other:?}"
        )),
    }
}

/// Every variable in the head and in every NAF literal must appear in a POSITIVE body
/// literal (clingo's safety condition). The positive domain restrictor `Pos(p(V0))`
/// supplies this; a rule that would be unsafe is rejected (never mis-grounded).
fn check_safety(head: &SurfaceAtom, body: &[BodyLit]) -> Result<(), String> {
    let mut pos_vars: HashSet<&str> = HashSet::new();
    for lit in body {
        if let BodyLit::Pos(a) = lit {
            for t in &a.args {
                if let AspTerm::Var(v) = t {
                    pos_vars.insert(v.as_str());
                }
            }
        }
    }
    let unbound = |atom: &SurfaceAtom, kind: &str| -> Result<(), String> {
        for t in &atom.args {
            if let AspTerm::Var(v) = t {
                if !pos_vars.contains(v.as_str()) {
                    return Err(format!(
                        "unsafe rule: {kind} variable {v} not bound by a positive body literal"
                    ));
                }
            }
        }
        Ok(())
    };
    unbound(head, "head")?;
    for lit in body {
        if let BodyLit::Naf(a) = lit {
            unbound(a, "negative-literal")?;
        }
    }
    Ok(())
}

fn term(t: &LogicalTerm, vars: &mut VarMap) -> AspTerm {
    match t {
        LogicalTerm::Variable(v) => AspTerm::Var(vars.bind(v)),
        LogicalTerm::Constant(c) => AspTerm::Const(sanitize(c)),
        LogicalTerm::Description(d) => AspTerm::Const(sanitize(&format!("le_{d}"))),
        // Numbers belong to the compute fragment (filtered out); render defensively.
        LogicalTerm::Number(n) => AspTerm::Const(sanitize(&format!("num_{n}"))),
        // `zo'e` is a single RIGID unspecified referent — one shared constant, exactly as
        // `tptp.rs`. A role filled with a specific constant must NOT satisfy a `zoe` query
        // (the existential-vs-rigid distinction the tptp fix established).
        LogicalTerm::Unspecified => AspTerm::Const("zoe".to_string()),
    }
}

/// `rel_x1` → slot 1, `foo_x12` → slot 12. Robust to underscores in the type name (splits
/// on the LAST `_x`).
fn parse_role_slot(rel: &str) -> Result<usize, String> {
    rel.rsplit_once("_x")
        .and_then(|(_, n)| n.parse::<usize>().ok())
        .ok_or_else(|| format!("role predicate without a numeric _x suffix: {rel}"))
}

fn is_var(term: &LogicalTerm, name: &str) -> bool {
    matches!(term, LogicalTerm::Variable(v) if v == name)
}

fn node_at(buf: &LogicBuffer, id: u32) -> Result<&LogicNode, String> {
    buf.nodes
        .get(id as usize)
        .ok_or_else(|| format!("node index {id} out of range"))
}

/// Flatten a (possibly left-nested) `And` chain to its leaf node ids; a non-`And` node is a
/// single leaf. Keying roles by slot number afterward makes the result order-independent.
fn flatten_and(buf: &LogicBuffer, id: u32) -> Result<Vec<u32>, String> {
    let mut out = Vec::new();
    collect_and(buf, id, &mut out)?;
    Ok(out)
}

fn collect_and(buf: &LogicBuffer, id: u32, out: &mut Vec<u32>) -> Result<(), String> {
    match node_at(buf, id)? {
        LogicNode::AndNode((l, r)) => {
            collect_and(buf, *l, out)?;
            collect_and(buf, *r, out)?;
        }
        _ => out.push(id),
    }
    Ok(())
}

/// Render a name as a clingo identifier: strip cmevla dots, keep `[A-Za-z0-9_]`, hex-escape
/// anything else (kept injective so distinct source names never collide), and prefix `c_`
/// unless it already begins with a lowercase letter (clingo constants are lowercase-initial;
/// an uppercase initial would be parsed as a variable).
fn sanitize(name: &str) -> String {
    let trimmed = name.trim_matches('.');
    let s = if trimmed.is_empty() { name } else { trimmed };
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            out.push(c);
        } else {
            out.push_str(&format!("_{:x}_", c as u32));
        }
    }
    let ok_start = out.chars().next().is_some_and(|c| c.is_ascii_lowercase());
    if ok_start { out } else { format!("c_{out}") }
}

/// Per-formula renaming of nibli variable names to fresh clingo variables (`V0`, `V1`, …).
/// Uppercase-initial, which clingo requires for variables. Mapping by name keeps repeated
/// references consistent.
struct VarMap {
    map: HashMap<String, String>,
    next: usize,
}

impl VarMap {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
            next: 0,
        }
    }

    fn bind(&mut self, name: &str) -> String {
        if let Some(v) = self.map.get(name) {
            return v.clone();
        }
        let v = format!("V{}", self.next);
        self.next += 1;
        self.map.insert(name.to_string(), v.clone());
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Flat buffer builders (mirror logji's test helpers) ──
    fn pred(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
        nodes.push(LogicNode::Predicate((rel.to_string(), args)));
        (nodes.len() - 1) as u32
    }
    fn and(nodes: &mut Vec<LogicNode>, l: u32, r: u32) -> u32 {
        nodes.push(LogicNode::AndNode((l, r)));
        (nodes.len() - 1) as u32
    }
    fn or(nodes: &mut Vec<LogicNode>, l: u32, r: u32) -> u32 {
        nodes.push(LogicNode::OrNode((l, r)));
        (nodes.len() - 1) as u32
    }
    fn not(nodes: &mut Vec<LogicNode>, x: u32) -> u32 {
        nodes.push(LogicNode::NotNode(x));
        (nodes.len() - 1) as u32
    }
    fn exists(nodes: &mut Vec<LogicNode>, v: &str, b: u32) -> u32 {
        nodes.push(LogicNode::ExistsNode((v.to_string(), b)));
        (nodes.len() - 1) as u32
    }
    fn forall(nodes: &mut Vec<LogicNode>, v: &str, b: u32) -> u32 {
        nodes.push(LogicNode::ForAllNode((v.to_string(), b)));
        (nodes.len() - 1) as u32
    }
    fn var(s: &str) -> LogicalTerm {
        LogicalTerm::Variable(s.to_string())
    }
    fn con(s: &str) -> LogicalTerm {
        LogicalTerm::Constant(s.to_string())
    }

    /// `∃ev. type(ev) ∧ type_x1(ev, arg)` — a 1-place event group over `arg`.
    fn event1(nodes: &mut Vec<LogicNode>, ev: &str, ty: &str, arg: LogicalTerm) -> u32 {
        let t = pred(nodes, ty, vec![var(ev)]);
        let r = pred(nodes, &format!("{ty}_x1"), vec![var(ev), arg]);
        let a = and(nodes, t, r);
        exists(nodes, ev, a)
    }

    fn buf(nodes: Vec<LogicNode>, roots: Vec<u32>) -> LogicBuffer {
        LogicBuffer { nodes, roots }
    }

    #[test]
    fn ground_fact_query() {
        let mut n = Vec::new();
        let root = event1(&mut n, "_ev0", "prenu", con("adam"));
        let q = buf(n, vec![root]);
        let out = render_program(&[], &q).unwrap();
        assert!(out.contains("goal :- prenu(adam)."), "{out}");
        assert!(out.contains("#show goal/0."), "{out}");
    }

    #[test]
    fn rigid_zoe_constant() {
        // A 2-role atom with a trailing Unspecified filler renders `zoe`, not a fresh var.
        let mut n = Vec::new();
        let t = pred(&mut n, "dunda", vec![var("_ev0")]);
        let r1 = pred(&mut n, "dunda_x1", vec![var("_ev0"), con("adam")]);
        let r2 = pred(
            &mut n,
            "dunda_x2",
            vec![var("_ev0"), LogicalTerm::Unspecified],
        );
        let a1 = and(&mut n, t, r1);
        let a2 = and(&mut n, a1, r2);
        let root = exists(&mut n, "_ev0", a2);
        let q = buf(n, vec![root]);
        let out = render_program(&[], &q).unwrap();
        assert!(out.contains("goal :- dunda(adam, zoe)."), "{out}");
    }

    #[test]
    fn horn_rule_regroups() {
        // ForAll(v0, Or(Not(∃prenu(v0)), ∃morsi(v0))) → `morsi(V0) :- prenu(V0).`
        let mut n = Vec::new();
        let p = event1(&mut n, "_e0", "prenu", var("_v0"));
        let np = not(&mut n, p);
        let q = event1(&mut n, "_e1", "morsi", var("_v0"));
        let d = or(&mut n, np, q);
        let root = forall(&mut n, "_v0", d);
        let kb = buf(n, vec![root]);
        let query = {
            let mut m = Vec::new();
            let r = event1(&mut m, "_e2", "morsi", con("adam"));
            buf(m, vec![r])
        };
        let out = render_program(&[kb], &query).unwrap();
        assert!(out.contains("morsi(V0) :- prenu(V0)."), "{out}");
    }

    #[test]
    fn negated_restrictor_becomes_naf() {
        // ForAll(v0, Or(Not(Not(∃gerku(v0))), Or(Not(∃prenu(v0)), ∃morsi(v0))))
        //   → `morsi(V0) :- not gerku(V0), prenu(V0).`  (order-independent; both present)
        let mut n = Vec::new();
        let g = event1(&mut n, "_e0", "gerku", var("_v0"));
        let ng = not(&mut n, g);
        let nng = not(&mut n, ng); // poi na gerku → Not(Not(∃gerku))
        let p = event1(&mut n, "_e1", "prenu", var("_v0"));
        let np = not(&mut n, p);
        let q = event1(&mut n, "_e2", "morsi", var("_v0"));
        let inner = or(&mut n, np, q);
        let body = or(&mut n, nng, inner);
        let root = forall(&mut n, "_v0", body);
        let kb = buf(n, vec![root]);
        let query = {
            let mut m = Vec::new();
            let r = event1(&mut m, "_e3", "morsi", con("adam"));
            buf(m, vec![r])
        };
        let out = render_program(&[kb], &query).unwrap();
        assert!(out.contains("morsi(V0) :- "), "{out}");
        assert!(out.contains("not gerku(V0)"), "{out}");
        assert!(out.contains("prenu(V0)"), "{out}");
    }

    #[test]
    fn unsafe_rule_is_rejected() {
        // A `poi na R`-only rule (no positive domain) → `morsi(V0) :- not gerku(V0).` is
        // unsafe (V0 only in a negative literal); the translator must Err, not emit it.
        let mut n = Vec::new();
        let g = event1(&mut n, "_e0", "gerku", var("_v0"));
        let ng = not(&mut n, g);
        let nng = not(&mut n, ng);
        let q = event1(&mut n, "_e1", "morsi", var("_v0"));
        let body = or(&mut n, nng, q);
        let root = forall(&mut n, "_v0", body);
        let kb = buf(n, vec![root]);
        let query = {
            let mut m = Vec::new();
            let r = event1(&mut m, "_e2", "morsi", con("adam"));
            buf(m, vec![r])
        };
        let err = render_program(&[kb], &query).unwrap_err();
        assert!(err.contains("unsafe"), "{err}");
    }

    #[test]
    fn non_classical_node_errors() {
        // A ComputeNode reaching the translator is a filter bug → Err (never mistranslated).
        let compute = buf(
            vec![LogicNode::ComputeNode(("pilji".into(), vec![]))],
            vec![0],
        );
        let query = {
            let mut m = Vec::new();
            let r = event1(&mut m, "_e0", "morsi", con("adam"));
            buf(m, vec![r])
        };
        assert!(render_program(&[compute], &query).is_err());
    }

    #[test]
    fn sanitize_strips_dots_and_guards_start() {
        assert_eq!(sanitize(".adam."), "adam");
        assert_eq!(sanitize("gerku_x1"), "gerku_x1");
        // Uppercase-initial would parse as a clingo variable → prefixed.
        assert_eq!(sanitize("Adam"), "c_Adam");
    }
}
