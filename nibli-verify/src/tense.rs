//! Tense **flavorization** pre-pass: rewrite tensed `LogicBuffer`s into tense-free
//! buffers over flavor-suffixed predicates, so BOTH oracle translators (TPTP and ASP)
//! can judge the tensed fragment without knowing anything about tense.
//!
//! The engine treats tense wrappers as opaque fact flavors with exact-match
//! unification (`StoredFact::with_tense`, `check_formula_holds_core`'s threaded
//! `tense` context). The observable semantics, pinned by the engine-probe matrix in
//! `corpus.rs`'s `tense_*` cases:
//!
//!   1. **Facts are flavor-exact.** `pu P` / `ca P` / `ba P` / bare `P` are four
//!      disjoint atoms; no wrapper ever satisfies another (the audit's P9 diagonal).
//!   2. **Unmarked rules are flavor-polymorphic.** `ro lo gerku cu danlu` derives a
//!      flavor-f conclusion from flavor-f conditions, for every flavor f — a bare
//!      rule + `pu gerku(rex)` yields `pu danlu(rex)`, chains included.
//!   3. **Explicitly-tensed literals are flavor constants.** A `poi pu citka`
//!      antecedent requires a `Past` witness in EVERY flavor instantiation of the
//!      rule; an explicitly-tensed CONSEQUENT (`ganai … gi pu …`) pins the rule to
//!      that conclusion flavor and evaluates its unmarked conditions at BARE.
//!
//! The rewrite makes this syntactic: predicate names gain a flavor suffix (`gerku`
//! → `gerku__pu`; role predicates keep their `_xN` tail parseable: `gerku__pu_x1`),
//! tense nodes are consumed, and each unmarked rule is emitted once per flavor in
//! the program's flavor set (always including bare — a no-suffix copy). A program
//! with no tense nodes passes through untouched (identity fast-path), so the
//! pre-du/NAF pipelines are byte-identical to before when tense is absent.
//!
//! **Conservative skips** (returned as `Err`, surfaced as a skip — never mis-judged):
//! - **tense × NAF** (a double-negation restrictor or a `na` query in a program that
//!   contains any tense node): the engine's `NegatedExistsGroup` carries NO tense
//!   field, so NAF restrictors are evaluated tenselessly (audit finding U1) — a
//!   witness in the query's flavor does NOT block, a bare witness DOES. Encoding
//!   that into an oracle would canonize behavior the audit flagged as possibly
//!   unintended; it stays un-oracled until U1 is resolved.
//! - **tense × abstraction** (`__abs_` under any flavor): suffixing would break the
//!   opaque content-hash identity between rule head and query.
//! - **nested / exotic tense placements** (tense inside an event group, tensed
//!   whole-rule spines, multi-wrapping): not shapes nibli-semantics emits today; fail closed.

use std::collections::BTreeSet;

use nibli_types::logic::{LogicBuffer, LogicNode};

/// A tense flavor. `Bare` is the unmarked flavor (empty suffix).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Flavor {
    Bare,
    Past,
    Present,
    Future,
}

impl Flavor {
    fn suffix(self) -> &'static str {
        match self {
            Flavor::Bare => "",
            Flavor::Past => "__pu",
            Flavor::Present => "__ca",
            Flavor::Future => "__ba",
        }
    }
}

/// Suffix a predicate name with a flavor, keeping the `_xN` role tail parseable by
/// the ASP regrouper: `gerku` → `gerku__pu`, `gerku_x1` → `gerku__pu_x1`.
fn suffix_rel(rel: &str, f: Flavor) -> String {
    if f == Flavor::Bare {
        return rel.to_string();
    }
    if let Some((base, n)) = rel.rsplit_once("_x") {
        if !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()) {
            return format!("{base}{}_x{n}", f.suffix());
        }
    }
    format!("{rel}{}", f.suffix())
}

fn tense_of(node: &LogicNode) -> Option<(Flavor, u32)> {
    match node {
        LogicNode::PastNode(c) => Some((Flavor::Past, *c)),
        LogicNode::PresentNode(c) => Some((Flavor::Present, *c)),
        LogicNode::FutureNode(c) => Some((Flavor::Future, *c)),
        _ => None,
    }
}

fn node_at(buf: &LogicBuffer, id: u32) -> Result<&LogicNode, String> {
    buf.nodes
        .get(id as usize)
        .ok_or_else(|| format!("node index {id} out of range"))
}

/// Flavorize a whole `(KB, query)` case. Returns rewritten, tense-free buffers (an
/// unmarked rule becomes one buffer per occurring flavor). Identity when no tense
/// node occurs anywhere. `Err` = outside the verified tense fragment → the caller
/// skips the case.
pub fn flavorize(
    kb: &[LogicBuffer],
    query: &LogicBuffer,
) -> Result<(Vec<LogicBuffer>, LogicBuffer), String> {
    // 1. The occurring flavor set (bare always; deterministic order via BTreeSet).
    let mut flavors: BTreeSet<Flavor> = BTreeSet::new();
    flavors.insert(Flavor::Bare);
    for buf in kb.iter().chain(std::iter::once(query)) {
        for node in &buf.nodes {
            if let Some((f, _)) = tense_of(node) {
                flavors.insert(f);
            }
        }
    }
    if flavors.len() == 1 {
        // No tense anywhere — identity fast-path (pre-tense pipelines unchanged).
        return Ok((kb.to_vec(), query.clone()));
    }

    // 2. Conservative guards (see module docs).
    for buf in kb.iter().chain(std::iter::once(query)) {
        for node in &buf.nodes {
            if let LogicNode::Predicate((rel, _)) = node {
                if rel.starts_with("__abs_") {
                    return Err(
                        "tense with abstraction (suffix would break opaque identity)".to_string(),
                    );
                }
            }
            if let LogicNode::NotNode(x) = node {
                if subtree_has_not(buf, *x)? {
                    return Err(
                        "tense with NAF (NegatedExistsGroup is tenseless — audit U1)".to_string(),
                    );
                }
            }
        }
        // A `na` query (root-level NotNode) in a tensed program is NAF territory too.
        if std::ptr::eq(buf, query) {
            for &r in &buf.roots {
                if matches!(node_at(buf, r)?, LogicNode::NotNode(_)) {
                    return Err(
                        "tense with NAF (NegatedExistsGroup is tenseless — audit U1)".to_string(),
                    );
                }
            }
        }
    }

    // 3. Rewrite.
    let mut out_kb: Vec<LogicBuffer> = Vec::new();
    for buf in kb {
        out_kb.extend(rewrite_buffer(buf, &flavors)?);
    }
    let mut out_query = rewrite_buffer(query, &flavors)?;
    if out_query.len() != 1 {
        // A query buffer is a fact-shape (possibly tensed) — never a rule, so the
        // rewrite yields exactly one buffer. More than one means a ForAll query
        // reached us; that is not a shape the gate poses.
        return Err("query rewrote to multiple flavor copies (unsupported query shape)".into());
    }
    Ok((out_kb, out_query.remove(0)))
}

/// Whether the subtree rooted at `id` contains a `NotNode` (used to spot the
/// double-negation NAF restrictor under an antecedent's outer `Not`).
fn subtree_has_not(buf: &LogicBuffer, id: u32) -> Result<bool, String> {
    Ok(match node_at(buf, id)? {
        LogicNode::NotNode(_) => true,
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            subtree_has_not(buf, *l)? || subtree_has_not(buf, *r)?
        }
        LogicNode::ExistsNode((_, b)) | LogicNode::ForAllNode((_, b)) => subtree_has_not(buf, *b)?,
        n => match tense_of(n) {
            Some((_, c)) => subtree_has_not(buf, c)?,
            None => false,
        },
    })
}

/// Rewrite one buffer: a fact/query (per-root, single output buffer) or a rule
/// (one output buffer per flavor if its conclusion is unmarked).
fn rewrite_buffer(
    buf: &LogicBuffer,
    flavors: &BTreeSet<Flavor>,
) -> Result<Vec<LogicBuffer>, String> {
    // Rule shape: sole root ForAll.
    if let [r] = buf.roots.as_slice() {
        if matches!(node_at(buf, *r)?, LogicNode::ForAllNode(_)) {
            return rewrite_rule(buf, *r, flavors);
        }
    }
    // Fact/query shape: each root is a (possibly tensed) event group / atom.
    let mut nodes: Vec<LogicNode> = Vec::new();
    let mut roots: Vec<u32> = Vec::new();
    for &r in &buf.roots {
        let (f, group) = match tense_of(node_at(buf, r)?) {
            Some((f, c)) => (f, c),
            None => (Flavor::Bare, r),
        };
        roots.push(copy_suffixed(buf, group, f, &mut nodes)?);
    }
    Ok(vec![LogicBuffer { nodes, roots }])
}

/// Rewrite a `ForAll` rule. If the matrix (consequent) is explicitly tensed, emit ONE
/// copy: consequent at its explicit flavor, unmarked literals at BARE. Otherwise emit
/// one copy per occurring flavor, with unmarked literals at that flavor. Explicitly-
/// tensed antecedent literals keep their own flavor in every copy.
fn rewrite_rule(
    buf: &LogicBuffer,
    root: u32,
    flavors: &BTreeSet<Flavor>,
) -> Result<Vec<LogicBuffer>, String> {
    // Find the matrix: walk nested ForAlls, then the Or-spine to its terminal.
    let mut cur = root;
    while let LogicNode::ForAllNode((_, b)) = node_at(buf, cur)? {
        cur = *b;
    }
    while let LogicNode::OrNode((_, rest)) = node_at(buf, cur)? {
        cur = *rest;
    }
    let matrix_explicit = tense_of(node_at(buf, cur)?).is_some();

    let unmarked_flavors: Vec<Flavor> = if matrix_explicit {
        vec![Flavor::Bare]
    } else {
        flavors.iter().copied().collect()
    };

    let mut out = Vec::new();
    for &f in &unmarked_flavors {
        let mut nodes: Vec<LogicNode> = Vec::new();
        let new_root = copy_rule_node(buf, root, f, &mut nodes)?;
        out.push(LogicBuffer {
            nodes,
            roots: vec![new_root],
        });
    }
    Ok(out)
}

/// Copy a rule-spine node into `out`, applying flavor `f` to unmarked literals and
/// consuming explicit tense wrappers (their subtree gets the wrapper's flavor).
fn copy_rule_node(
    buf: &LogicBuffer,
    id: u32,
    f: Flavor,
    out: &mut Vec<LogicNode>,
) -> Result<u32, String> {
    let node = node_at(buf, id)?;
    if let Some((g, c)) = tense_of(node) {
        // An explicitly-tensed literal (antecedent group or the consequent matrix):
        // a flavor CONSTANT — same in every copy.
        return copy_suffixed(buf, c, g, out);
    }
    let new = match node {
        LogicNode::ForAllNode((v, b)) => {
            let nb = copy_rule_node(buf, *b, f, out)?;
            LogicNode::ForAllNode((v.clone(), nb))
        }
        LogicNode::OrNode((l, r)) => {
            let nl = copy_rule_node(buf, *l, f, out)?;
            let nr = copy_rule_node(buf, *r, f, out)?;
            LogicNode::OrNode((nl, nr))
        }
        LogicNode::NotNode(x) => {
            let nx = copy_rule_node(buf, *x, f, out)?;
            LogicNode::NotNode(nx)
        }
        LogicNode::AndNode(_) | LogicNode::ExistsNode(_) | LogicNode::Predicate(_) => {
            // An unmarked literal group: takes the copy's flavor.
            return copy_suffixed(buf, id, f, out);
        }
        other => return Err(format!("unsupported node in tensed rule spine: {other:?}")),
    };
    out.push(new);
    Ok((out.len() - 1) as u32)
}

/// Copy the subtree at `id` into `out`, suffixing every predicate with flavor `f`.
/// A tense node INSIDE a group (nested tense) is not a shape nibli-semantics emits — `Err`.
fn copy_suffixed(
    buf: &LogicBuffer,
    id: u32,
    f: Flavor,
    out: &mut Vec<LogicNode>,
) -> Result<u32, String> {
    let new = match node_at(buf, id)? {
        LogicNode::Predicate((rel, args)) => {
            // `du` never occurs under tense here (the du filter admits only the bare
            // sole-root shape), and bare-suffixing is a no-op — safe either way.
            LogicNode::Predicate((suffix_rel(rel, f), args.clone()))
        }
        LogicNode::AndNode((l, r)) => {
            let nl = copy_suffixed(buf, *l, f, out)?;
            let nr = copy_suffixed(buf, *r, f, out)?;
            LogicNode::AndNode((nl, nr))
        }
        LogicNode::OrNode((l, r)) => {
            let nl = copy_suffixed(buf, *l, f, out)?;
            let nr = copy_suffixed(buf, *r, f, out)?;
            LogicNode::OrNode((nl, nr))
        }
        LogicNode::NotNode(x) => {
            let nx = copy_suffixed(buf, *x, f, out)?;
            LogicNode::NotNode(nx)
        }
        LogicNode::ExistsNode((v, b)) => {
            let nb = copy_suffixed(buf, *b, f, out)?;
            LogicNode::ExistsNode((v.clone(), nb))
        }
        LogicNode::ForAllNode((v, b)) => {
            let nb = copy_suffixed(buf, *b, f, out)?;
            LogicNode::ForAllNode((v.clone(), nb))
        }
        other => match tense_of(other) {
            Some(_) => return Err("nested tense wrapper (unsupported shape)".to_string()),
            None => return Err(format!("unsupported node under tense rewrite: {other:?}")),
        },
    };
    out.push(new);
    Ok((out.len() - 1) as u32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nibli_types::logic::LogicalTerm;

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
    fn past(nodes: &mut Vec<LogicNode>, c: u32) -> u32 {
        nodes.push(LogicNode::PastNode(c));
        (nodes.len() - 1) as u32
    }
    fn var(s: &str) -> LogicalTerm {
        LogicalTerm::Variable(s.to_string())
    }
    fn con(s: &str) -> LogicalTerm {
        LogicalTerm::Constant(s.to_string())
    }
    fn buf(nodes: Vec<LogicNode>, roots: Vec<u32>) -> LogicBuffer {
        LogicBuffer { nodes, roots }
    }

    /// `∃ev. ty(ev) ∧ ty_x1(ev, arg)`.
    fn group1(nodes: &mut Vec<LogicNode>, ev: &str, ty: &str, arg: LogicalTerm) -> u32 {
        let t = pred(nodes, ty, vec![var(ev)]);
        let r = pred(nodes, &format!("{ty}_x1"), vec![var(ev), arg]);
        let a = and(nodes, t, r);
        exists(nodes, ev, a)
    }

    fn rels(b: &LogicBuffer) -> Vec<String> {
        b.nodes
            .iter()
            .filter_map(|n| match n {
                LogicNode::Predicate((rel, _)) => Some(rel.clone()),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn suffix_keeps_role_tail_parseable() {
        assert_eq!(suffix_rel("gerku", Flavor::Past), "gerku__pu");
        assert_eq!(suffix_rel("gerku_x1", Flavor::Past), "gerku__pu_x1");
        assert_eq!(suffix_rel("gerku_x12", Flavor::Future), "gerku__ba_x12");
        assert_eq!(suffix_rel("gerku", Flavor::Bare), "gerku");
    }

    #[test]
    fn no_tense_is_identity() {
        let mut n = Vec::new();
        let root = group1(&mut n, "_ev0", "gerku", con("adam"));
        let fact = buf(n, vec![root]);
        let mut qn = Vec::new();
        let qroot = group1(&mut qn, "_ev0", "gerku", con("adam"));
        let query = buf(qn, vec![qroot]);
        let (kb2, q2) = flavorize(&[fact.clone()], &query).unwrap();
        assert_eq!(kb2, vec![fact]);
        assert_eq!(q2, query);
    }

    #[test]
    fn tensed_fact_and_query_are_suffixed() {
        // KB: Past(gerku(adam)); query: Past(gerku(adam)) → both become gerku__pu.
        let mk = |a: &str| {
            let mut n = Vec::new();
            let g = group1(&mut n, "_ev0", "gerku", con(a));
            let root = past(&mut n, g);
            buf(n, vec![root])
        };
        let (kb2, q2) = flavorize(&[mk("adam")], &mk("adam")).unwrap();
        assert_eq!(kb2.len(), 1);
        assert_eq!(rels(&kb2[0]), vec!["gerku__pu", "gerku__pu_x1"]);
        assert_eq!(rels(&q2), vec!["gerku__pu", "gerku__pu_x1"]);
    }

    /// `∀v. Or(Not(gerku-group(v)), danlu-group(v))` — the unmarked taxonomy rule.
    fn bare_rule() -> LogicBuffer {
        let mut n = Vec::new();
        let ante = group1(&mut n, "_e0", "gerku", var("_v0"));
        let na = not(&mut n, ante);
        let cons = group1(&mut n, "_e1", "danlu", var("_v0"));
        let o = or(&mut n, na, cons);
        let root = forall(&mut n, "_v0", o);
        buf(n, vec![root])
    }

    #[test]
    fn unmarked_rule_gets_one_copy_per_flavor() {
        // Program flavor set = {bare, past} (from the tensed fact) → the unmarked
        // rule is emitted twice: a bare copy and a __pu copy (polymorphism, pinned
        // by the engine-probe matrix: bare rule + pu fact derives pu conclusion).
        let mut fn_ = Vec::new();
        let g = group1(&mut fn_, "_ev0", "gerku", con("rex"));
        let froot = past(&mut fn_, g);
        let fact = buf(fn_, vec![froot]);

        let mut qn = Vec::new();
        let qg = group1(&mut qn, "_ev0", "danlu", con("rex"));
        let qroot = past(&mut qn, qg);
        let query = buf(qn, vec![qroot]);

        let (kb2, q2) = flavorize(&[bare_rule(), fact], &query).unwrap();
        // rule×2 + fact×1.
        assert_eq!(kb2.len(), 3);
        let all: Vec<Vec<String>> = kb2.iter().map(rels).collect();
        assert!(all.contains(&vec![
            "gerku".to_string(),
            "gerku_x1".to_string(),
            "danlu".to_string(),
            "danlu_x1".to_string()
        ]));
        assert!(all.contains(&vec![
            "gerku__pu".to_string(),
            "gerku__pu_x1".to_string(),
            "danlu__pu".to_string(),
            "danlu__pu_x1".to_string()
        ]));
        assert_eq!(rels(&q2), vec!["danlu__pu", "danlu__pu_x1"]);
    }

    #[test]
    fn explicit_consequent_pins_one_copy_with_bare_conditions() {
        // ∀v. Or(Not(gerku(v)), Past(danlu(v))) — engine-pinned: fires from a BARE
        // gerku fact only, deriving the Past conclusion. One copy: gerku unsuffixed,
        // danlu__pu.
        let mut n = Vec::new();
        let ante = group1(&mut n, "_e0", "gerku", var("_v0"));
        let na = not(&mut n, ante);
        let cons = group1(&mut n, "_e1", "danlu", var("_v0"));
        let pcons = past(&mut n, cons);
        let o = or(&mut n, na, pcons);
        let root = forall(&mut n, "_v0", o);
        let rule = buf(n, vec![root]);

        let mut qn = Vec::new();
        let qg = group1(&mut qn, "_ev0", "danlu", con("rex"));
        let qroot = past(&mut qn, qg);
        let query = buf(qn, vec![qroot]);

        let (kb2, _q2) = flavorize(&[rule], &query).unwrap();
        assert_eq!(kb2.len(), 1, "explicit consequent → exactly one copy");
        assert_eq!(
            rels(&kb2[0]),
            vec!["gerku", "gerku_x1", "danlu__pu", "danlu__pu_x1"]
        );
    }

    #[test]
    fn tense_with_naf_is_skipped() {
        // A double-negation (NAF) restrictor + a tensed fact → Err (audit U1: the
        // engine's NegatedExistsGroup is tenseless; do not canonize that behavior).
        let mut n = Vec::new();
        let dom = group1(&mut n, "_e0", "prenu", var("_v0"));
        let ndom = not(&mut n, dom);
        let r = group1(&mut n, "_e1", "gerku", var("_v0"));
        let nr = not(&mut n, r);
        let nnr = not(&mut n, nr); // Not(Not(gerku)) — the `poi na` shape
        let cons = group1(&mut n, "_e2", "morsi", var("_v0"));
        let o2 = or(&mut n, nnr, cons);
        let o1 = or(&mut n, ndom, o2);
        let root = forall(&mut n, "_v0", o1);
        let rule = buf(n, vec![root]);

        let mut fn_ = Vec::new();
        let g = group1(&mut fn_, "_ev0", "prenu", con("adam"));
        let froot = past(&mut fn_, g);
        let fact = buf(fn_, vec![froot]);

        let mut qn = Vec::new();
        let qroot = group1(&mut qn, "_ev0", "morsi", con("adam"));
        let query = buf(qn, vec![qroot]);

        let err = flavorize(&[rule, fact], &query).unwrap_err();
        assert!(err.contains("NAF"), "{err}");
    }

    #[test]
    fn tense_with_abstraction_is_skipped() {
        let mut n = Vec::new();
        let m = pred(&mut n, "__abs_h", vec![var("_a")]);
        let root = past(&mut n, m);
        let fact = buf(n, vec![root]);
        let mut qn = Vec::new();
        let qroot = group1(&mut qn, "_ev0", "morsi", con("adam"));
        let query = buf(qn, vec![qroot]);
        let err = flavorize(&[fact], &query).unwrap_err();
        assert!(err.contains("abstraction"), "{err}");
    }
}
