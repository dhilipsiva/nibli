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
//!   2. **Unmarked rules are Bare-only.** A bare rule plus `past dog(Rex)` does not
//!      derive `past animal(Rex)`; the author's temporal mapping must be written on
//!      the rule literals.
//!   3. **Explicitly-tensed literals are flavor constants.** A `poi pu citka`
//!      antecedent requires a `Past` witness; an explicitly-tensed CONSEQUENT
//!      (`ganai … gi pu …`) derives only that flavor. Every unmarked literal in
//!      the same rule remains Bare.
//!
//! The rewrite makes this syntactic: predicate names gain a flavor suffix (`gerku`
//! → `gerku__pu`; role predicates keep their `_xN` tail parseable: `gerku__pu_x1`),
//! tense nodes are consumed, and every rule is emitted once: unmarked literals use
//! unsuffixed predicates while explicitly tensed literals use their suffix. A
//! program with no tense nodes passes through untouched (identity fast-path), so
//! the pre-du/NAF pipelines are byte-identical when tense is absent.
//!
//! **Tense × restrictor-NAF is flavorized** (since the flavor-aware `NegatedExistsGroup`):
//! a `past ~P` restrictor compiles to `Not(Past(Not(∃P)))`; the rewrite consumes the tense
//! wrapper and suffixes the inner NAF predicate, yielding `Not(Not(∃P__pu))` — which the ASP
//! translator maps to `not P__pu` = "no Past-flavor P witness", exactly the engine's
//! flavor-exact NAF (a Past witness blocks; a bare/future one does not). A bare `~P`
//! remains bare. This leg is differentially oracled by the tense×NAF cases in
//! `corpus_naf.rs` and `generator::random_tense_naf_case`.
//!
//! **Conservative skips** (returned as `Err`, surfaced as a skip — never mis-judged):
//! - **top-level negated (`na`) query** in a tensed program: not a shape the gate poses
//!   (every curated / generated query is positive), and a directly-negated query's tense
//!   semantics were not part of the `NegatedExistsGroup` fix — skip rather than oracle it.
//! - **tense × abstraction** (`__abs_` under any flavor): suffixing would break the
//!   opaque lossless marker identity between rule head and query.
//! - **nested / exotic tense placements** (tense inside an event group, tensed
//!   whole-rule spines): outside this verifier's single-temporal-wrapper fragment,
//!   so they fail closed rather than acquire an invented suffix product. Source KR
//!   tense×deontic stacks are rejected before IR emission; the raw-IR defense below
//!   still refuses a hand-built stack in either order.

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
    if let Some((base, n)) = rel.rsplit_once("_x")
        && !n.is_empty()
        && n.chars().all(|c| c.is_ascii_digit())
    {
        return format!("{base}{}_x{n}", f.suffix());
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

/// Flavorize a whole `(KB, query)` case. Returns rewritten, tense-free buffers;
/// every input buffer produces one output buffer. Identity when no tense node
/// occurs anywhere. `Err` = outside the verified tense fragment → the caller skips
/// the case.
pub fn flavorize(
    kb: &[LogicBuffer],
    query: &LogicBuffer,
) -> Result<(Vec<LogicBuffer>, LogicBuffer), String> {
    let has_tense = kb
        .iter()
        .chain(std::iter::once(query))
        .flat_map(|buf| &buf.nodes)
        .any(|node| tense_of(node).is_some());
    if !has_tense {
        // No tense anywhere — identity fast-path (pre-tense pipelines unchanged).
        return Ok((kb.to_vec(), query.clone()));
    }

    // 2. Conservative guards (see module docs). Tense × restrictor-NAF is NO LONGER
    //    skipped — the rewrite below suffixes the inner NAF predicates so `past ~P`
    //    flavorizes to `not P__pu`. Only abstraction and a top-level `na` query skip here;
    //    exotic placements fail closed inside the rewrite (`copy_suffixed`).
    for buf in kb.iter().chain(std::iter::once(query)) {
        for node in &buf.nodes {
            if let LogicNode::Predicate((rel, _)) = node
                && rel.starts_with("__abs_")
            {
                return Err(
                    "tense with abstraction (suffix would break opaque identity)".to_string(),
                );
            }
        }
        // A top-level negated (`na`) query in a tensed program is not a shape the gate
        // poses; skip rather than oracle an untested (non-restrictor) NAF placement.
        if std::ptr::eq(buf, query) {
            for &r in &buf.roots {
                if matches!(node_at(buf, r)?, LogicNode::NotNode(_)) {
                    return Err(
                        "top-level negated (`na`) query in a tensed program (not a gate shape)"
                            .to_string(),
                    );
                }
            }
        }
    }

    // 3. Rewrite.
    let mut out_kb: Vec<LogicBuffer> = Vec::new();
    for buf in kb {
        out_kb.extend(rewrite_buffer(buf)?);
    }
    let mut out_query = rewrite_buffer(query)?;
    if out_query.len() != 1 {
        // A query buffer is a fact-shape (possibly tensed) — never a rule, so the
        // rewrite yields exactly one buffer. More than one means a ForAll query
        // reached us; that is not a shape the gate poses.
        return Err("query rewrote to multiple flavor copies (unsupported query shape)".into());
    }
    Ok((out_kb, out_query.remove(0)))
}

/// Rewrite one buffer: a fact/query or a rule, always as one output buffer.
fn rewrite_buffer(buf: &LogicBuffer) -> Result<Vec<LogicBuffer>, String> {
    // Rule shape: sole root ForAll.
    if let [r] = buf.roots.as_slice()
        && matches!(node_at(buf, *r)?, LogicNode::ForAllNode(_))
    {
        return rewrite_rule(buf, *r);
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

/// Rewrite a `ForAll` rule once. Unmarked literals remain Bare; each explicit
/// tense wrapper selects that literal's flavor.
fn rewrite_rule(buf: &LogicBuffer, root: u32) -> Result<Vec<LogicBuffer>, String> {
    let mut nodes: Vec<LogicNode> = Vec::new();
    let new_root = copy_rule_node(buf, root, Flavor::Bare, &mut nodes)?;
    Ok(vec![LogicBuffer {
        nodes,
        roots: vec![new_root],
    }])
}

/// Copy a rule-spine node into `out`, applying Bare to unmarked literals and
/// consuming explicit tense wrappers (their subtree gets the wrapper's flavor).
fn copy_rule_node(
    buf: &LogicBuffer,
    id: u32,
    f: Flavor,
    out: &mut Vec<LogicNode>,
) -> Result<u32, String> {
    let node = node_at(buf, id)?;
    if let Some((g, c)) = tense_of(node) {
        // An explicitly-tensed literal (antecedent group or consequent matrix)
        // keeps its declared flavor.
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

    fn valid_abstraction_marker() -> String {
        let mut key = vec![0xa0, 0x10];
        key.extend_from_slice(&0_u64.to_be_bytes());
        key.extend_from_slice(&0_u64.to_be_bytes());
        nibli_types::abstraction::encode_v1(&key)
    }

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
    fn present(nodes: &mut Vec<LogicNode>, c: u32) -> u32 {
        nodes.push(LogicNode::PresentNode(c));
        (nodes.len() - 1) as u32
    }
    fn obligatory(nodes: &mut Vec<LogicNode>, c: u32) -> u32 {
        nodes.push(LogicNode::ObligatoryNode(c));
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
        let (kb2, q2) = flavorize(std::slice::from_ref(&fact), &query).unwrap();
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

    #[test]
    fn raw_tense_deontic_stacks_never_reach_an_external_oracle() {
        let query = {
            let mut nodes = Vec::new();
            let root = group1(&mut nodes, "_ev0", "gerku", con("adam"));
            buf(nodes, vec![root])
        };

        for temporal_outer in [false, true] {
            let mut nodes = Vec::new();
            let leaf = group1(&mut nodes, "_ev0", "gerku", con("adam"));
            let root = if temporal_outer {
                let deontic = obligatory(&mut nodes, leaf);
                past(&mut nodes, deontic)
            } else {
                let temporal = past(&mut nodes, leaf);
                obligatory(&mut nodes, temporal)
            };
            let error = flavorize(&[buf(nodes, vec![root])], &query)
                .expect_err("raw mixed stack must be refused before oracle translation");
            assert!(error.contains("unsupported"), "{error}");
        }
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
    fn unmarked_rule_remains_bare_in_a_tensed_program() {
        // The tensed fact/query trigger flavorization, but they do not clone or
        // re-flavor the bare rule.
        let mut fn_ = Vec::new();
        let g = group1(&mut fn_, "_ev0", "gerku", con("rex"));
        let froot = past(&mut fn_, g);
        let fact = buf(fn_, vec![froot]);

        let mut qn = Vec::new();
        let qg = group1(&mut qn, "_ev0", "danlu", con("rex"));
        let qroot = past(&mut qn, qg);
        let query = buf(qn, vec![qroot]);

        let (kb2, q2) = flavorize(&[bare_rule(), fact], &query).unwrap();
        assert_eq!(kb2.len(), 2, "one rule + one fact");
        let all: Vec<Vec<String>> = kb2.iter().map(rels).collect();
        assert!(all.contains(&vec![
            "gerku".to_string(),
            "gerku_x1".to_string(),
            "danlu".to_string(),
            "danlu_x1".to_string()
        ]));
        assert!(all.iter().all(|rels| {
            !(rels.contains(&"gerku__pu".to_string()) && rels.contains(&"danlu__pu".to_string()))
        }));
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
    fn explicit_rule_literals_keep_their_declared_flavors() {
        // Past(gerku(v)) -> Present(danlu(v)): a cross-flavor mapping is
        // represented directly, with no generated Bare or same-flavor copy.
        let mut n = Vec::new();
        let ante = group1(&mut n, "_e0", "gerku", var("_v0"));
        let pante = past(&mut n, ante);
        let na = not(&mut n, pante);
        let cons = group1(&mut n, "_e1", "danlu", var("_v0"));
        let ccons = present(&mut n, cons);
        let o = or(&mut n, na, ccons);
        let root = forall(&mut n, "_v0", o);
        let rule = buf(n, vec![root]);

        let mut qn = Vec::new();
        let qg = group1(&mut qn, "_ev0", "danlu", con("rex"));
        let qroot = present(&mut qn, qg);
        let query = buf(qn, vec![qroot]);

        let (kb2, _q2) = flavorize(&[rule], &query).unwrap();
        assert_eq!(kb2.len(), 1);
        assert_eq!(
            rels(&kb2[0]),
            vec!["gerku__pu", "gerku__pu_x1", "danlu__ca", "danlu__ca_x1"]
        );
    }

    #[test]
    fn tense_with_naf_restrictor_is_flavorized() {
        // A `past ~gerku` restrictor compiles to `Not(Past(Not(∃gerku)))`. With the
        // flavor-aware NegatedExistsGroup this is no longer skipped: the rewrite consumes
        // the Past wrapper and suffixes the inner NAF predicate, so the rule carries
        // `gerku__pu` (= clingo `not gerku__pu` = "no Past-flavor gerku") and NO bare gerku
        // NAF (the restrictor is an explicit flavor constant).
        let mut n = Vec::new();
        let dom = group1(&mut n, "_e0", "prenu", var("_v0"));
        let ndom = not(&mut n, dom);
        let r = group1(&mut n, "_e1", "gerku", var("_v0"));
        let nr = not(&mut n, r); // Not(∃gerku)
        let pnr = past(&mut n, nr); // Past(Not(∃gerku)) — `past ~gerku`
        let nnr = not(&mut n, pnr); // Not(Past(Not(∃gerku))) — antecedent negation
        let cons = group1(&mut n, "_e2", "morsi", var("_v0"));
        let o2 = or(&mut n, nnr, cons);
        let o1 = or(&mut n, ndom, o2);
        let root = forall(&mut n, "_v0", o1);
        let rule = buf(n, vec![root]);

        // A tensed fact ensures the flavorization pass runs.
        let mut fn_ = Vec::new();
        let g = group1(&mut fn_, "_ev0", "prenu", con("adam"));
        let froot = past(&mut fn_, g);
        let fact = buf(fn_, vec![froot]);

        let mut qn = Vec::new();
        let qroot = group1(&mut qn, "_ev0", "morsi", con("adam"));
        let query = buf(qn, vec![qroot]);

        let (kb2, _q2) = flavorize(&[rule, fact], &query).expect("tense×NAF now flavorizes");
        let all: Vec<Vec<String>> = kb2.iter().map(rels).collect();
        assert!(
            all.iter().any(|r| r.contains(&"gerku__pu".to_string())),
            "NAF predicate must be Past-suffixed: {all:?}"
        );
        assert!(
            all.iter().all(|r| !r.contains(&"gerku".to_string())),
            "explicit `past ~gerku` must not leave a bare gerku NAF: {all:?}"
        );
    }

    #[test]
    fn bare_naf_restrictor_remains_unsuffixed() {
        // ∀v. prenu(v) ∧ ~gerku(v) -> morsi(v), with no temporal wrapper on
        // the NAF literal. An unrelated Past fact forces the pre-pass to run.
        let mut n = Vec::new();
        let dom = group1(&mut n, "_e0", "prenu", var("_v0"));
        let ndom = not(&mut n, dom);
        let r = group1(&mut n, "_e1", "gerku", var("_v0"));
        let nr = not(&mut n, r);
        let nnr = not(&mut n, nr);
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

        let (kb2, _q2) = flavorize(&[rule, fact], &query).unwrap();
        let rule_relations = rels(&kb2[0]);
        assert!(rule_relations.contains(&"gerku".to_string()));
        assert!(
            rule_relations
                .iter()
                .all(|relation| !relation.starts_with("gerku__")),
            "bare NAF must remain unsuffixed: {rule_relations:?}"
        );
    }

    #[test]
    fn tense_with_abstraction_is_skipped() {
        let mut n = Vec::new();
        let m = pred(&mut n, &valid_abstraction_marker(), vec![var("_a")]);
        let root = past(&mut n, m);
        let fact = buf(n, vec![root]);
        let mut qn = Vec::new();
        let qroot = group1(&mut qn, "_ev0", "morsi", con("adam"));
        let query = buf(qn, vec![qroot]);
        let err = flavorize(&[fact], &query).unwrap_err();
        assert!(err.contains("abstraction"), "{err}");
    }
}
