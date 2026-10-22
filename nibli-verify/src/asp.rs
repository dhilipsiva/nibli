//! Structural translation of a nibli `LogicBuffer` (the nibli-semantics FOL IR) into a **clingo**
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
//!
//! **`du` equality** is handled by a canonicalization pre-pass ([`DuClasses`]): the ground
//! `du(c1, c2)` facts are union-found into equivalence classes, every constant in the
//! remaining program is rewritten to its class representative, and the `du` facts are
//! dropped — after canonicalization the merged entities ARE one constant, which is exactly
//! nibli's union-find semantics (substitutivity in fact lookup, rule firing, and NAF checks
//! alike). A `du` QUERY becomes clingo's term-equality builtin `C1 == C2` over the
//! canonicalized constants, so the oracle — not the translator — decides identity.
//!
//! **NON-ground `equals`** — a disequality guard between two rule variables, `~($a = $b)`,
//! as in utopia's multi-sig void rule ("two DISTINCT auditors") — maps to clingo's `!=`
//! builtin, and its positive twin to `==`. The interception must happen BEFORE
//! `regroup_event` (see [`equals_args`]); a fallthrough there renders `not equals(A, B)`,
//! which is vacuously true for every pair because nothing ever derives `equals/2`. The
//! filter admits this shape only when the KB has no ground `du` facts, so structural
//! comparison and `!=` decide identity identically — see
//! [`crate::filter::buffer_asp_mappable_with`].

use std::collections::{BTreeMap, HashMap, HashSet};

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

/// Union-find over the ground `du` facts of a program, with deterministic
/// (lexicographically-smallest) class representatives — the `du` canonicalization pre-pass.
pub struct DuClasses {
    rep: HashMap<String, String>,
}

impl DuClasses {
    /// Collect the `du`-equivalence classes from the KB buffers. Only the sole-root ground
    /// `du(c1, c2)` shape participates (the only shape the filter admits); everything else
    /// is left untouched for the filter to have already rejected.
    pub fn collect(kb: &[LogicBuffer]) -> Self {
        let mut parent: HashMap<String, String> = HashMap::new();
        for buf in kb {
            if let Some((a, b)) = du_fact_args(buf) {
                let ra = find_root(&mut parent, &a);
                let rb = find_root(&mut parent, &b);
                if ra != rb {
                    // Union by lexicographic order: the smaller name becomes the root, so
                    // the representative is deterministic regardless of assertion order.
                    let (small, big) = if ra < rb { (ra, rb) } else { (rb, ra) };
                    parent.insert(big, small);
                }
            }
        }
        // Flatten to a direct constant → representative map.
        let keys: Vec<String> = parent.keys().cloned().collect();
        let mut rep = HashMap::new();
        for k in keys {
            let r = find_root(&mut parent, &k);
            rep.insert(k, r);
        }
        DuClasses { rep }
    }

    /// No ground `du` fact merged anything — the KB's identity relation is plain
    /// syntactic equality. Read by `run_lines_asp` to decide whether a NON-ground `equals`
    /// may map to clingo's `!=` (see `filter::buffer_asp_mappable_with`).
    pub fn is_empty(&self) -> bool {
        self.rep.is_empty()
    }

    /// The canonical representative for a constant (itself if never merged).
    fn canon<'a>(&'a self, c: &'a str) -> &'a str {
        self.rep.get(c).map(String::as_str).unwrap_or(c)
    }

    /// A structural copy of `buf` with every `Constant` rewritten to its representative.
    fn rewrite(&self, buf: &LogicBuffer) -> LogicBuffer {
        let nodes = buf
            .nodes
            .iter()
            .map(|n| match n {
                LogicNode::Predicate((rel, args)) => LogicNode::Predicate((
                    rel.clone(),
                    args.iter().map(|t| self.rewrite_term(t)).collect(),
                )),
                other => other.clone(),
            })
            .collect();
        LogicBuffer {
            nodes,
            roots: buf.roots.clone(),
        }
    }

    fn rewrite_term(&self, t: &LogicalTerm) -> LogicalTerm {
        match t {
            LogicalTerm::Constant(c) => LogicalTerm::Constant(self.canon(c).to_string()),
            other => other.clone(),
        }
    }
}

/// `Some((c1, c2))` iff the buffer is exactly one sole-root ground `du(c1, c2)` fact —
/// the only `du` shape the filter admits into this fragment.
fn du_fact_args(buf: &LogicBuffer) -> Option<(String, String)> {
    if let [r] = buf.roots.as_slice()
        && let Some(LogicNode::Predicate((rel, args))) = buf.nodes.get(*r as usize)
        && rel == "equals"
        && args.len() == 2
        && let (LogicalTerm::Constant(a), LogicalTerm::Constant(b)) = (&args[0], &args[1])
    {
        return Some((a.clone(), b.clone()));
    }
    None
}

/// Path-compressing find for [`DuClasses::collect`]'s string union-find.
fn find_root(parent: &mut HashMap<String, String>, x: &str) -> String {
    let mut cur = x.to_string();
    let mut path = Vec::new();
    while let Some(p) = parent.get(&cur) {
        path.push(cur.clone());
        cur = p.clone();
    }
    for n in path {
        parent.insert(n, cur.clone());
    }
    cur
}

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

/// A body literal: a positive atom `a(..)`, a default-negation literal `not a(..)`, or a
/// term-(dis)equality builtin `t1 == t2` / `t1 != t2` (the canonicalized `du` comparison).
enum BodyLit {
    Pos(SurfaceAtom),
    Naf(SurfaceAtom),
    Eq(AspTerm, AspTerm),
    Neq(AspTerm, AspTerm),
}

impl BodyLit {
    fn render(&self) -> String {
        match self {
            BodyLit::Pos(a) => a.render(),
            BodyLit::Naf(a) => format!("not {}", a.render()),
            BodyLit::Eq(l, r) => format!("{} == {}", l.render(), r.render()),
            BodyLit::Neq(l, r) => format!("{} != {}", l.render(), r.render()),
        }
    }
}

/// The two argument terms of a flat `equals(a, b)` atom, or `None` for anything else.
///
/// `equals` is the ONE relation nibli never event-decomposes (it rides the union-find, not
/// the fact store), so it reaches the translator as a bare arity-2 `Predicate` and must be
/// intercepted BEFORE `regroup_event` — which would happily render it as an ordinary atom
/// `equals(A, B)`.
///
/// That fallthrough is not a cosmetic bug, it is a silently WRONG oracle. Nothing in a
/// generated program ever puts `equals/2` in a head — the `DuClasses` pre-pass drops the
/// `du` facts outright — so `equals(A, B)` is unconditionally false, and `not equals(A, B)`
/// is therefore vacuously TRUE for every pair, INCLUDING `A == A`. A rule guarded by
/// `~($a = $b)` (utopia's multi-sig void needs two DISTINCT auditors) would fire for a
/// single auditor signing twice, clingo would report the void, and the differential would
/// blame the engine for the one guarantee that rule exists to enforce.
fn equals_args(buf: &LogicBuffer, id: u32) -> Result<Option<(&LogicalTerm, &LogicalTerm)>, String> {
    match node_at(buf, id)? {
        LogicNode::Predicate((rel, args)) if rel == "equals" && args.len() == 2 => {
            Ok(Some((&args[0], &args[1])))
        }
        _ => Ok(None),
    }
}

/// Render a full clingo `.lp` program: every KB buffer root as a fact/rule, and the query
/// reified into a 0-ary `goal` atom shown via `#show goal/0.`. clingo then reports whether
/// `goal` is in the (unique, for a stratified program) stable model — the entailment test.
pub fn render_program(kb: &[LogicBuffer], query: &LogicBuffer) -> Result<String, String> {
    // `du` canonicalization pre-pass: union-find the ground `du` facts, rewrite every
    // constant to its class representative, and drop the `du` fact buffers themselves —
    // after canonicalization the merged entities ARE one constant (nibli's union-find
    // semantics, made syntactic). See the module docs.
    let du = DuClasses::collect(kb);
    let kb_rw: Vec<LogicBuffer> = kb
        .iter()
        .filter(|b| du_fact_args(b).is_none())
        .map(|b| du.rewrite(b))
        .collect();
    let query_rw = du.rewrite(query);
    let query = &query_rw;

    let mut out = String::new();
    for buf in &kb_rw {
        for &root in &buf.roots {
            for line in translate_root(buf, root)? {
                out.push_str(&line);
                out.push('\n');
            }
        }
    }

    // Exact-count query: a sole-root `Count(v, n, body)` reifies to a clingo `#count`
    // aggregate — `goal :- #count { V0 : atoms(V0) } = n.` The aggregate counts the
    // distinct entities satisfying the (regrouped) restrictor+body conjunction over the
    // stable model, which equals the clean-core verifier engine's entity count:
    // universals create no implicit witnesses and `du` classes are canonicalized
    // on both sides (see `filter::count_case_guard`).
    if let [r] = query.roots.as_slice()
        && let LogicNode::CountNode((v, n, body)) = node_at(query, *r)?
    {
        let mut vars = VarMap::new();
        let cv = vars.bind(v);
        let mut lits: Vec<String> = Vec::new();
        for c in flatten_and(query, *body)? {
            lits.push(regroup_event(query, c, &mut vars)?.render());
        }
        out.push_str(&format!(
            "goal :- #count {{ {cv} : {} }} = {n}.\n",
            lits.join(", ")
        ));
        out.push_str("#show goal/0.\n");
        return Ok(out);
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
///
/// Nested prenex universals (`all $t: all $s: …` → `ForAll(t, ForAll(s, body))`) are
/// flattened: every binder is registered in the VarMap before the rule body is peeled,
/// so multi-var Horn/NAF rules (utopia's teaches/reward/void gates) map to safe
/// clingo rules instead of failing at the inner ForAll as a "non-event group".
fn translate_root(buf: &LogicBuffer, root: u32) -> Result<Vec<String>, String> {
    match node_at(buf, root)? {
        LogicNode::ForAllNode((v, body)) => {
            let mut binders: Vec<String> = vec![v.clone()];
            let mut cur = *body;
            #[allow(clippy::while_let_loop)] // the match also handles the terminal shapes
            loop {
                match node_at(buf, cur)? {
                    LogicNode::ForAllNode((v2, b2)) => {
                        binders.push(v2.clone());
                        cur = *b2;
                    }
                    _ => break,
                }
            }
            let binder_refs: Vec<&str> = binders.iter().map(String::as_str).collect();
            translate_rule(buf, &binder_refs, cur)
        }
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

/// Translate a (possibly multi-binder) universal rule, where `body` is a right-nested
/// `Or` of `Not(...)` antecedent disjuncts terminating in the consequent matrix
/// (verified against nibli-semantics `close_quantifier`). `binders` is the outer-
/// to-inner prenex list (single-var rules pass one name). Peel the antecedent,
/// regroup the head, emit `head :- body.`.
fn translate_rule(buf: &LogicBuffer, binders: &[&str], body: u32) -> Result<Vec<String>, String> {
    let mut vars = VarMap::new();
    for v in binders {
        vars.bind(v); // outer → V0, next → V1, …
    }

    let mut antecedent: Vec<BodyLit> = Vec::new();
    let mut cur = body;
    #[allow(clippy::while_let_loop)] // the match also handles the terminal shapes
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
    // `equals` is flat, so it must be caught before the `Predicate` arms below hand it to
    // `regroup_event` — see `equals_args` for why that fallthrough is unsound, not untidy.
    if let LogicNode::NotNode(inner2) = node_at(buf, inner)?
        && let Some((l, r)) = equals_args(buf, *inner2)?
    {
        let (l, r) = (term(buf, l, vars), term(buf, r, vars));
        out.push(BodyLit::Neq(l, r));
        return Ok(());
    }
    if let Some((l, r)) = equals_args(buf, inner)? {
        let (l, r) = (term(buf, l, vars), term(buf, r, vars));
        out.push(BodyLit::Eq(l, r));
        return Ok(());
    }
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

/// A conjunct of a compound restrictor: `Not(a = b)` → `!=`, `a = b` → `==`,
/// `Not(∃R)` → NAF, `∃P`/`P` → positive.
fn pos_or_naf(
    buf: &LogicBuffer,
    id: u32,
    vars: &mut VarMap,
    out: &mut Vec<BodyLit>,
) -> Result<(), String> {
    // The `equals` interception, again before `regroup_event` — this is the arm utopia's
    // fifteen-conjunct void rule actually takes for its `~($a = $b)`.
    if let LogicNode::NotNode(inner) = node_at(buf, id)?
        && let Some((l, r)) = equals_args(buf, *inner)?
    {
        let (l, r) = (term(buf, l, vars), term(buf, r, vars));
        out.push(BodyLit::Neq(l, r));
        return Ok(());
    }
    if let Some((l, r)) = equals_args(buf, id)? {
        let (l, r) = (term(buf, l, vars), term(buf, r, vars));
        out.push(BodyLit::Eq(l, r));
        return Ok(());
    }
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
    // A NEGATED identity query. The query filter does not admit this shape today, so this
    // arm is defence in depth — but it costs six lines and closes the same vacuous-`not
    // equals` hole the rule-body path had, so a future filter relaxation cannot reopen it
    // silently. See `equals_args`.
    if let LogicNode::NotNode(inner) = node_at(buf, id)?
        && let Some((l, r)) = equals_args(buf, *inner)?
    {
        let (l, r) = (term(buf, l, vars), term(buf, r, vars));
        out.push(BodyLit::Neq(l, r));
        return Ok(());
    }
    match node_at(buf, id)? {
        // Query-side §6 factoring can place one user-named existential around
        // several independently reified event groups. Peel that binder and
        // let the shared VarMap preserve the join across all body literals;
        // an event existential (`_evN`) still goes through `regroup_event`.
        LogicNode::ExistsNode((var, body)) if var.starts_with('$') => {
            collect_query_body(buf, *body, vars, out)?;
        }
        // A `du` query after canonicalization: identity holds iff both sides rewrote to
        // the SAME representative. Delegate to clingo's term-equality builtin so the
        // oracle — not the translator — decides: `goal :- c1 == c2.`
        LogicNode::Predicate((rel, args)) if rel == "equals" && args.len() == 2 => {
            let l = term(buf, &args[0], vars);
            let r = term(buf, &args[1], vars);
            out.push(BodyLit::Eq(l, r));
        }
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
            args: args.iter().map(|t| term(buf, t, vars)).collect(),
        }),
        // An abstraction wrapper `∃absvar. (nu(absvar) ∧ __abs_<id>(absvar) ∧ <content> ∧
        // <atom that USES absvar>)`. nibli treats `lo nu P` as an opaque referent (matched by the
        // `__abs_<id>` marker, never by its content), so keep only the atom that uses the referent
        // — the referent itself is the opaque constant (see `term`/`abs_const_of`) — and drop the
        // abstraction's inert typing markers and inner content.
        LogicNode::ExistsNode((ev, body)) if abs_const_of(buf, ev).is_some() => {
            let mut using: Vec<u32> = Vec::new();
            for c in flatten_and(buf, *body)? {
                // Skip a bare abstraction-typing marker (`nu(absvar)` / `__abs_<id>(absvar)`).
                if let LogicNode::Predicate((_, cargs)) = node_at(buf, c)?
                    && cargs.len() == 1
                    && is_var(&cargs[0], ev)
                {
                    continue;
                }
                if references_var(buf, c, ev) {
                    using.push(c); // the atom that fills a role with the referent
                }
                // else: the abstraction's own inner content — inert, dropped.
            }
            match using.as_slice() {
                [one] => regroup_event(buf, *one, vars),
                _ => Err(format!(
                    "abstraction referent {ev} is used by {} atoms (expected exactly one)",
                    using.len()
                )),
            }
        }
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
                    roles.insert(k, term(buf, &cargs[1], vars));
                } else {
                    return Err(format!("unrecognized conjunct shape in event group: {rel}"));
                }
            }
            let rel = type_pred.ok_or_else(|| "event group has no type predicate".to_string())?;
            // Dense x1..xN; a missing interior slot fills the rigid `something` (as for arity padding).
            let n = roles.keys().copied().max().unwrap_or(0);
            let args = (1..=n)
                .map(|k| {
                    roles
                        .remove(&k)
                        .unwrap_or_else(|| AspTerm::Const("something".to_string()))
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
            if let AspTerm::Var(v) = t
                && !pos_vars.contains(v.as_str())
            {
                return Err(format!(
                    "unsafe rule: {kind} variable {v} not bound by a positive body literal"
                ));
            }
        }
        Ok(())
    };
    // A comparison builtin binds nothing — clingo requires both sides already bound by a
    // positive body literal, exactly like a negative literal's arguments. Without this a
    // rule whose only mention of a variable is `X != Y` would be rejected by clingo at
    // grounding time (an oracle CRASH read as a harness error), or worse, mis-ground.
    let unbound_term = |t: &AspTerm, kind: &str| -> Result<(), String> {
        if let AspTerm::Var(v) = t
            && !pos_vars.contains(v.as_str())
        {
            return Err(format!(
                "unsafe rule: {kind} variable {v} not bound by a positive body literal"
            ));
        }
        Ok(())
    };
    unbound(head, "head")?;
    for lit in body {
        match lit {
            BodyLit::Naf(a) => unbound(a, "negative-literal")?,
            BodyLit::Eq(l, r) => {
                unbound_term(l, "equality")?;
                unbound_term(r, "equality")?;
            }
            BodyLit::Neq(l, r) => {
                unbound_term(l, "disequality")?;
                unbound_term(r, "disequality")?;
            }
            BodyLit::Pos(_) => {}
        }
    }
    Ok(())
}

fn term(buf: &LogicBuffer, t: &LogicalTerm, vars: &mut VarMap) -> AspTerm {
    match t {
        // An abstraction referent (`event { P }`) is an OPAQUE individual named by its lossless marker —
        // nibli matches abstractions by the complete `__abs_<id>` marker, never by re-deriving content, so
        // both the rule head and the query resolve the same `lo nu` to the same constant. Map the
        // variable to that constant (a stable opaque id) rather than a fresh clingo variable.
        LogicalTerm::Variable(v) => match abs_const_of(buf, v) {
            Some(c) => AspTerm::Const(c),
            None => AspTerm::Var(vars.bind(v)),
        },
        LogicalTerm::Constant(c) => AspTerm::Const(sanitize(c)),
        LogicalTerm::Description(d) => AspTerm::Const(sanitize(&format!("le_{d}"))),
        // Numbers belong to the compute fragment (filtered out); render defensively.
        // If numbers ever enter the mappable fragment: a bare `num_<n>` Herbrand
        // constant IS a domain member here, matching the engine since the
        // numbers-join-the-domain change (asserted numbers are quantifier-domain
        // members — GUARANTEES §Disclosed Sharp Edges).
        LogicalTerm::Number(n) => AspTerm::Const(sanitize(&format!("num_{n}"))),
        // `zo'e` is a single RIGID unspecified referent — one shared constant, exactly as
        // `tptp.rs`. A role filled with a specific constant must NOT satisfy a `something` query
        // (the existential-vs-rigid distinction the tptp fix established).
        LogicalTerm::Unspecified => AspTerm::Const("something".to_string()),
    }
}

/// If `var` is an abstraction referent (some `__abs_<id>(var)` marker exists in the buffer),
/// return the opaque constant naming it (the sanitized `__abs_<id>`). Both the rule head and the
/// query share the same complete lossless marker for the same abstraction kind + body, so this
/// constant matches across them.
fn abs_const_of(buf: &LogicBuffer, var: &str) -> Option<String> {
    for node in &buf.nodes {
        if let LogicNode::Predicate((rel, args)) = node
            && rel.starts_with("__abs_")
            && args.len() == 1
            && is_var(&args[0], var)
        {
            return Some(sanitize(rel));
        }
    }
    None
}

/// Whether `var` appears as an argument anywhere in the sub-tree rooted at `id`.
fn references_var(buf: &LogicBuffer, id: u32, var: &str) -> bool {
    match node_at(buf, id) {
        Ok(LogicNode::Predicate((_, args))) => args.iter().any(|t| is_var(t, var)),
        Ok(LogicNode::AndNode((l, r))) | Ok(LogicNode::OrNode((l, r))) => {
            references_var(buf, *l, var) || references_var(buf, *r, var)
        }
        Ok(LogicNode::NotNode(x)) => references_var(buf, *x, var),
        Ok(LogicNode::ExistsNode((_, b))) | Ok(LogicNode::ForAllNode((_, b))) => {
            references_var(buf, *b, var)
        }
        _ => false,
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

    fn valid_abstraction_marker() -> String {
        let mut key = vec![0xa0, 0x10];
        key.extend_from_slice(&0_u64.to_be_bytes());
        key.extend_from_slice(&0_u64.to_be_bytes());
        nibli_types::abstraction::encode_v1(&key)
    }

    // ── Flat buffer builders (mirror nibli-reason's test helpers) ──
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
    fn abstraction_referent_is_opaque_constant() {
        // The abstraction referent is modeled as an opaque constant keyed by its complete
        // versioned marker; the typing marker + inert content are dropped, keeping only the atom
        // that uses it.
        let mut n = Vec::new();
        let marker_relation = valid_abstraction_marker();
        let marker = pred(&mut n, &marker_relation, vec![var("_absv")]);
        let ev = event1(&mut n, "_ev", "bilga", var("_absv"));
        let body = and(&mut n, marker, ev);
        let root = exists(&mut n, "_absv", body);
        let q = buf(n, vec![root]);
        let out = render_program(&[], &q).unwrap();
        assert!(
            out.contains(&format!("goal :- bilga({}).", sanitize(&marker_relation))),
            "{out}"
        );
    }

    #[test]
    fn rigid_unspecified_constant() {
        // A 2-role atom with a trailing Unspecified filler renders `something`, not a fresh var.
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
        assert!(out.contains("goal :- dunda(adam, something)."), "{out}");
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
    fn nested_prenex_forall_flattens() {
        // ForAll(t, ForAll(s, Or(Not(∃teaches(t,s)), ∃reward(t))))
        //   → `reward(V0) :- teaches(V0, V1).`  (both binders bound)
        let mut n = Vec::new();
        // teaches(ev, t, s) as type + two roles
        let t_type = pred(&mut n, "teaches", vec![var("_e0")]);
        let t_x1 = pred(&mut n, "teaches_x1", vec![var("_e0"), var("_t")]);
        let t_x2 = pred(&mut n, "teaches_x2", vec![var("_e0"), var("_s")]);
        let a1 = and(&mut n, t_type, t_x1);
        let a2 = and(&mut n, a1, t_x2);
        let teaches = exists(&mut n, "_e0", a2);
        let n_teaches = not(&mut n, teaches);
        let r_type = pred(&mut n, "reward", vec![var("_e1")]);
        let r_x1 = pred(&mut n, "reward_x1", vec![var("_e1"), var("_t")]);
        let ra = and(&mut n, r_type, r_x1);
        let reward = exists(&mut n, "_e1", ra);
        let body = or(&mut n, n_teaches, reward);
        let inner = forall(&mut n, "_s", body);
        let root = forall(&mut n, "_t", inner);
        let kb = buf(n, vec![root]);
        let query = {
            let mut m = Vec::new();
            let r = event1(&mut m, "_e2", "reward", con("bela"));
            buf(m, vec![r])
        };
        let out = render_program(&[kb], &query).unwrap();
        assert!(
            out.contains("reward(V0) :- teaches(V0, V1).")
                || (out.contains("reward(V0)")
                    && out.contains("teaches(V0, V1)")
                    && out.contains(":-")),
            "nested prenex must emit a two-var rule, got:\n{out}"
        );
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
            vec![LogicNode::ComputeNode(("product".into(), vec![]))],
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

    /// A sole-root ground `du(a, b)` buffer — the shape the filter admits.
    fn du_fact(a: &str, b: &str) -> LogicBuffer {
        let mut n = Vec::new();
        let root = pred(&mut n, "equals", vec![con(a), con(b)]);
        buf(n, vec![root])
    }

    #[test]
    fn equality_facts_canonicalize_constants_and_are_dropped() {
        // du(bel, adam) + du(kim, bel) → one class, rep = lexicographic min = adam.
        // A fact over `kim` and a query over `bel` must BOTH rewrite to `adam`, and no
        // `du` atom may survive into the program.
        let mut fact_nodes = Vec::new();
        let fact_root = event1(&mut fact_nodes, "_ev0", "prenu", con("kim"));
        let fact = buf(fact_nodes, vec![fact_root]);

        let mut q_nodes = Vec::new();
        let q_root = event1(&mut q_nodes, "_ev0", "prenu", con("bel"));
        let query = buf(q_nodes, vec![q_root]);

        let out = render_program(
            &[du_fact("bel", "adam"), du_fact("kim", "bel"), fact],
            &query,
        )
        .unwrap();
        assert!(out.contains("prenu(adam)."), "{out}");
        assert!(out.contains("goal :- prenu(adam)."), "{out}");
        assert!(
            !out.contains("du("),
            "du atom leaked into the program: {out}"
        );
        assert!(!out.contains("bel"), "unrewritten constant leaked: {out}");
        assert!(!out.contains("kim"), "unrewritten constant leaked: {out}");
    }

    #[test]
    fn du_query_becomes_eq_builtin() {
        // Linked: query du(adam, bel) with KB du(adam, bel) → both canonicalize to adam
        // → `goal :- adam == adam.` (clingo derives goal → Entailed).
        let out = render_program(&[du_fact("adam", "bel")], &du_fact("adam", "bel")).unwrap();
        assert!(out.contains("goal :- adam == adam."), "{out}");

        // Unlinked: query du(adam, bel) with an empty KB → `goal :- adam == bel.`
        // (fails → goal absent → NotEntailed, matching nibli's closed-world FALSE).
        let out = render_program(&[], &du_fact("adam", "bel")).unwrap();
        assert!(out.contains("goal :- adam == bel."), "{out}");
    }

    #[test]
    fn count_query_becomes_count_aggregate() {
        // `re lo gerku cu danlu` → Count(_v0, 2, And(gerku-group, danlu-group)) →
        // goal :- #count { V0 : gerku(V0), danlu(V0) } = 2.
        let mut n = Vec::new();
        let g1 = event1(&mut n, "_ev1", "gerku", var("_v0"));
        let g2 = event1(&mut n, "_ev0", "danlu", var("_v0"));
        let a = and(&mut n, g1, g2);
        n.push(LogicNode::CountNode(("_v0".to_string(), 2, a)));
        let root = (n.len() - 1) as u32;
        let query = buf(n, vec![root]);

        let mut kn = Vec::new();
        let kroot = event1(&mut kn, "_ev0", "gerku", con("adam"));
        let kb = buf(kn, vec![kroot]);

        let out = render_program(&[kb], &query).unwrap();
        assert!(out.contains("gerku(adam)."), "{out}");
        assert!(
            out.contains("goal :- #count { V0 : gerku(V0), danlu(V0) } = 2."),
            "{out}"
        );
        assert!(out.contains("#show goal/0."), "{out}");
    }

    #[test]
    fn equals_canonicalization_is_order_independent() {
        // The representative is the lexicographically-smallest member, regardless of the
        // order the du facts arrive in.
        let a = DuClasses::collect(&[du_fact("kim", "adam"), du_fact("bel", "kim")]);
        let b = DuClasses::collect(&[du_fact("bel", "kim"), du_fact("kim", "adam")]);
        for c in ["adam", "bel", "kim"] {
            assert_eq!(a.canon(c), "adam", "class of {c}");
            assert_eq!(b.canon(c), "adam", "class of {c}");
        }
        // An unmerged constant is its own representative.
        assert_eq!(a.canon("dan"), "dan");
    }

    /// THE VACUOUS-`not equals` GUARD.
    ///
    /// A disequality guard between two rule variables — utopia's `~($a = $b)`, the
    /// multi-sig void rule's "two DISTINCT auditors" clause — must render as clingo's
    /// `!=` builtin. If it ever falls through to `regroup_event` instead, it renders as
    /// `not equals(A, B)`, and since the `DuClasses` pre-pass DROPS every `du` fact,
    /// nothing puts `equals/2` in a head — so `equals(A, B)` is unconditionally false and
    /// `not equals(A, B)` is vacuously TRUE for every pair, `A == A` included.
    ///
    /// That failure is silent and it points the wrong way: clingo would derive the void
    /// for a single auditor signing twice, and the differential would report the ENGINE
    /// as divergent on precisely the guarantee that rule exists to enforce. Hence a
    /// direct render assertion rather than trusting the end-to-end pin alone.
    #[test]
    fn nonground_disequality_renders_as_the_clingo_builtin_not_a_naf_atom() {
        // ∀x ∀y. (sign(x) ∧ sign(y) ∧ ¬(x = y)) → void(x)
        //   compiled shape: ForAll x. ForAll y. Or(Not(body), head)
        let mut nodes = Vec::new();
        let s1 = event1(&mut nodes, "e1", "sign", var("x"));
        let s2 = event1(&mut nodes, "e2", "sign", var("y"));
        let eq = pred(&mut nodes, "equals", vec![var("x"), var("y")]);
        let neq = not(&mut nodes, eq);
        let b1 = and(&mut nodes, s1, s2);
        let body = and(&mut nodes, b1, neq);
        let head = event1(&mut nodes, "e3", "void", var("x"));
        let nb = not(&mut nodes, body);
        let imp = or(&mut nodes, nb, head);
        let fy = forall(&mut nodes, "y", imp);
        let fx = forall(&mut nodes, "x", fy);
        let kb = LogicBuffer {
            nodes,
            roots: vec![fx],
        };

        let mut qn = Vec::new();
        let q = event1(&mut qn, "e9", "void", con("adam"));
        let query = LogicBuffer {
            nodes: qn,
            roots: vec![q],
        };

        let lp = render_program(&[kb], &query).expect("render");
        assert!(
            lp.contains("!="),
            "disequality must reach clingo as the `!=` builtin:\n{lp}"
        );
        assert!(
            !lp.contains("not equals"),
            "`not equals(..)` is vacuously true — nothing derives `equals/2`:\n{lp}"
        );
    }

    /// The positive twin: a non-ground `a = b` conjunct is `==`, never a NAF atom.
    #[test]
    fn nonground_equality_renders_as_the_clingo_builtin() {
        let mut nodes = Vec::new();
        let s1 = event1(&mut nodes, "e1", "sign", var("x"));
        let s2 = event1(&mut nodes, "e2", "sign", var("y"));
        let eq = pred(&mut nodes, "equals", vec![var("x"), var("y")]);
        let b1 = and(&mut nodes, s1, s2);
        let body = and(&mut nodes, b1, eq);
        let head = event1(&mut nodes, "e3", "void", var("x"));
        let nb = not(&mut nodes, body);
        let imp = or(&mut nodes, nb, head);
        let fy = forall(&mut nodes, "y", imp);
        let fx = forall(&mut nodes, "x", fy);
        let kb = LogicBuffer {
            nodes,
            roots: vec![fx],
        };
        let mut qn = Vec::new();
        let q = event1(&mut qn, "e9", "void", con("adam"));
        let query = LogicBuffer {
            nodes: qn,
            roots: vec![q],
        };
        let lp = render_program(&[kb], &query).expect("render");
        assert!(lp.contains("=="), "equality must render as `==`:\n{lp}");
        assert!(
            !lp.contains("equals("),
            "no `equals/2` atom may survive:\n{lp}"
        );
    }
}
