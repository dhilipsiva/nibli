//! Structural translation of a nibli `LogicBuffer` (the smuni FOL IR) into a TPTP
//! FOF problem for the Vampire oracle.
//!
//! This map is only sound for the Horn / NAF-free fragment — callers MUST gate each
//! case with [`crate::filter`] first. On a negation-free program every `NotNode` is a
//! material-implication arrow (a universal restrictive / `ganai..gi` compiles to
//! `Or(Not(A), B)` in `nibli-semantics/src/semantic/compile.rs`), so a direct boolean map yields
//! the correct classical theory. The translator never emits the non-classical nodes
//! (`ComputeNode`, tense/deontic, `CountNode`); reaching one is a filter bug and is
//! surfaced as an error rather than silently mistranslated. The identity predicate
//! `du` maps to TPTP NATIVE `=` (see `render_atom`) — congruence closure over a
//! definite theory matches nibli's union-find semantics in both directions.

use std::collections::HashMap;

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

/// Render a full TPTP FOF problem: every KB buffer root as an `axiom`, the query
/// buffer roots (conjoined) as the `conjecture`. Vampire then reports `Theorem`
/// (KB entails the query) or `CounterSatisfiable` (it does not).
pub fn render_problem(kb: &[LogicBuffer], query: &LogicBuffer) -> Result<String, String> {
    let mut out = String::new();
    let mut ax = 0usize;
    for buf in kb {
        for &root in &buf.roots {
            out.push_str(&format!(
                "fof(ax_{ax}, axiom, {}).\n",
                render_root(buf, root)?
            ));
            ax += 1;
        }
    }
    let goal = match query.roots.as_slice() {
        [] => return Err("query buffer has no roots".to_string()),
        [r] => render_root(query, *r)?,
        roots => {
            let parts: Result<Vec<_>, _> = roots.iter().map(|r| render_root(query, *r)).collect();
            format!("({})", parts?.join(" & "))
        }
    };
    out.push_str(&format!("fof(goal, conjecture, {goal}).\n"));
    Ok(out)
}

/// Render one root formula with its own fresh variable namespace (TPTP variables are
/// formula-scoped).
fn render_root(buf: &LogicBuffer, root: u32) -> Result<String, String> {
    let mut vars = VarMap::new();
    render_node(buf, root, &mut vars)
}

fn render_node(buf: &LogicBuffer, id: u32, vars: &mut VarMap) -> Result<String, String> {
    let node = buf
        .nodes
        .get(id as usize)
        .ok_or_else(|| format!("node index {id} out of range"))?;
    Ok(match node {
        LogicNode::Predicate((rel, args)) => render_atom(rel, args, vars),
        LogicNode::AndNode((l, r)) => {
            format!(
                "({} & {})",
                render_node(buf, *l, vars)?,
                render_node(buf, *r, vars)?
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "({} | {})",
                render_node(buf, *l, vars)?,
                render_node(buf, *r, vars)?
            )
        }
        LogicNode::NotNode(x) => format!("(~ {})", render_node(buf, *x, vars)?),
        LogicNode::ExistsNode((v, b)) => {
            let tv = vars.bind(v);
            let body = render_node(buf, *b, vars)?;
            format!("(? [{tv}] : {body})")
        }
        LogicNode::ForAllNode((v, b)) => {
            let tv = vars.bind(v);
            let body = render_node(buf, *b, vars)?;
            format!("(! [{tv}] : {body})")
        }
        other => {
            return Err(format!(
                "non-classical node reached the translator (filter bug): {other:?}"
            ));
        }
    })
}

fn render_atom(rel: &str, args: &[LogicalTerm], vars: &mut VarMap) -> String {
    // `du` is nibli's identity predicate (union-find with path compression +
    // substitutivity). Map it to TPTP NATIVE equality: over a definite (Horn,
    // negation-free) theory, classical congruence closure derives exactly the
    // reflexive/symmetric/transitive/substitutive consequences nibli's equivalence
    // index derives — in both directions, so `FALSE ⟺ not-entailed` holds for
    // equality atoms too. Rendering `du` as an uninterpreted binary predicate here
    // would be a soundness trap: nibli's TRUE-via-substitutivity would look like a
    // divergence. (The filter admits only the sole-root ground `du(c1, c2)` shape.)
    if rel == "equals" && args.len() == 2 {
        let l = render_term(&args[0], vars);
        let r = render_term(&args[1], vars);
        return format!("({l} = {r})");
    }
    if args.is_empty() {
        return sanitize_functor(rel);
    }
    let terms: Vec<String> = args.iter().map(|t| render_term(t, vars)).collect();
    format!("{}({})", sanitize_functor(rel), terms.join(", "))
}

fn render_term(t: &LogicalTerm, vars: &mut VarMap) -> String {
    match t {
        LogicalTerm::Variable(v) => vars.bind(v),
        LogicalTerm::Constant(c) => sanitize_functor(c),
        LogicalTerm::Description(d) => sanitize_functor(&format!("le_{d}")),
        // Numbers belong to the compute fragment (filtered out); render defensively.
        LogicalTerm::Number(n) => sanitize_functor(&format!("num_{n}")),
        // `zo'e` is a single RIGID unspecified referent — one shared constant, NOT an
        // existential drop-to-`$true`. That matches nibli's closed-world semantics: a role
        // asserted with a specific filler (`pilno_x2(ev, varfarin)`) does NOT satisfy a query
        // for the unspecified filler (`pilno_x2(ev, zo'e)`), so `la .adam. cu pilno` is FALSE
        // even when Adam takes warfarin. (Dropping to `$true` wrongly made it existential and
        // diverged from nibli on the gdpr/ddi slices.)
        LogicalTerm::Unspecified => "something".to_string(),
    }
}

/// Per-formula renaming of nibli variable names to fresh, valid TPTP variables
/// (`V0`, `V1`, …). Mapping by name keeps repeated references consistent and avoids
/// any collision between distinct nibli variables.
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

/// Render a relation/constant name as a TPTP functor: a bare `lower_word`
/// (`^[a-z][a-zA-Z0-9_]*$`) where possible, otherwise a single-quoted atom with `\`
/// and `'` escaped. Cmevla dots (`.adam.`) are stripped first so the same entity maps
/// to one stable functor.
fn sanitize_functor(name: &str) -> String {
    let trimmed = name.trim_matches('.');
    let s = if trimmed.is_empty() { name } else { trimmed };
    let bare = s.chars().next().is_some_and(|c| c.is_ascii_lowercase())
        && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if bare {
        s.to_string()
    } else {
        let escaped = s.replace('\\', "\\\\").replace('\'', "\\'");
        format!("'{escaped}'")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn buf(nodes: Vec<LogicNode>, roots: Vec<u32>) -> LogicBuffer {
        LogicBuffer { nodes, roots }
    }

    #[test]
    fn ground_atom() {
        let b = buf(
            vec![LogicNode::Predicate((
                "gerku".into(),
                vec![LogicalTerm::Constant("adam".into())],
            ))],
            vec![0],
        );
        let out = render_problem(&[], &b).unwrap();
        assert!(out.contains("fof(goal, conjecture, gerku(adam))."), "{out}");
    }

    #[test]
    fn unspecified_arg_is_rigid_constant() {
        // An unspecified referent is rigid, translated to the shared constant `something` —
        // NOT dropped to `$true` (which would wrongly make it existential; see render_term).
        let b = buf(
            vec![LogicNode::Predicate((
                "gerku_x2".into(),
                vec![LogicalTerm::Variable("ev".into()), LogicalTerm::Unspecified],
            ))],
            vec![0],
        );
        let out = render_problem(&[], &b).unwrap();
        assert!(
            out.contains("conjecture, gerku_x2(V0, something))."),
            "{out}"
        );
    }

    #[test]
    fn universal_implication() {
        // ! [V0] : (~ dog(V0) | animal(V0))  — the Or(Not(A),B) rule shape.
        let b = buf(
            vec![
                LogicNode::Predicate(("dog".into(), vec![LogicalTerm::Variable("x".into())])),
                LogicNode::Predicate(("animal".into(), vec![LogicalTerm::Variable("x".into())])),
                LogicNode::NotNode(0),
                LogicNode::OrNode((2, 1)),
                LogicNode::ForAllNode(("x".into(), 3)),
            ],
            vec![4],
        );
        let out = render_problem(
            &[b],
            &buf(vec![LogicNode::Predicate(("p".into(), vec![]))], vec![0]),
        )
        .unwrap();
        assert!(out.contains("! [V0] :"), "{out}");
        assert!(out.contains("~ dog(V0)"), "{out}");
        assert!(out.contains("animal(V0)"), "{out}");
    }

    #[test]
    fn cmevla_dots_stripped() {
        assert_eq!(sanitize_functor(".adam."), "adam");
        assert_eq!(sanitize_functor("gerku_x1"), "gerku_x1");
        assert_eq!(sanitize_functor("ka'e"), "'ka\\'e'");
    }

    #[test]
    fn equals_maps_to_native_equality() {
        // `la .adam. cu du la .bel.` (axiom) + `la .bel. cu du la .adam.` (conjecture):
        // both must render as TPTP `=`, never as an uninterpreted `du(...)` predicate
        // (which would lack congruence and fake a divergence).
        let du = |a: &str, b: &str| {
            buf(
                vec![LogicNode::Predicate((
                    "equals".into(),
                    vec![
                        LogicalTerm::Constant(a.into()),
                        LogicalTerm::Constant(b.into()),
                    ],
                ))],
                vec![0],
            )
        };
        let out = render_problem(&[du("adam", "bel")], &du("bel", "adam")).unwrap();
        assert!(out.contains("fof(ax_0, axiom, (adam = bel))."), "{out}");
        assert!(
            out.contains("fof(goal, conjecture, (bel = adam))."),
            "{out}"
        );
        assert!(
            !out.contains("equals("),
            "uninterpreted equality leaked: {out}"
        );
    }
}
