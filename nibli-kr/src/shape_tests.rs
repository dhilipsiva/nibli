//! KR-text-level shape regression tests — the migrated home of the semantic
//! compiler's former hand-built-`AstBuffer` shape tests (TODO item "Migrate
//! hand-built semantic-shape tests toward KR-text level").
//!
//! These drive the REAL front-end (`parse_checked` → `nibli_semantics::compile_from_ast`)
//! and assert on the public `LogicBuffer`, per the flat-vs-surface discipline
//! (CLAUDE.md): a hand-built flat buffer can drift from what the pipeline
//! actually produces, so any shape-dependent regression belongs at the surface.
//! They live in nibli-kr (not nibli-semantics) because the dependency direction
//! forbids a nibli-semantics→nibli-kr dev-dep; nibli-kr already dev-deps
//! nibli-semantics (the emit.rs goldens do the same). Structural helpers are
//! modeled on `nibli-verify/src/seam.rs`.
//!
//! ## Migration census (old nibli-semantics test → here / STAYED / FOLDED)
//!
//! MIGRATED here, by topical submodule (old test name → new spelling):
//! - events: event_decompose_basic, _all_roles_emitted (+terms_misc
//!   known_gismu_arity FOLDED), _pair_shared_event, _pair_no_intersective_fallacy,
//!   _decompose_with_quantifier, _conversion_x2 (+wrappers x2_conversion FOLDED,
//!   via `owned`)
//! - quantifiers: re_lo/no_lo/pa_lo Count trio, lo_still_exists, afterthought
//!   je/ja/jo (+terms_misc ge_gi FOLDED into `and`), da/da_de/da_da/di exists,
//!   da_with_negation, ma/two_ma/ma_in_rel_clause
//! - scoping: da_before/after_universal (+regressions da_after_universal_closes
//!   FOLDED), interleaved_count, restrictor_internal_da, prenex_da, da_repeated,
//!   equals_existential
//! - wrappers: tense past/now/future, deontic must/may, negation, something
//! - rel_clauses: incidental_consequent, restrictive_antecedent,
//!   incidental_under_exact_count, abstraction_da_single
//! - abstractions: fact/amount/concept/event, property_with_slot
//! - injection: single_predicate_injects (KR twin), the three named-arg `it`
//!   routing tests
//! - lowering: equals_flat, place_label, via_modal (from modals)
//! - terms: la_name, number, quoted, no_explicit_args, le_description,
//!   ro_le/ro_lo/pa_le/pa_lo opaque-vs-veridical
//! - regressions: place_tag_within_arity, compound_in_restrictive (KR twin),
//!   rel_clause_on_name_conjoined
//!
//! STAYED in nibli-semantics (unmigratable — the input has no KR surface, or
//! the front-end rejects/cannot spell it, or it is an internal-static unit
//! test): the 9 corrupt-buffer controls + 3 injected-fact API tests (lib.rs);
//! the internal-static units (count_unspecified ×3, inject_variable,
//! fresh_vars, inject_variable_into_and); the parse/emit-rejected-first guards
//! (slot-outside-property, via-arity-1, equals>2, place-tag-beyond-arity,
//! tag-collision, untagged-overflow ×2, unknown-gismu-arity, name-firewall,
//! mandatory-`it` firewall ×2, cll-place-counter, WithArgs-at-proposition ×2).

use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm};

/// Compile KR text through the real front-end + semantic compiler to its
/// public `LogicBuffer`, panicking with the text on any error.
pub(super) fn lb(text: &str) -> LogicBuffer {
    let ast = crate::parse_checked(text).unwrap_or_else(|e| panic!("parse {text:?}: {e}"));
    nibli_semantics::compile_from_ast(ast)
        .unwrap_or_else(|e| panic!("nibli-semantics {text:?}: {e}"))
}

/// The buffer's (first) root node.
pub(super) fn root(b: &LogicBuffer) -> &LogicNode {
    &b.nodes[b.roots[0] as usize]
}

/// The node at index `id`.
pub(super) fn node(b: &LogicBuffer, id: u32) -> &LogicNode {
    &b.nodes[id as usize]
}

/// The argument terms of the first `Predicate` with relation `rel`, if any
/// (scans the whole arena — these single-root compiles have no dead nodes).
pub(super) fn pred_args(b: &LogicBuffer, rel: &str) -> Option<Vec<LogicalTerm>> {
    b.nodes.iter().find_map(|n| match n {
        LogicNode::Predicate((r, args)) if r == rel => Some(args.clone()),
        _ => None,
    })
}

/// Whether the buffer contains a `Predicate` with relation `rel`.
pub(super) fn has_pred(b: &LogicBuffer, rel: &str) -> bool {
    pred_args(b, rel).is_some()
}

/// Whether `rel`'s 2nd argument (the role filler in a decomposed
/// `rel_xN(event, filler)` predicate) is the constant `c`.
pub(super) fn role_is_const(b: &LogicBuffer, rel: &str, c: &str) -> bool {
    matches!(
        pred_args(b, rel).as_deref(),
        Some([_, LogicalTerm::Constant(k)]) if k == c
    )
}

/// The 2nd (role-filler) argument of `rel`, if `rel` is present with ≥2 args.
pub(super) fn role_filler(b: &LogicBuffer, rel: &str) -> Option<LogicalTerm> {
    match pred_args(b, rel).as_deref() {
        Some([_, filler]) => Some(filler.clone()),
        _ => None,
    }
}

/// The child node ids of one node (NOTE: `CountNode`'s middle field is a
/// COUNT, never a node index — only its body id is a child).
fn children(n: &LogicNode) -> Vec<u32> {
    match n {
        LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => vec![],
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => vec![*l, *r],
        LogicNode::NotNode(i)
        | LogicNode::PastNode(i)
        | LogicNode::PresentNode(i)
        | LogicNode::FutureNode(i)
        | LogicNode::ObligatoryNode(i)
        | LogicNode::PermittedNode(i) => vec![*i],
        LogicNode::ExistsNode((_, b)) | LogicNode::ForAllNode((_, b)) => vec![*b],
        LogicNode::CountNode((_, _, b)) => vec![*b],
    }
}

/// Whether a `Predicate` with relation `rel` appears in the subtree rooted at
/// `id`.
pub(super) fn has_pred_from(b: &LogicBuffer, id: u32, rel: &str) -> bool {
    let n = node(b, id);
    if let LogicNode::Predicate((r, _)) = n
        && r == rel
    {
        return true;
    }
    children(n).into_iter().any(|c| has_pred_from(b, c, rel))
}

/// Whether a `ForAllNode` appears in the subtree rooted at `id`.
fn subtree_has_forall(b: &LogicBuffer, id: u32) -> bool {
    let n = node(b, id);
    if matches!(n, LogicNode::ForAllNode(_)) {
        return true;
    }
    children(n).into_iter().any(|c| subtree_has_forall(b, c))
}

/// The names of all FREE `Variable` occurrences (binder-tracking; a closed
/// top-level form has NONE — any free `$var`/witness is an under-quantification
/// bug). Deduplicated.
pub(super) fn free_vars(b: &LogicBuffer) -> Vec<String> {
    fn walk(b: &LogicBuffer, id: u32, bound: &mut Vec<String>, out: &mut Vec<String>) {
        match node(b, id) {
            LogicNode::Predicate((_, args)) | LogicNode::ComputeNode((_, args)) => {
                for a in args {
                    if let LogicalTerm::Variable(v) = a
                        && !bound.contains(v)
                    {
                        out.push(v.clone());
                    }
                }
            }
            LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
                walk(b, *l, bound, out);
                walk(b, *r, bound, out);
            }
            LogicNode::NotNode(i)
            | LogicNode::PastNode(i)
            | LogicNode::PresentNode(i)
            | LogicNode::FutureNode(i)
            | LogicNode::ObligatoryNode(i)
            | LogicNode::PermittedNode(i) => walk(b, *i, bound, out),
            LogicNode::ExistsNode((v, body)) | LogicNode::ForAllNode((v, body)) => {
                bound.push(v.clone());
                walk(b, *body, bound, out);
                bound.pop();
            }
            LogicNode::CountNode((v, _, body)) => {
                bound.push(v.clone());
                walk(b, *body, bound, out);
                bound.pop();
            }
        }
    }
    let mut out = Vec::new();
    walk(b, b.roots[0], &mut Vec::new(), &mut out);
    out.sort();
    out.dedup();
    out
}

/// The number of `ExistsNode`s binding a variable named `name`, reachable from
/// the root. (`ForAll` binders are NOT counted — a prenex-bound var is
/// universal, not existential.)
pub(super) fn count_exists_binding(b: &LogicBuffer, name: &str) -> usize {
    fn walk(b: &LogicBuffer, id: u32, name: &str) -> usize {
        let n = node(b, id);
        let here = matches!(n, LogicNode::ExistsNode((v, _)) if v == name) as usize;
        here + children(n)
            .into_iter()
            .map(|c| walk(b, c, name))
            .sum::<usize>()
    }
    walk(b, b.roots[0], name)
}

/// True if some `ExistsNode` binding `name` has a `ForAll` in its body subtree
/// — the existential OUTSCOPES a universal (∃-over-∀), reaching through the
/// matrix-side Or/And that `binder_spine` stops at.
pub(super) fn exists_outscopes_forall(b: &LogicBuffer, name: &str) -> bool {
    fn walk(b: &LogicBuffer, id: u32, name: &str) -> bool {
        let n = node(b, id);
        if let LogicNode::ExistsNode((v, body)) = n
            && v == name
            && subtree_has_forall(b, *body)
        {
            return true;
        }
        children(n).into_iter().any(|c| walk(b, c, name))
    }
    walk(b, b.roots[0], name)
}

/// A quantifier binder, for asserting nesting ORDER. `ForAll`/`Count` bodies
/// carry fresh `_vN` description vars, so only `Exists` carries its bound name
/// (so a test can assert it is exactly `$da`/`$de`/`$di`).
#[derive(Debug, PartialEq)]
pub(super) enum Binder {
    Exists(String),
    ForAll,
    Count(u32),
}

/// The quantifier-binder sequence from the ROOT inward, following the single
/// body branch through transparent Not/tense/deontic wrappers and stopping at
/// the first And/Or/Predicate. Distinguishes `∃da.∀x` (`[Exists("$da"),
/// ForAll]`) from `∀x.∃da` (`[ForAll]`, the `da` hidden in the universal's
/// matrix Or — use `exists_outscopes_forall` for that).
pub(super) fn binder_spine(b: &LogicBuffer) -> Vec<Binder> {
    let mut out = Vec::new();
    let mut cur = b.roots[0];
    loop {
        match node(b, cur) {
            LogicNode::ExistsNode((v, body)) => {
                out.push(Binder::Exists(v.clone()));
                cur = *body;
            }
            LogicNode::ForAllNode((_, body)) => {
                out.push(Binder::ForAll);
                cur = *body;
            }
            LogicNode::CountNode((_, n, body)) => {
                out.push(Binder::Count(*n));
                cur = *body;
            }
            LogicNode::NotNode(i)
            | LogicNode::PastNode(i)
            | LogicNode::PresentNode(i)
            | LogicNode::FutureNode(i)
            | LogicNode::ObligatoryNode(i)
            | LogicNode::PermittedNode(i) => cur = *i,
            _ => break,
        }
    }
    out
}

/// For a universally-quantified form `∀x. P → Q`, flattened to
/// `ForAll(_, Or(Not(antecedent), consequent))`, return `(antecedent_id,
/// consequent_id)`. Panics if the root is not that shape.
pub(super) fn forall_or_split(b: &LogicBuffer) -> (u32, u32) {
    let body = match root(b) {
        LogicNode::ForAllNode((_, body)) => *body,
        other => panic!("root is not ForAll: {other:?}"),
    };
    let (l, r) = match node(b, body) {
        LogicNode::OrNode((l, r)) => (*l, *r),
        other => panic!("ForAll body is not Or: {other:?}"),
    };
    let antecedent = match node(b, l) {
        LogicNode::NotNode(p) => *p,
        _ => l,
    };
    (antecedent, r)
}

mod abstractions;
mod events;
mod injection;
mod lowering;
mod mutation_audit;
mod quantifiers;
mod regressions;
mod rel_clauses;
mod scoping;
mod terms;
mod wrappers;
