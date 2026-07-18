use super::*;
use crate::ir::{IrForm, IrTerm};
use nibli_types::ast::{
    Argument, Determiner, Marker, Predicate, Pronoun, Proposition, RelClause, RelClauseKind,
    Sentence,
};

/// Helper: build a minimal buffer and compile the first sentence.
/// Returns the compiled IrForm.
fn compile_one(
    predicates: Vec<Predicate>,
    arguments: Vec<Argument>,
    proposition: Proposition,
) -> (IrForm, SemanticCompiler) {
    let sentences = vec![Sentence::Simple(proposition)];
    let mut compiler = SemanticCompiler::new();
    let form = compiler.compile_proposition(
        match &sentences[0] {
            Sentence::Simple(b) => b,
            _ => unreachable!(),
        },
        &predicates,
        &arguments,
        &sentences,
    );
    (form, compiler)
}

/// Helper: resolve a string from the compiler's interner
fn resolve(compiler: &SemanticCompiler, spur: &lasso::Spur) -> String {
    compiler.interner.resolve(spur).to_string()
}

/// Helper: collect all (relation_name, args) pairs from a IrForm tree.
fn collect_predicates(form: &IrForm, compiler: &SemanticCompiler) -> Vec<(String, Vec<IrTerm>)> {
    let mut result = Vec::new();
    collect_predicates_inner(form, compiler, &mut result);
    result
}

fn collect_predicates_inner(
    form: &IrForm,
    compiler: &SemanticCompiler,
    result: &mut Vec<(String, Vec<IrTerm>)>,
) {
    match form {
        IrForm::Predicate { relation, args } => {
            result.push((resolve(compiler, relation), args.clone()));
        }
        IrForm::And(l, r) | IrForm::Or(l, r) | IrForm::Biconditional(l, r) | IrForm::Xor(l, r) => {
            collect_predicates_inner(l, compiler, result);
            collect_predicates_inner(r, compiler, result);
        }
        IrForm::Not(inner)
        | IrForm::Exists(_, inner)
        | IrForm::ForAll(_, inner)
        | IrForm::Past(inner)
        | IrForm::Present(inner)
        | IrForm::Future(inner)
        | IrForm::Obligatory(inner)
        | IrForm::Permitted(inner) => {
            collect_predicates_inner(inner, compiler, result);
        }
        IrForm::Count { body, .. } => {
            collect_predicates_inner(body, compiler, result);
        }
    }
}

/// Helper: check if form contains a predicate with given name.
fn has_pred(form: &IrForm, name: &str, compiler: &SemanticCompiler) -> bool {
    collect_predicates(form, compiler)
        .iter()
        .any(|(n, _)| n == name)
}

/// Helper: get the args of the first predicate with given name.
fn get_pred_args(form: &IrForm, name: &str, compiler: &SemanticCompiler) -> Option<Vec<IrTerm>> {
    collect_predicates(form, compiler)
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, args)| args)
}

/// Helper: extract a `Constant` term's interned string (panics otherwise).
fn const_str(compiler: &SemanticCompiler, term: &IrTerm) -> String {
    match term {
        IrTerm::Constant(c) => resolve(compiler, c),
        other => panic!("expected Constant, got {:?}", other),
    }
}

/// Helper: collect the names of all FREE `Variable` occurrences in a form
/// (binder-tracking). A closed top-level form should have NONE — any free
/// da/de/di/ma var is an under-quantification soundness bug.
fn free_vars(form: &IrForm, compiler: &SemanticCompiler) -> Vec<String> {
    let mut bound: Vec<lasso::Spur> = Vec::new();
    let mut out: Vec<String> = Vec::new();
    free_vars_inner(form, compiler, &mut bound, &mut out);
    out
}

fn free_vars_inner(
    form: &IrForm,
    compiler: &SemanticCompiler,
    bound: &mut Vec<lasso::Spur>,
    out: &mut Vec<String>,
) {
    match form {
        IrForm::Predicate { args, .. } => {
            for arg in args {
                if let IrTerm::Variable(spur) = arg {
                    if !bound.contains(spur) {
                        out.push(resolve(compiler, spur));
                    }
                }
            }
        }
        IrForm::And(l, r) | IrForm::Or(l, r) | IrForm::Biconditional(l, r) | IrForm::Xor(l, r) => {
            free_vars_inner(l, compiler, bound, out);
            free_vars_inner(r, compiler, bound, out);
        }
        IrForm::Not(inner)
        | IrForm::Past(inner)
        | IrForm::Present(inner)
        | IrForm::Future(inner)
        | IrForm::Obligatory(inner)
        | IrForm::Permitted(inner) => {
            free_vars_inner(inner, compiler, bound, out);
        }
        IrForm::Exists(v, body) | IrForm::ForAll(v, body) => {
            bound.push(*v);
            free_vars_inner(body, compiler, bound, out);
            bound.pop();
        }
        IrForm::Count { var, body, .. } => {
            bound.push(*var);
            free_vars_inner(body, compiler, bound, out);
            bound.pop();
        }
    }
}

/// Helper: count `Exists` nodes binding a variable with the given name.
/// (ForAll binders are NOT counted — a prenex-bound `da` is universal, not
/// existential.)
fn count_exists_binding(form: &IrForm, name: &str, compiler: &SemanticCompiler) -> usize {
    match form {
        IrForm::Exists(v, body) => {
            let here = usize::from(resolve(compiler, v) == name);
            here + count_exists_binding(body, name, compiler)
        }
        IrForm::ForAll(_, body) => count_exists_binding(body, name, compiler),
        IrForm::And(l, r) | IrForm::Or(l, r) | IrForm::Biconditional(l, r) | IrForm::Xor(l, r) => {
            count_exists_binding(l, name, compiler) + count_exists_binding(r, name, compiler)
        }
        IrForm::Not(inner)
        | IrForm::Past(inner)
        | IrForm::Present(inner)
        | IrForm::Future(inner)
        | IrForm::Obligatory(inner)
        | IrForm::Permitted(inner) => count_exists_binding(inner, name, compiler),
        IrForm::Count { body, .. } => count_exists_binding(body, name, compiler),
        IrForm::Predicate { .. } => 0,
    }
}

/// A quantifier binder, for asserting nesting ORDER (which `free_vars` /
/// `count_exists_binding` do not capture). `ForAll`/`Count` carry no var name
/// (description vars are fresh `_vN`); `Exists` carries the bound name so a
/// test can assert it is exactly `da`/`de`/`di`.
#[derive(Debug, PartialEq)]
enum Binder {
    Exists(String),
    ForAll,
    Count(u32),
}

/// The quantifier-binder sequence from the ROOT inward, following the single
/// body branch through transparent Not/tense/deontic wrappers and stopping at
/// the first And/Or/Predicate. Lets a test distinguish `∃da.∀x`
/// (`[Exists("$da"), ForAll]`) from `∀x.∃da` (`[ForAll]`, the `da` hidden in
/// the universal's matrix Or). Use `exists_outscopes_forall` for ∃-over-∀
/// nesting that the Or/And hides from the spine.
fn binder_spine(form: &IrForm, compiler: &SemanticCompiler) -> Vec<Binder> {
    let mut out = Vec::new();
    let mut cur = form;
    loop {
        match cur {
            IrForm::Exists(v, body) => {
                out.push(Binder::Exists(resolve(compiler, v)));
                cur = body;
            }
            IrForm::ForAll(_, body) => {
                out.push(Binder::ForAll);
                cur = body;
            }
            IrForm::Count { count, body, .. } => {
                out.push(Binder::Count(*count));
                cur = body;
            }
            IrForm::Not(inner)
            | IrForm::Past(inner)
            | IrForm::Present(inner)
            | IrForm::Future(inner)
            | IrForm::Obligatory(inner)
            | IrForm::Permitted(inner) => cur = inner,
            _ => break,
        }
    }
    out
}

/// True if a `ForAll` appears anywhere in `form`'s subtree.
fn subtree_has_forall(form: &IrForm) -> bool {
    match form {
        IrForm::ForAll(_, _) => true,
        IrForm::Exists(_, b)
        | IrForm::Not(b)
        | IrForm::Past(b)
        | IrForm::Present(b)
        | IrForm::Future(b)
        | IrForm::Obligatory(b)
        | IrForm::Permitted(b) => subtree_has_forall(b),
        IrForm::Count { body, .. } => subtree_has_forall(body),
        IrForm::And(l, r) | IrForm::Or(l, r) | IrForm::Biconditional(l, r) | IrForm::Xor(l, r) => {
            subtree_has_forall(l) || subtree_has_forall(r)
        }
        IrForm::Predicate { .. } => false,
    }
}

/// True if some `Exists` binding `name` has a `ForAll` in its subtree — i.e.
/// the existential OUTSCOPES a universal (∃-over-∀). Reaches through the
/// matrix-side Or/And that `binder_spine` stops at.
fn exists_outscopes_forall(form: &IrForm, name: &str, compiler: &SemanticCompiler) -> bool {
    match form {
        IrForm::Exists(v, body) => {
            (resolve(compiler, v) == name && subtree_has_forall(body))
                || exists_outscopes_forall(body, name, compiler)
        }
        IrForm::ForAll(_, body) => exists_outscopes_forall(body, name, compiler),
        IrForm::Count { body, .. } => exists_outscopes_forall(body, name, compiler),
        IrForm::Not(b)
        | IrForm::Past(b)
        | IrForm::Present(b)
        | IrForm::Future(b)
        | IrForm::Obligatory(b)
        | IrForm::Permitted(b) => exists_outscopes_forall(b, name, compiler),
        IrForm::And(l, r) | IrForm::Or(l, r) | IrForm::Biconditional(l, r) | IrForm::Xor(l, r) => {
            exists_outscopes_forall(l, name, compiler) || exists_outscopes_forall(r, name, compiler)
        }
        IrForm::Predicate { .. } => false,
    }
}

/// Helper: compile a full sentence (not just proposition) to test rel clause handling.
fn compile_sentence_full(
    predicates: Vec<Predicate>,
    arguments: Vec<Argument>,
    sentences: Vec<Sentence>,
) -> (IrForm, SemanticCompiler) {
    let mut compiler = SemanticCompiler::new();
    let form = compiler.compile_sentence(0, &predicates, &arguments, &sentences);
    (form, compiler)
}

// ─── Topical submodules (the shared compile/assert helpers above are
//     reachable via `use super::*;`) ────────────────────────────────────
//
// SCOPE (2026-07-18): the KR-text-expressible *shape* tests migrated to
// `nibli-kr/src/shape_tests/` (flat-vs-surface discipline). What remains here
// is exactly the set with NO KR surface: corrupt-buffer negative controls
// (`crate::ast_buffer_validation_tests`), the direct-injection API tests
// (`crate::injected_fact_tests`), the internal-static units (the
// `count_unspecified`/`inject_variable`/`fresh_var` white-box tests), and the
// defense-in-depth guards whose inputs the KR parser/emitter rejects or cannot
// spell first (over-arity/collision/overflow place tags, mandatory-`it`
// firewall, unknown-word arity, `WithArgs` at proposition level, the
// CLL place-counter, n-ary identity, arity-1 `via`).

mod abstractions;
mod injection;
mod lowering;
mod modals;
mod regressions;
mod rel_clauses;
mod scoping;
mod terms_misc;
