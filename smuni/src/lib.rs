//! Smuni (meaning/semantics): flat AST buffer → FOL logic buffer. An internal
//! Rust pipeline stage of the single `lasna` WASM component (NOT a standalone
//! WIT component). Compiles the gerna's
//! flat AST buffer into a flat First-Order Logic buffer via the [`SemanticCompiler`],
//! then flattens the tree-structured [`LogicalForm`] IR into the WIT-compatible
//! index-based [`LogicBuffer`].
//!
//! The flattener expands `Biconditional` and `Xor` IR nodes into primitive
//! `And`/`Or`/`Not` nodes (sharing sub-tree indices for zero-cost duplication).

/// Compile-time PHF dictionary for gismu/lujvo arity lookup.
pub mod dictionary;
/// First-Order Logic IR types (`LogicalTerm`, `LogicalForm`).
pub mod ir;
/// Semantic compiler: AST → FOL logic form tree.
pub mod semantic;

use ir::{LogicalForm, LogicalTerm};
use nibli_types::ast as gerna_ast;
use nibli_types::error::NibliError;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm as WitTerm};
use semantic::SemanticCompiler;

/// Core compilation: gerna AST buffer → FOL logic buffer.
/// Used by both the native API and the WIT export path.
fn compile_ast(ast: &gerna_ast::AstBuffer) -> Result<LogicBuffer, NibliError> {
    let mut compiler = SemanticCompiler::new();
    let mut logic_forms = Vec::with_capacity(ast.roots.len());

    // Only compile top-level (root) sentences.
    // Rel clause bodies live in ast.sentences but are referenced
    // by index from Sumti::Restricted — they are NOT roots.
    for &root_idx in ast.roots.iter() {
        logic_forms.push(compiler.compile_sentence(
            root_idx,
            &ast.selbris,
            &ast.sumtis,
            &ast.sentences,
        ));
    }

    // Check for semantic errors accumulated during compilation.
    if let Some(err) = compiler.errors.first() {
        return Err(NibliError::Semantic(err.clone()));
    }

    let mut nodes = Vec::new();
    let mut roots = Vec::with_capacity(logic_forms.len());

    for form in logic_forms {
        let root_id = flatten_form(&form, &mut nodes, &compiler.interner);
        roots.push(root_id);
    }

    Ok(LogicBuffer { nodes, roots })
}

/// Recursively flatten a [`LogicalForm`] tree into the flat `nodes` array.
///
/// Returns the index of the root node in the array. String interning keys
/// are resolved to `String` at this boundary for WIT serialization.
/// `Biconditional` and `Xor` are expanded into primitive `And`/`Or`/`Not`.
fn flatten_form(form: &LogicalForm, nodes: &mut Vec<LogicNode>, interner: &lasso::Rodeo) -> u32 {
    match form {
        LogicalForm::Predicate { relation, args } => {
            let wit_args = args
                .iter()
                .map(|a| match a {
                    LogicalTerm::Variable(v) => WitTerm::Variable(interner.resolve(v).to_string()),
                    LogicalTerm::Constant(c) => WitTerm::Constant(interner.resolve(c).to_string()),
                    LogicalTerm::Description(d) => {
                        WitTerm::Description(interner.resolve(d).to_string())
                    }
                    LogicalTerm::Unspecified => WitTerm::Unspecified,
                    LogicalTerm::Number(n) => WitTerm::Number(*n),
                })
                .collect();

            let id = nodes.len() as u32;
            nodes.push(LogicNode::Predicate((
                interner.resolve(relation).to_string(),
                wit_args,
            )));
            id
        }
        LogicalForm::And(left, right) => {
            let l_id = flatten_form(left, nodes, interner);
            let r_id = flatten_form(right, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::AndNode((l_id, r_id)));
            id
        }
        LogicalForm::Or(left, right) => {
            let l_id = flatten_form(left, nodes, interner);
            let r_id = flatten_form(right, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::OrNode((l_id, r_id)));
            id
        }
        LogicalForm::Not(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::NotNode(inner_id));
            id
        }
        LogicalForm::Exists(v, body) => {
            let b_id = flatten_form(body, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::ExistsNode((
                interner.resolve(v).to_string(),
                b_id,
            )));
            id
        }
        LogicalForm::ForAll(v, body) => {
            let b_id = flatten_form(body, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::ForAllNode((
                interner.resolve(v).to_string(),
                b_id,
            )));
            id
        }
        LogicalForm::Past(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::PastNode(inner_id));
            id
        }
        LogicalForm::Present(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::PresentNode(inner_id));
            id
        }
        LogicalForm::Future(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::FutureNode(inner_id));
            id
        }
        LogicalForm::Obligatory(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::ObligatoryNode(inner_id));
            id
        }
        LogicalForm::Permitted(inner) => {
            let inner_id = flatten_form(inner, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::PermittedNode(inner_id));
            id
        }
        LogicalForm::Count { var, count, body } => {
            let b_id = flatten_form(body, nodes, interner);
            let id = nodes.len() as u32;
            nodes.push(LogicNode::CountNode((
                interner.resolve(var).to_string(),
                *count,
                b_id,
            )));
            id
        }
        LogicalForm::Biconditional(left, right) => {
            // Expand A ↔ B to (¬A ∨ B) ∧ (¬B ∨ A) using shared sub-tree indices
            let l_id = flatten_form(left, nodes, interner);
            let r_id = flatten_form(right, nodes, interner);
            let not_l = nodes.len() as u32;
            nodes.push(LogicNode::NotNode(l_id));
            let not_r = nodes.len() as u32;
            nodes.push(LogicNode::NotNode(r_id));
            let impl1 = nodes.len() as u32;
            nodes.push(LogicNode::OrNode((not_l, r_id)));
            let impl2 = nodes.len() as u32;
            nodes.push(LogicNode::OrNode((not_r, l_id)));
            let id = nodes.len() as u32;
            nodes.push(LogicNode::AndNode((impl1, impl2)));
            id
        }
        LogicalForm::Xor(left, right) => {
            // Expand A ⊕ B to (A ∨ B) ∧ ¬(A ∧ B) using shared sub-tree indices
            let l_id = flatten_form(left, nodes, interner);
            let r_id = flatten_form(right, nodes, interner);
            let or_id = nodes.len() as u32;
            nodes.push(LogicNode::OrNode((l_id, r_id)));
            let and_id = nodes.len() as u32;
            nodes.push(LogicNode::AndNode((l_id, r_id)));
            let not_and = nodes.len() as u32;
            nodes.push(LogicNode::NotNode(and_id));
            let id = nodes.len() as u32;
            nodes.push(LogicNode::AndNode((or_id, not_and)));
            id
        }
    }
}

/// Compile a gerna-produced AST buffer into a logic buffer.
/// Primary API for all callers (lasna, nibli-engine).
pub fn compile_from_gerna_ast(ast: gerna_ast::AstBuffer) -> Result<LogicBuffer, NibliError> {
    compile_ast(&ast)
}

/// Compile a directly-injected ground fact `(relation, args)` into the SAME
/// event-decomposed, arity-padded FOL shape that a surface assertion of
/// `relation` produces — so injected facts are matched by surface text queries
/// (`la .adam. cu gerku` matches `:assert gerku adam`), not just by raw-FOL or
/// same-shape direct facts.
///
/// Used by the trusted programmatic injection APIs (nibli-engine
/// `assert_fact_direct`, lasna's WIT `assert-fact`, the REPL `:assert`). Mirrors
/// `apply_selbri`'s `Selbri::Root` arm exactly so the stored shape is identical
/// to text assertion: `fit_args` pads to `get_arity_or_default`, then
/// `event_decompose`. `du` is the one exception — it stays a FLAT 2-arg
/// `du(x1, x2)` predicate (NOT event-decomposed), because logji's union-find
/// equality interception only fires on `relation == "du" && args.len() == 2`;
/// the Neo-Davidsonian form would silently disable equality reasoning.
pub fn compile_injected_fact(relation: &str, args: &[WitTerm]) -> LogicBuffer {
    let mut compiler = SemanticCompiler::new();
    let ir_args: Vec<LogicalTerm> = args
        .iter()
        .map(|t| wit_term_to_ir(t, &mut compiler.interner))
        .collect();

    let form = if relation == "du" {
        let fitted = SemanticCompiler::fit_args(&ir_args, 2);
        LogicalForm::Predicate {
            relation: compiler.interner.get_or_intern("du"),
            args: fitted,
        }
    } else {
        let arity = crate::dictionary::JbovlasteSchema::get_arity_or_default(relation);
        let fitted = SemanticCompiler::fit_args(&ir_args, arity);
        compiler.event_decompose(relation, &fitted)
    };

    let mut nodes = Vec::new();
    let root = flatten_form(&form, &mut nodes, &compiler.interner);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

/// Convert a flat WIT/IR `LogicalTerm` to the interned smuni IR `LogicalTerm`
/// (the inverse of `flatten_form`'s Predicate arm).
fn wit_term_to_ir(term: &WitTerm, interner: &mut lasso::Rodeo) -> LogicalTerm {
    match term {
        WitTerm::Variable(v) => LogicalTerm::Variable(interner.get_or_intern(v)),
        WitTerm::Constant(c) => LogicalTerm::Constant(interner.get_or_intern(c)),
        WitTerm::Description(d) => LogicalTerm::Description(interner.get_or_intern(d)),
        WitTerm::Unspecified => LogicalTerm::Unspecified,
        WitTerm::Number(n) => LogicalTerm::Number(*n),
    }
}
