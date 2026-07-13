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
use nibli_types::ast as flat_ast;
use nibli_types::error::NibliError;
use nibli_types::logic::{LogicBuffer, LogicNode, LogicalTerm as WitTerm};
use semantic::SemanticCompiler;

/// Structural validation of an [`flat_ast::AstBuffer`] at the PUBLIC compile
/// boundary — a MECHANISM, not call-site discipline (the same pattern as the
/// assert-boundary groundness drop): every index reachable from `roots` must be
/// in bounds, and reference chains must be acyclic. The recursive compiler
/// would otherwise PANIC on an out-of-bounds index or overflow the stack on a
/// reference cycle — both crash classes for a hand-built/corrupt buffer (the
/// gerna flattener produces valid buffers by construction; this guards the
/// programmatic path). Sharing (a DAG) is legal — only true cycles reject.
/// Iterative DFS, so an adversarially deep buffer cannot overflow the
/// validator itself.
fn validate_ast_buffer(ast: &flat_ast::AstBuffer) -> Result<(), NibliError> {
    use flat_ast::{Argument, ModalTag, Predicate, Sentence};

    #[derive(Clone, Copy, PartialEq)]
    enum Kind {
        Sel,
        Sum,
        Sen,
    }
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        White,
        Grey,
        Black,
    }
    let err = |kind: &str, idx: u32, len: usize| {
        NibliError::Semantic(format!(
            "corrupt AST buffer: {kind} index {idx} out of bounds (len {len}) — \
             rejecting the whole buffer (fail closed)"
        ))
    };
    let cycle_err = |kind: &str, idx: u32| {
        NibliError::Semantic(format!(
            "corrupt AST buffer: {kind} index {idx} participates in a reference \
             cycle — rejecting the whole buffer (fail closed)"
        ))
    };

    // Child references of one node: (kind, index) pairs.
    let children = |kind: Kind, idx: u32| -> Vec<(Kind, u32)> {
        match kind {
            Kind::Sel => match &ast.selbris[idx as usize] {
                Predicate::Root(_) | Predicate::Compound(_) => vec![],
                Predicate::Tanru((m, h)) => vec![(Kind::Sel, *m), (Kind::Sel, *h)],
                Predicate::Converted((_, i)) | Predicate::Negated(i) | Predicate::Grouped(i) => {
                    vec![(Kind::Sel, *i)]
                }
                Predicate::WithArgs((core, args)) => {
                    let mut v = vec![(Kind::Sel, *core)];
                    v.extend(args.iter().map(|a| (Kind::Sum, *a)));
                    v
                }
                Predicate::Abstraction((_, s)) => vec![(Kind::Sen, *s)],
            },
            Kind::Sum => match &ast.sumtis[idx as usize] {
                Argument::Pronoun(_)
                | Argument::Name(_)
                | Argument::QuotedLiteral(_)
                | Argument::Unspecified
                | Argument::Number(_) => vec![],
                Argument::Description((_, s)) | Argument::QuantifiedDescription((_, _, s)) => {
                    vec![(Kind::Sel, *s)]
                }
                Argument::Tagged((_, i)) => vec![(Kind::Sum, *i)],
                Argument::ModalTagged((modal, i)) => {
                    let mut v = vec![(Kind::Sum, *i)];
                    let ModalTag::Custom(s) = modal;
                    v.push((Kind::Sel, *s));
                    v
                }
                Argument::Restricted((i, clause)) => {
                    vec![(Kind::Sum, *i), (Kind::Sen, clause.body_sentence)]
                }
            },
            Kind::Sen => match &ast.sentences[idx as usize] {
                Sentence::Simple(b) => {
                    let mut v = vec![(Kind::Sel, b.relation)];
                    v.extend(b.head_terms.iter().map(|t| (Kind::Sum, *t)));
                    v.extend(b.tail_terms.iter().map(|t| (Kind::Sum, *t)));
                    v
                }
                Sentence::Connected((_, l, r)) => vec![(Kind::Sen, *l), (Kind::Sen, *r)],
                Sentence::Prenex((_, body)) => vec![(Kind::Sen, *body)],
            },
        }
    };
    let meta = |kind: Kind| -> (&'static str, usize) {
        match kind {
            Kind::Sel => ("selbri", ast.selbris.len()),
            Kind::Sum => ("sumti", ast.sumtis.len()),
            Kind::Sen => ("sentence", ast.sentences.len()),
        }
    };

    let mut states = [
        vec![State::White; ast.selbris.len()],
        vec![State::White; ast.sumtis.len()],
        vec![State::White; ast.sentences.len()],
    ];
    let slot = |k: Kind| match k {
        Kind::Sel => 0usize,
        Kind::Sum => 1,
        Kind::Sen => 2,
    };

    // Explicit-stack DFS with enter/exit markers (three-color cycle detection).
    let mut stack: Vec<(Kind, u32, bool)> = Vec::new();
    for &root in &ast.roots {
        if root as usize >= ast.sentences.len() {
            return Err(err("root sentence", root, ast.sentences.len()));
        }
        stack.push((Kind::Sen, root, false));
        while let Some((k, i, exited)) = stack.pop() {
            if exited {
                states[slot(k)][i as usize] = State::Black;
                continue;
            }
            match states[slot(k)][i as usize] {
                State::Black => continue,
                // Re-entered while still in progress: only a descendant of the
                // node itself can pop its Enter marker before its Exit marker.
                State::Grey => return Err(cycle_err(meta(k).0, i)),
                State::White => {}
            }
            states[slot(k)][i as usize] = State::Grey;
            stack.push((k, i, true));
            for (ck, ci) in children(k, i) {
                let (name, len) = meta(ck);
                if ci as usize >= len {
                    return Err(err(name, ci, len));
                }
                match states[slot(ck)][ci as usize] {
                    State::Grey => return Err(cycle_err(name, ci)),
                    State::Black => {}
                    State::White => stack.push((ck, ci, false)),
                }
            }
        }
    }
    Ok(())
}

/// Core compilation: gerna AST buffer → FOL logic buffer.
/// Used by both the native API and the WIT export path.
fn compile_ast(ast: &flat_ast::AstBuffer) -> Result<LogicBuffer, NibliError> {
    validate_ast_buffer(ast)?;
    let mut compiler = SemanticCompiler::new();
    let mut logic_forms = Vec::with_capacity(ast.roots.len());

    // Only compile top-level (root) sentences.
    // Rel clause bodies live in ast.sentences but are referenced
    // by index from Argument::Restricted — they are NOT roots.
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
pub fn compile_from_ast(ast: flat_ast::AstBuffer) -> Result<LogicBuffer, NibliError> {
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
/// `apply_predicate`'s `Predicate::Root` arm exactly so the stored shape is identical
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
        let arity = crate::dictionary::LexiconSchema::get_arity_or_default(relation);
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

#[cfg(test)]
mod ast_buffer_validation_tests {
    //! Negative controls for the compile-boundary AST validation: a hand-built
    //! corrupt buffer must be REJECTED with a Semantic error — never a slice
    //! panic (out-of-bounds index) or a stack overflow (reference cycle).
    use super::compile_from_ast;
    use nibli_types::ast::*;

    fn bare_proposition(relation: u32, head: Vec<u32>) -> Sentence {
        Sentence::Simple(Proposition {
            relation,
            head_terms: head,
            tail_terms: vec![],
            negated: false,
            tense: None,
            deontic: None,
        })
    }

    fn expect_corrupt(ast: AstBuffer, what: &str) {
        match compile_from_ast(ast) {
            Err(nibli_types::error::NibliError::Semantic(msg)) => assert!(
                msg.contains("corrupt AST buffer"),
                "{what}: expected the corrupt-buffer rejection, got: {msg}"
            ),
            other => panic!("{what}: expected Err(Semantic(corrupt ...)), got {other:?}"),
        }
    }

    #[test]
    fn oob_root_sentence_rejected() {
        expect_corrupt(
            AstBuffer {
                selbris: vec![],
                sumtis: vec![],
                sentences: vec![],
                roots: vec![0],
            },
            "root index into empty sentences",
        );
    }

    #[test]
    fn oob_bridi_relation_rejected() {
        expect_corrupt(
            AstBuffer {
                selbris: vec![],
                sumtis: vec![],
                sentences: vec![bare_proposition(7, vec![])],
                roots: vec![0],
            },
            "bridi relation selbri index",
        );
    }

    #[test]
    fn oob_bridi_term_rejected() {
        expect_corrupt(
            AstBuffer {
                selbris: vec![Predicate::Root("gerku".to_string())],
                sumtis: vec![],
                sentences: vec![bare_proposition(0, vec![3])],
                roots: vec![0],
            },
            "bridi head term sumti index",
        );
    }

    #[test]
    fn oob_nested_tanru_arm_rejected() {
        expect_corrupt(
            AstBuffer {
                selbris: vec![
                    Predicate::Tanru((1, 99)),
                    Predicate::Root("sutra".to_string()),
                ],
                sumtis: vec![],
                sentences: vec![bare_proposition(0, vec![])],
                roots: vec![0],
            },
            "tanru head selbri index",
        );
    }

    #[test]
    fn oob_rel_clause_sentence_rejected() {
        expect_corrupt(
            AstBuffer {
                selbris: vec![Predicate::Root("gerku".to_string())],
                sumtis: vec![
                    Argument::Name("adam".to_string()),
                    Argument::Restricted((
                        0,
                        RelClause {
                            kind: RelClauseKind::Poi,
                            body_sentence: 42,
                        },
                    )),
                ],
                sentences: vec![bare_proposition(0, vec![1])],
                roots: vec![0],
            },
            "relative-clause body sentence index",
        );
    }

    #[test]
    fn sentence_self_cycle_rejected() {
        // Prenex whose body is ITSELF: the recursive compiler would overflow
        // the stack — same crash class as an OOB panic, same rejection.
        expect_corrupt(
            AstBuffer {
                selbris: vec![],
                sumtis: vec![],
                sentences: vec![Sentence::Prenex((vec!["da".to_string()], 0))],
                roots: vec![0],
            },
            "prenex self-cycle",
        );
    }

    #[test]
    fn cross_array_cycle_rejected() {
        // selbri 0 = Abstraction -> sentence 0, whose bridi relation = selbri 0.
        expect_corrupt(
            AstBuffer {
                selbris: vec![Predicate::Abstraction((AbstractionKind::Nu, 0))],
                sumtis: vec![],
                sentences: vec![bare_proposition(0, vec![])],
                roots: vec![0],
            },
            "abstraction/bridi cross-array cycle",
        );
    }

    #[test]
    fn shared_subterm_dag_still_compiles() {
        // Sharing is NOT a cycle: the same sumti referenced twice must compile.
        let ast = AstBuffer {
            selbris: vec![Predicate::Root("batci".to_string())],
            sumtis: vec![Argument::Name("adam".to_string())],
            sentences: vec![bare_proposition(0, vec![0, 0])],
            roots: vec![0],
        };
        compile_from_ast(ast).expect("a shared (DAG) subterm is legal");
    }
}
