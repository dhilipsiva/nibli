#[allow(warnings)]
pub mod bindings;
pub mod dictionary;
pub mod ir;
pub mod semantic;

use bindings::exports::lojban::nesy::semantics::Guest;
use bindings::lojban::nesy::ast_types::{
    AstBuffer, LogicBuffer, LogicNode, LogicalTerm as WitTerm,
};
use ir::{LogicalForm, LogicalTerm};
use semantic::SemanticCompiler;

struct SemanticsComponent;

impl Guest for SemanticsComponent {
    /// Consumes the Canonical ABI AST buffer and returns a zero-copy logic arena buffer.
    fn compile_buffer(ast: AstBuffer) -> Result<LogicBuffer, String> {
        let mut compiler = SemanticCompiler::new();
        let mut logic_forms = Vec::with_capacity(ast.sentences.len());

        for sentence in ast.sentences {
            logic_forms.push(compiler.compile_bridi(&sentence, &ast.selbris, &ast.sumtis));
        }

        // Flatten the logical trees into a flat, integer-indexed arena buffer
        let mut nodes = Vec::new();
        let mut roots = Vec::with_capacity(logic_forms.len());

        for form in logic_forms {
            let root_id = flatten_form(&form, &mut nodes, &compiler.interner);
            roots.push(root_id);
        }

        Ok(LogicBuffer { nodes, roots })
    }
}

/// Recursively flattens the nested LogicalForm into the flat WIT LogicBuffer
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
    }
}

bindings::export!(SemanticsComponent with_types_in bindings);
