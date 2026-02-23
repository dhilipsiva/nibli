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
    fn compile_buffer(ast: AstBuffer) -> Result<LogicBuffer, String> {
        let mut compiler = SemanticCompiler::new();
        let mut logic_forms = Vec::with_capacity(ast.roots.len());

        // Only compile top-level (root) sentences.
        // Rel clause bodies live in ast.sentences but are referenced
        // by index from Sumti::Restricted — they are NOT roots.
        for &root_idx in ast.roots.iter() {
            let sentence = &ast.sentences[root_idx as usize];
            logic_forms.push(compiler.compile_bridi(
                sentence,
                &ast.selbris,
                &ast.sumtis,
                &ast.sentences,
            ));
        }

        let mut nodes = Vec::new();
        let mut roots = Vec::with_capacity(logic_forms.len());

        for form in logic_forms {
            let root_id = flatten_form(&form, &mut nodes, &compiler.interner);
            roots.push(root_id);
        }

        Ok(LogicBuffer { nodes, roots })
    }
}

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
    }
}

bindings::export!(SemanticsComponent with_types_in bindings);
