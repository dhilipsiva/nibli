//! Bridge conversions: smuni WIT logic types → logji WIT logic types.
//!
//! These types are structurally identical (generated from the same WIT `logic-types`
//! interface) but are different Rust types because each crate generates its own bindings.

use crate::bindings::lojban::nibli::logic_types as logji_logic;
use smuni::bindings::lojban::nibli::logic_types as smuni_logic;
use std::collections::HashSet;

fn convert_logical_term(t: &smuni_logic::LogicalTerm) -> logji_logic::LogicalTerm {
    match t {
        smuni_logic::LogicalTerm::Variable(v) => logji_logic::LogicalTerm::Variable(v.clone()),
        smuni_logic::LogicalTerm::Constant(c) => logji_logic::LogicalTerm::Constant(c.clone()),
        smuni_logic::LogicalTerm::Description(d) => {
            logji_logic::LogicalTerm::Description(d.clone())
        }
        smuni_logic::LogicalTerm::Unspecified => logji_logic::LogicalTerm::Unspecified,
        smuni_logic::LogicalTerm::Number(n) => logji_logic::LogicalTerm::Number(*n),
    }
}

fn convert_logic_node(
    n: &smuni_logic::LogicNode,
    compute_preds: &HashSet<String>,
) -> logji_logic::LogicNode {
    match n {
        smuni_logic::LogicNode::Predicate((rel, args))
            if compute_preds.contains(rel.as_str()) =>
        {
            logji_logic::LogicNode::ComputeNode((
                rel.clone(),
                args.iter().map(convert_logical_term).collect(),
            ))
        }
        smuni_logic::LogicNode::Predicate((rel, args)) => logji_logic::LogicNode::Predicate((
            rel.clone(),
            args.iter().map(convert_logical_term).collect(),
        )),
        smuni_logic::LogicNode::ComputeNode((rel, args)) => {
            logji_logic::LogicNode::ComputeNode((
                rel.clone(),
                args.iter().map(convert_logical_term).collect(),
            ))
        }
        smuni_logic::LogicNode::AndNode((l, r)) => logji_logic::LogicNode::AndNode((*l, *r)),
        smuni_logic::LogicNode::OrNode((l, r)) => logji_logic::LogicNode::OrNode((*l, *r)),
        smuni_logic::LogicNode::NotNode(id) => logji_logic::LogicNode::NotNode(*id),
        smuni_logic::LogicNode::ExistsNode((v, b)) => {
            logji_logic::LogicNode::ExistsNode((v.clone(), *b))
        }
        smuni_logic::LogicNode::ForAllNode((v, b)) => {
            logji_logic::LogicNode::ForAllNode((v.clone(), *b))
        }
        smuni_logic::LogicNode::PastNode(id) => logji_logic::LogicNode::PastNode(*id),
        smuni_logic::LogicNode::PresentNode(id) => logji_logic::LogicNode::PresentNode(*id),
        smuni_logic::LogicNode::FutureNode(id) => logji_logic::LogicNode::FutureNode(*id),
        smuni_logic::LogicNode::ObligatoryNode(id) => {
            logji_logic::LogicNode::ObligatoryNode(*id)
        }
        smuni_logic::LogicNode::PermittedNode(id) => logji_logic::LogicNode::PermittedNode(*id),
        smuni_logic::LogicNode::CountNode((v, c, b)) => {
            logji_logic::LogicNode::CountNode((v.clone(), *c, *b))
        }
    }
}

/// Convert a smuni LogicBuffer to a logji LogicBuffer, applying compute predicate
/// transformation during conversion (Predicate → ComputeNode for registered predicates).
pub fn convert_logic_buffer(
    buf: &smuni_logic::LogicBuffer,
    compute_preds: &HashSet<String>,
) -> logji_logic::LogicBuffer {
    logji_logic::LogicBuffer {
        nodes: buf
            .nodes
            .iter()
            .map(|n| convert_logic_node(n, compute_preds))
            .collect(),
        roots: buf.roots.clone(),
    }
}
