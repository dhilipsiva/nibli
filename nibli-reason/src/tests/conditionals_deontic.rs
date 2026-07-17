use super::*;

// ── Material conditional / modus ponens tests ──

/// Helper: build "ganai la .X. P gi la .X. Q" as Or(Not(Pred(P, [X])), Pred(Q, [X]))
/// This is the logic IR that sentence connective `ganai...gi` produces.
fn make_material_conditional(entity: &str, antecedent: &str, consequent: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let ante = pred(
        &mut nodes,
        antecedent,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let cons = pred(
        &mut nodes,
        consequent,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let neg_ante = not(&mut nodes, ante);
    let root = or(&mut nodes, neg_ante, cons);
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_material_conditional_modus_ponens() {
    // ganai la .sol. barda gi la .sol. tsali
    // + la .sol. barda
    // → la .sol. tsali should be TRUE via modus ponens
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "barda"));
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert!(query(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_modus_ponens_reversed_order() {
    // Assert the conditional FIRST, then the antecedent
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert_buf(&kb, make_assertion("sol", "barda"));
    assert!(query(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_modus_tollens() {
    // ganai la .sol. barda gi la .sol. tsali
    // + la .sol. na tsali (Not tsali)
    // → la .sol. na barda (Not barda) via modus tollens
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));

    // Assert Not(tsali(sol))
    let mut neg_nodes = Vec::new();
    let inner = pred(
        &mut neg_nodes,
        "tsali",
        vec![
            LogicalTerm::Constant("sol".to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = not(&mut neg_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: neg_nodes,
            roots: vec![root],
        },
    );

    // Query: barda(sol) should be FALSE (modus tollens derives Not(barda(sol)))
    assert!(query_false(&kb, make_query("sol", "barda")));
}

#[test]
fn test_material_conditional_antecedent_not_satisfied() {
    // ganai la .sol. barda gi la .sol. tsali
    // (no barda assertion)
    // → la .sol. tsali should be FALSE (antecedent not satisfied)
    let kb = new_kb();
    assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
    assert!(query_false(&kb, make_query("sol", "tsali")));
}

#[test]
fn test_material_conditional_chain() {
    // ganai A gi B, ganai B gi C, assert A → derive C
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "tarci"));
    assert_buf(&kb, make_material_conditional("sol", "tarci", "gusni"));
    assert_buf(&kb, make_material_conditional("sol", "gusni", "melbi"));
    assert!(query(&kb, make_query("sol", "melbi")));
}

// ── Deontic predicate tests ──

/// Helper: build a 3-place deontic assertion: Pred(rel, [Const(entity), Const(action), Zoe])
fn make_deontic_assertion(entity: &str, relation: &str, action: &str) -> LogicBuffer {
    let mut nodes = Vec::new();
    let root = pred(
        &mut nodes,
        relation,
        vec![
            LogicalTerm::Constant(entity.to_string()),
            LogicalTerm::Constant(action.to_string()),
            LogicalTerm::Unspecified,
        ],
    );
    LogicBuffer {
        nodes,
        roots: vec![root],
    }
}

#[test]
fn test_deontic_obliged_assert_query() {
    // bilga(alis, klama, Zoe) — Alice is obligated to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "bilga", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "bilga", "klama")));
    assert!(query_false(
        &kb,
        make_deontic_assertion("bob", "bilga", "klama")
    ));
}

#[test]
fn test_deontic_permits_assert_query() {
    // curmi(alis, klama, Zoe) — Alice is permitted to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "curmi", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "curmi", "klama")));
    assert!(query_false(
        &kb,
        make_deontic_assertion("alis", "curmi", "tavla")
    ));
}

#[test]
fn test_deontic_needs_assert_query() {
    // nitcu(alis, klama, Zoe) — Alice needs to go
    let kb = new_kb();
    assert_buf(&kb, make_deontic_assertion("alis", "nitcu", "klama"));
    assert!(query(&kb, make_deontic_assertion("alis", "nitcu", "klama")));
    assert!(query_false(
        &kb,
        make_deontic_assertion("alis", "nitcu", "tavla")
    ));
}

#[test]
fn test_deontic_universal_obligation() {
    // ∀x. prenu(x) → bilga(x, Zoe, Zoe) — all people are obligated
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "prenu"));
    assert_buf(&kb, make_universal("prenu", "bilga"));
    assert!(query(&kb, make_query("alis", "bilga")));
    assert!(query_false(&kb, make_query("bob", "bilga")));
}

#[test]
fn test_deontic_conditional_chain() {
    // ganai bilga(sol) gi nitcu(sol) — if obligated then needed
    // + bilga(sol) → nitcu(sol) via modus ponens
    let kb = new_kb();
    assert_buf(&kb, make_assertion("sol", "bilga"));
    assert_buf(&kb, make_material_conditional("sol", "bilga", "nitcu"));
    assert!(query(&kb, make_query("sol", "nitcu")));
}

// ── Deontic deontic tests ──

/// Helper: build a PermittedNode wrapping the given node.
fn permitted(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
    let id = nodes.len() as u32;
    nodes.push(LogicNode::PermittedNode(inner));
    id
}

#[test]
fn test_obligatory_assert_query() {
    // Assert Obligatory(klama(alis, zo'e)) then query exact → TRUE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = obligatory(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = obligatory(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_permitted_assert_query() {
    // Assert Permitted(klama(alis, zo'e)) then query exact → TRUE
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = permitted(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = permitted(&mut q_nodes, q_inner);
    assert!(query(
        &kb,
        LogicBuffer {
            nodes: q_nodes,
            roots: vec![q_root]
        }
    ));
}

#[test]
fn test_obligatory_distinct_from_bare() {
    // `Obligatory(klama(alis))` is "ought", NOT "is": a bare actuality query must NOT
    // match a stored obligation, while the obligation stays queryable with its wrapper.
    // Deriving "is" from "ought" is an over-claim. (Replaces the former
    // `test_obligatory_transparent`, which enshrined the now-fixed collapse.)
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = obligatory(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );

    // Bare actuality query must NOT match the stored obligation.
    assert!(
        query_false(&kb, make_query("alis", "klama")),
        "ought must not imply is"
    );

    // The obligation itself is still queryable with the wrapper.
    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = obligatory(&mut q_nodes, q_inner);
    assert!(
        query(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root]
            }
        ),
        "the obligation itself is preserved"
    );
}

#[test]
fn test_bare_does_not_imply_obligation() {
    // The converse direction: a bare fact ("is") must NOT satisfy a deontic query
    // ("ought").
    let kb = new_kb();
    assert_buf(&kb, make_assertion("alis", "klama"));
    let mut q_nodes = Vec::new();
    let q_inner = pred(
        &mut q_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let q_root = obligatory(&mut q_nodes, q_inner);
    assert!(
        query_false(
            &kb,
            LogicBuffer {
                nodes: q_nodes,
                roots: vec![q_root]
            }
        ),
        "is must not imply ought"
    );
}

#[test]
fn test_permitted_distinct_from_bare() {
    // `e'e` analog: a permission is not an actuality.
    let kb = new_kb();
    let mut a_nodes = Vec::new();
    let inner = pred(
        &mut a_nodes,
        "klama",
        vec![
            LogicalTerm::Constant("alis".into()),
            LogicalTerm::Unspecified,
        ],
    );
    let root = permitted(&mut a_nodes, inner);
    assert_buf(
        &kb,
        LogicBuffer {
            nodes: a_nodes,
            roots: vec![root],
        },
    );
    assert!(
        query_false(&kb, make_query("alis", "klama")),
        "permitted must not imply is"
    );
}
