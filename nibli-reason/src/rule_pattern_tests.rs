// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

#[test]
fn local_pattern_binding_matches_clone_and_insert_without_leaking() {
    for base in [
        HashMap::new(),
        HashMap::from([
            ("x".into(), "outer".into()),
            ("ev".into(), "original".into()),
        ]),
    ] {
        let original = base.clone();
        for local in [None, Some(("ev", "first")), Some(("fresh", "second"))] {
            let variables = PatternVariables { base: &base, local };
            let mut copied = base.clone();
            if let Some((name, value)) = local {
                copied.insert(name.into(), value.into());
            }
            for name in ["x", "ev", "fresh", "missing"] {
                assert_eq!(variables.get(name), copied.get(name).map(String::as_str));
            }
        }
        assert_eq!(base, original);
    }
}

#[test]
fn local_pattern_templates_preserve_shadowing_skolems_recursion_and_refusal() {
    // Direct tests of the internal template builder, not a hand-built substitute
    // for surface event decomposition. Surface behavior has a separate test.
    let base = HashMap::from([
        ("x".into(), "outer".into()),
        ("ev".into(), "original".into()),
    ]);
    let ground_symbol = SkolemSymbol::for_test(1);
    let dependent_symbol = SkolemSymbol::for_test(2);
    let ground = HashMap::from([
        ("ev".into(), ground_symbol),
        ("ground".into(), ground_symbol),
        ("both".into(), ground_symbol),
    ]);
    let dependent = HashMap::from([
        ("ev".into(), (dependent_symbol, vec!["outer".into()])),
        ("dependent".into(), (dependent_symbol, vec!["outer".into()])),
        ("both".into(), (dependent_symbol, vec!["outer".into()])),
    ]);
    let mut args: Vec<_> = ["x", "ev", "ground", "dependent", "both", "missing"]
        .into_iter()
        .map(|name| LogicalTerm::Variable(name.into()))
        .collect();
    args.extend([
        LogicalTerm::Constant("Constant".into()),
        LogicalTerm::Description("description".into()),
        LogicalTerm::Number(7.0),
        LogicalTerm::Unspecified,
    ]);
    let buffer = LogicBuffer {
        nodes: vec![
            LogicNode::Predicate(("template".into(), args.clone())),
            LogicNode::ExistsNode(("ev".into(), 0)),
            LogicNode::ObligatoryNode(1),
            LogicNode::PermittedNode(1),
            LogicNode::ExistsNode(("missing".into(), 0)),
            LogicNode::NotNode(0),
            LogicNode::AndNode((0, 0)),
            LogicNode::ComputeNode(("template".into(), args)),
            LogicNode::ExistsNode(("fresh".into(), 0)),
        ],
        roots: vec![0],
    };
    for local in [None, Some(("ev", "local")), Some(("fresh", "new"))] {
        let variables = PatternVariables { base: &base, local };
        let mut copied = base.clone();
        if let Some((name, value)) = local {
            copied.insert(name.into(), value.into());
        }
        for tense in [
            None,
            Some("Past"),
            Some("Present"),
            Some("Future"),
            Some("Obligatory"),
            Some("Permitted"),
        ] {
            for node in (0..buffer.nodes.len() as u32).chain([u32::MAX]) {
                let actual = build_rule_template_fact_with_variables(
                    &buffer, node, variables, &ground, &dependent, tense,
                );
                let copied_result =
                    build_rule_template_fact(&buffer, node, &copied, &ground, &dependent, tense);
                assert_eq!(
                    actual, copied_result,
                    "node={node}, local={local:?}, tense={tense:?}"
                );
                if [4, 5, 6, u32::MAX].contains(&node)
                    || (node == 8 && local != Some(("fresh", "new")))
                {
                    assert!(actual.is_none());
                } else {
                    let expected = vec![
                        GroundTerm::PatternVar("outer".into()),
                        GroundTerm::PatternVar(
                            if local == Some(("ev", "local")) {
                                "local"
                            } else {
                                "original"
                            }
                            .into(),
                        ),
                        GroundTerm::Skolem(ground_symbol),
                        GroundTerm::SkolemFn(
                            dependent_symbol,
                            Box::new(GroundTerm::PatternVar("outer".into())),
                        ),
                        GroundTerm::Skolem(ground_symbol),
                        GroundTerm::PatternVar("missing".into()),
                        GroundTerm::Constant("Constant".into()),
                        GroundTerm::Description("description".into()),
                        GroundTerm::from_f64(7.0),
                        GroundTerm::Unspecified,
                    ];
                    assert_eq!(
                        actual,
                        Some(StoredFact::with_tense(
                            GroundFact::new("template", expected),
                            tense
                        ))
                    );
                }
            }
        }
    }
}
