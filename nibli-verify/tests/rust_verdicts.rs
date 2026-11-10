use nibli_verify::rust_verdicts::{Bundle, Case, Fact, Path, Status, session, verify};
use std::collections::BTreeMap;

fn fixture() -> Bundle {
    let mut b = Bundle {
        schema: 1,
        domain: vec!["QueryResult::True".into(), "QueryResult::False".into()],
        cases: vec![],
        paths: vec![],
        locations: BTreeMap::new(),
        facts: vec![],
    };
    fn fact(b: &mut Bundle, r: &str, args: &[&str]) {
        b.facts.push(Fact {
            relation: r.into(),
            arguments: args.iter().map(|a| (*a).into()).collect(),
        });
    }
    let t = "QueryResult::True";
    let f = "QueryResult::False";
    for v in [t, f] {
        fact(&mut b, "rv_type", &[v, "QueryResult"]);
        fact(&mut b, "rv_enum", &[v, v]);
    }
    fact(&mut b, "rv_distinct", &[t, f]);
    fact(&mut b, "rv_distinct", &[f, t]);
    fact(&mut b, "rv_guard_start", &["g0"]);
    // Small, independently written execution-path fixture. Production tests
    // obtain their paths from freshly extracted Rust, never this table.
    for (root, rows) in [
        (
            "and",
            vec![
                (vec![t, t], t),
                (vec![t, f], f),
                (vec![f, t], f),
                (vec![f, f], f),
            ],
        ),
        (
            "or",
            vec![
                (vec![t, t], t),
                (vec![t, f], t),
                (vec![f, t], t),
                (vec![f, f], f),
            ],
        ),
        ("not", vec![(vec![t], f), (vec![f], t)]),
    ] {
        for i in 0..if root == "not" { 1 } else { 2 } {
            fact(
                &mut b,
                "rv_argument",
                &[&format!("arg-{root}-{i}"), root, &i.to_string()],
            );
        }
        for (inputs, result) in rows {
            let id = format!("c{}", b.cases.len());
            let path = format!("p{id}");
            let expr = format!("e{id}");
            fact(&mut b, "rv_case", &[&id, root]);
            fact(&mut b, "rv_literal", &[&expr, root, result]);
            let mut guards = vec![];
            for (i, v) in inputs.iter().enumerate() {
                fact(&mut b, "rv_input", &[&id, &i.to_string(), v]);
                let guard = format!("g{id}-{i}");
                fact(
                    &mut b,
                    "rv_guard_test",
                    &[&guard, &format!("arg-{root}-{i}"), v],
                );
                guards.push(guard);
            }
            let guard = if guards.len() == 2 {
                let joined = format!("g{id}");
                fact(&mut b, "rv_guard_join", &[&joined, &guards[0], &guards[1]]);
                joined
            } else {
                guards[0].clone()
            };
            fact(&mut b, "rv_path", &[&path, root, &guard, &expr]);
            b.locations
                .insert(path.clone(), serde_json::json!({"fixture":true}));
            b.paths.push(Path {
                id: path,
                root: root.into(),
                kind: "return".into(),
                detail: expr,
            });
            b.cases.push(Case {
                id,
                root: root.into(),
                inputs: inputs.into_iter().map(str::to_owned).collect(),
            });
        }
    }
    b
}

#[test]
fn verifies_paths_and_rejects_wrong_outputs() {
    let mut b = fixture();
    let report = verify(&b).unwrap();
    assert_eq!(report.status, Status::Verified);
    let mut saved = serde_json::to_value(&report).unwrap();
    assert_eq!(
        nibli_verify::rust_verdicts::replay(&b, &saved)
            .unwrap()
            .status,
        Status::Verified
    );
    saved["cases"][0]["trace"]["observations"][0]["holds"] = serde_json::json!(false);
    assert!(nibli_verify::rust_verdicts::replay(&b, &saved).is_err());
    b.facts
        .iter_mut()
        .find(|f| f.relation == "rv_literal")
        .unwrap()
        .arguments[2] = "QueryResult::False".into();
    let report = verify(&b).unwrap();
    assert_eq!(report.status, Status::Counterexample);
    assert!(
        report
            .cases
            .iter()
            .any(|c| c.status == Status::Counterexample && !c.selected_paths.is_empty())
    );
}

#[test]
fn unreachable_barrier_does_not_hide_a_valid_execution() {
    let mut b = fixture();
    for (r, a) in [
        (
            "rv_guard_test",
            vec!["never-true", "arg-and-0", "QueryResult::True"],
        ),
        (
            "rv_guard_test",
            vec!["never-false", "arg-and-0", "QueryResult::False"],
        ),
        (
            "rv_guard_join",
            vec!["impossible", "never-true", "never-false"],
        ),
        (
            "rv_barrier",
            vec!["unreachable", "and", "impossible", "unsupported"],
        ),
    ] {
        b.facts.push(Fact {
            relation: r.into(),
            arguments: a.into_iter().map(str::to_owned).collect(),
        });
    }
    b.paths.push(Path {
        id: "unreachable".into(),
        root: "and".into(),
        kind: "blocked".into(),
        detail: "unsupported".into(),
    });
    b.locations
        .insert("unreachable".into(), serde_json::json!({"fixture":true}));
    assert_eq!(verify(&b).unwrap().status, Status::Verified);
}

#[test]
fn selected_barrier_is_inconclusive_and_selected_panic_is_a_counterexample() {
    for (kind, relation, status) in [
        ("blocked", "rv_barrier", Status::Inconclusive),
        ("panic", "rv_trap", Status::Counterexample),
    ] {
        let mut b = fixture();
        b.paths[0].kind = kind.into();
        b.facts
            .iter_mut()
            .find(|f| f.relation == "rv_path")
            .unwrap()
            .relation = relation.into();
        assert_eq!(verify(&b).unwrap().status, status);
    }
}

#[test]
fn missing_cases_duplicates_and_asserted_conclusions_fail_closed() {
    let mut missing = fixture();
    missing.cases.pop();
    assert!(missing.validate().is_err());
    let mut duplicate = fixture();
    duplicate.cases.push(duplicate.cases[0].clone());
    assert!(duplicate.validate().is_err());
    let mut injected = fixture();
    injected.facts.push(Fact {
        relation: "rv_case_ok".into(),
        arguments: vec!["c0".into()],
    });
    assert!(session(&injected).err().unwrap().contains("unadmitted"));
    let mut missing_guard = fixture();
    missing_guard
        .facts
        .iter_mut()
        .find(|f| f.relation == "rv_path")
        .unwrap()
        .arguments[2] = "missing".into();
    assert!(
        missing_guard
            .validate()
            .unwrap_err()
            .contains("missing path guard")
    );
    let mut cycle = fixture();
    cycle.facts.push(Fact {
        relation: "rv_guard_join".into(),
        arguments: vec!["cycle".into(), "cycle".into(), "g0".into()],
    });
    assert!(cycle.validate().unwrap_err().contains("cyclic"));
    let engine = session(&fixture()).unwrap();
    assert!(engine.assert_text("rv_case_ok(\"c0\").").is_err());
}

#[test]
fn incomplete_materialization_is_never_accepted() {
    let engine = session(&fixture()).unwrap();
    engine.set_materialization(false);
    engine.set_max_chain_depth(1).unwrap();
    assert!(nibli_verify::static_check::verdict(&engine, "rv_case_ok(\"c0\").").is_err());
}

#[test]
fn malformed_input_clears_stale_cli_success() {
    let directory =
        std::env::temp_dir().join(format!("nibli-verdict-invalid-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("bundle.json"), "{malformed").unwrap();
    std::fs::write(directory.join("result.json"), r#"{"status":"verified"}"#).unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_nibli-verify-rust"))
        .arg(directory.join("bundle.json"))
        .arg(&directory)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    let report: serde_json::Value =
        serde_json::from_slice(&std::fs::read(directory.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["status"], "inconclusive");
    std::fs::remove_dir_all(directory).unwrap();
}
