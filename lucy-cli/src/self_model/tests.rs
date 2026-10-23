use super::*;

fn scope() -> Scope {
    Scope {
        measurement: Measurement::Reported,
        source: "test".into(),
        context: digest(b"workspace"),
        capability: "read".into(),
    }
}

fn forecast(store: &Store) -> Prediction {
    predict(
        store,
        scope(),
        "session",
        "The next fixture operation succeeds.",
    )
    .unwrap()
}

#[test]
fn cold_start_feedback_and_recovery_are_evidence_driven() {
    let temp = tempfile::tempdir().unwrap();
    let store = Store::open(temp.path()).unwrap();
    assert_eq!(
        History::read(&store).unwrap().summary().unwrap()["scopes"],
        json!([])
    );
    let cold = forecast(&store);
    assert_eq!(
        (cold.probability_ppm, cold.policy),
        (500_000, Policy::Direct)
    );
    // Unresolved predictions and explicitly inconclusive observations do not
    // turn into failures or successes.
    let pending = forecast(&store);
    observe(
        &store,
        &cold.id,
        ResultKind::Inconclusive,
        "Fixture was cancelled.",
    )
    .unwrap();
    assert_eq!(forecast(&store).probability_ppm, 500_000);
    for _ in 0..2 {
        let p = forecast(&store);
        observe(
            &store,
            &p.id,
            ResultKind::Failure,
            "Fixture returned an error.",
        )
        .unwrap();
    }
    let cautious = forecast(&store);
    assert_eq!(
        (cautious.probability_ppm, cautious.policy),
        (250_000, Policy::InspectFirst)
    );
    assert_eq!(cautious.basis.len(), 2);
    assert!(!cautious.basis.iter().any(|id| id.contains(&pending.id)));
    for _ in 0..2 {
        let p = forecast(&store);
        observe(&store, &p.id, ResultKind::Success, "Fixture completed.").unwrap();
    }
    assert_eq!(forecast(&store).policy, Policy::Direct);
    let mut other = scope();
    other.measurement = Measurement::Runtime;
    assert_eq!(
        predict(&store, other, "session", "A native operation succeeds.")
            .unwrap()
            .probability_ppm,
        500_000
    );
    let summary = History::read(&store).unwrap().summary().unwrap();
    assert!(summary["pending"].as_u64().unwrap() > 0);
    assert_eq!(summary["scopes"].as_array().unwrap().len(), 2);
}

#[test]
fn learned_predictions_outscore_cold_baseline_on_a_repeated_failure_fixture() {
    let temp = tempfile::tempdir().unwrap();
    let store = Store::open(temp.path()).unwrap();
    for _ in 0..6 {
        let p = forecast(&store);
        observe(
            &store,
            &p.id,
            ResultKind::Failure,
            "Synthetic fixture returned an error.",
        )
        .unwrap();
    }
    let summary = History::read(&store).unwrap().summary().unwrap();
    // Brier scoring uses the forecast saved BEFORE each observation. With the
    // feedback ablated, every 0.5 forecast has squared error 0.25 here.
    assert!(summary["scopes"][0]["brier_score"].as_f64().unwrap() < 0.25);
    assert_eq!(summary["scopes"][0]["policy"], "inspect_first");
    // This fixture establishes mechanism, not improvement on arbitrary tasks.
}

#[test]
fn immutable_events_survive_reopen_reindex_and_backup() {
    let root = tempfile::tempdir().unwrap();
    let backup = tempfile::tempdir().unwrap();
    let restored = tempfile::tempdir().unwrap();
    let (before, manifest) = {
        let store = Store::open(root.path()).unwrap();
        let p = forecast(&store);
        let o = observe(&store, &p.id, ResultKind::Success, "Visible test result.").unwrap();
        assert_eq!(
            observe(&store, &p.id, ResultKind::Success, "Visible test result.").unwrap(),
            o
        );
        assert!(observe(&store, &p.id, ResultKind::Failure, "Contradiction.").is_err());
        assert!(observe(&store, "missing", ResultKind::Success, "Invented.").is_err());
        let before = History::read(&store).unwrap().summary().unwrap();
        (before, store.backup(backup.path()).unwrap())
    };
    let store = Store::open(root.path()).unwrap();
    store.sync().unwrap();
    assert_eq!(History::read(&store).unwrap().summary().unwrap(), before);
    let copy = Store::open(restored.path()).unwrap();
    copy.restore(&manifest).unwrap();
    assert_eq!(History::read(&copy).unwrap().summary().unwrap(), before);
}

#[test]
fn both_checkers_reject_orphans_future_evidence_duplicates_and_cycles() {
    let root = tempfile::tempdir().unwrap();
    let store = Store::open(root.path()).unwrap();
    let a = forecast(&store);
    let o = observe(&store, &a.id, ResultKind::Failure, "Fixture failure.").unwrap();
    let b = forecast(&store);
    let good = History::read(&store).unwrap();
    good.audit().unwrap();
    let mut cases = Vec::new();
    let mut bad = good.clone();
    bad.predictions.remove(&a.id);
    cases.push(bad);
    let mut bad = good.clone();
    bad.observations.remove(&o.id);
    cases.push(bad);
    let mut bad = good.clone();
    bad.observations.get_mut(&o.id).unwrap().at_ms = b.at_ms + 1;
    cases.push(bad);
    let mut bad = good.clone();
    bad.observations.get_mut(&o.id).unwrap().at_ms = a.at_ms - 1;
    cases.push(bad);
    let mut bad = good.clone();
    let mut duplicate = o.clone();
    duplicate.id = "different-outcome".into();
    bad.observations.insert(duplicate.id.clone(), duplicate);
    cases.push(bad);
    let mut bad = good.clone();
    bad.predictions.get_mut(&b.id).unwrap().scope.source = "someone-else".into();
    cases.push(bad);
    let mut bad = good.clone();
    bad.predictions.get_mut(&a.id).unwrap().basis = vec![o.id.clone()];
    bad.predictions.get_mut(&a.id).unwrap().at_ms = o.at_ms;
    cases.push(bad);
    for bad in cases {
        assert!(bad.graph_invalid());
        assert_eq!(
            bad.audit().unwrap_err(),
            "self-model evidence graph is invalid"
        );
    }
    let mut tampered = good.clone();
    tampered.predictions.get_mut(&b.id).unwrap().probability_ppm = 1_000_000;
    assert_eq!(
        tampered.audit().unwrap_err(),
        "prediction does not follow its recorded evidence"
    );
    let mut tampered = good;
    tampered
        .predictions
        .get_mut(&b.id)
        .unwrap()
        .basis
        .push(o.id);
    assert_eq!(
        tampered.audit().unwrap_err(),
        "invalid self-model prediction schema"
    );
}

#[test]
fn reification_is_deterministic_and_never_injects_text() {
    let root = tempfile::tempdir().unwrap();
    let store = Store::open(root.path()).unwrap();
    let mut hostile = scope();
    hostile.source = "\"). sl_invalid(History). # 雪".into();
    let p = predict(
        &store,
        hostile,
        "session",
        "Visible expectation; no source interpolation.",
    )
    .unwrap();
    observe(&store, &p.id, ResultKind::Success, "Visible evidence.").unwrap();
    let history = History::read(&store).unwrap();
    let facts = history.facts();
    assert_eq!(facts, History::read(&store).unwrap().facts());
    assert!(!facts.contains("sl_invalid"));
    assert!(!facts.contains("雪"));
    history.audit().unwrap();
}

#[test]
fn cli_reports_are_attributed_and_cannot_resolve_runtime_predictions() {
    let root = tempfile::tempdir().unwrap();
    let args = |op: &str| {
        vec![
            op.to_owned(),
            "--root".into(),
            root.path().to_str().unwrap().into(),
            "--stdin".into(),
        ]
    };
    let input = json!({"source":"codex","session":"real-session","context":"test workspace",
        "capability":"validation","expectation":"The stated check passes."});
    let p = command(&args("predict"), &input.to_string()).unwrap();
    assert_eq!(p["scope"]["measurement"], "reported");
    let o = json!({"prediction":p["id"],"result":"success","evidence":"I observed the named check pass."});
    command(&args("observe"), &o.to_string()).unwrap();
    assert_eq!(
        command(&args("status"), "").unwrap()["integrity"],
        "checked"
    );
    let mut forged = input;
    forged["measurement"] = json!("runtime");
    assert!(command(&args("predict"), &forged.to_string()).is_err());
    let native = {
        let store = Store::open(root.path()).unwrap();
        let mut scope = scope();
        scope.measurement = Measurement::Runtime;
        predict(&store, scope, "native", "Execution succeeds.").unwrap()
    };
    let fake =
        json!({"prediction":native.id,"result":"success","evidence":"A claim, not execution."});
    assert!(command(&args("observe"), &fake.to_string()).is_err());
    assert!(crate::cli::reads_stdin(&[
        "self-model".into(),
        "predict".into(),
        "--stdin".into()
    ]));
}
