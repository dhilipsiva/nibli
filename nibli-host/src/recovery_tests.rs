//! Real-component regressions are explicitly run by `smoke-host-state-controls`.
//! They fail if the requested component is absent; native CI does not build WASM.
use super::*;

#[test]
fn depth_parser_rejects_non_positive_or_non_integer_inputs() {
    for value in [
        "",
        "0",
        "-1",
        "+1",
        "1.5",
        "4294967296",
        " 10",
        "10 ",
        "ten",
    ] {
        assert!(parse_depth(value).is_err(), "accepted {value:?}");
    }
    assert_eq!(parse_depth("1"), Ok(1));
    assert_eq!(parse_depth("10"), Ok(10));
    assert_eq!(parse_depth("4294967295"), Ok(u32::MAX));
}

fn component_repl(nibli_store: Option<NibliStore>) -> Repl {
    let mut config = Config::new();
    config.wasm_component_model(true).consume_fuel(true);
    let engine = Engine::new(&config).unwrap();
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker).unwrap();
    compute_backend::add_to_linker::<HostState, HasSelf<HostState>>(
        &mut linker,
        |state: &mut HostState| state,
    )
    .unwrap();
    let path =
        std::env::var("NIBLI_WASM_PATH").expect("set NIBLI_WASM_PATH to the built component");
    // Cargo runs tests from this crate's directory; task-runner paths refer to
    // the workspace, as they do for an ordinary host process.
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join(path);
    let component = Component::from_file(&engine, path).expect("load built component");
    let fuel_budget = 50_000_000_000;
    let (store, pipeline, session_handle) = Repl::instantiate_session(
        &engine,
        &component,
        &linker,
        fuel_budget,
        512,
        None,
        SessionOptions {
            quiet: true,
            strict: false,
            existential_import: false,
            materialization: true,
        },
    )
    .unwrap();
    Repl {
        engine,
        component,
        linker,
        store,
        pipeline,
        session_handle,
        fuel_budget,
        memory_limit_mb: 512,
        nibli_store,
        db_path: None,
        journal: vec![
            JournalEntry::Strict(false),
            JournalEntry::ExistentialImport(false),
            JournalEntry::Depth(10),
        ],
        recovery_required: None,
        needs_rebuild: false,
        quiet: true,
        strict: false,
        existential_import: false,
        max_chain_depth: 10,
        materialization: true,
    }
}

fn active_ids(repl: &mut Repl) -> Vec<u64> {
    repl.prepare_session().unwrap();
    repl.pipeline
        .nibli_engine_engine()
        .session()
        .call_list_facts(&mut repl.store, repl.session_handle)
        .unwrap()
        .unwrap()
        .into_iter()
        .map(|fact| fact.id)
        .collect()
}

fn records(repl: &mut Repl) -> Vec<(u64, String, bool)> {
    repl.prepare_session().unwrap();
    repl.pipeline
        .nibli_engine_engine()
        .session()
        .call_list_assertion_records(&mut repl.store, repl.session_handle)
        .unwrap()
        .unwrap()
        .into_iter()
        .map(|record| {
            (
                record.id,
                record.label,
                matches!(
                    record.status,
                    pipeline_bind::nibli::engine::logic_types::AssertionStatus::Withdrawn
                ),
            )
        })
        .collect()
}

#[test]
#[ignore = "requires the built WASM component; run smoke-host-state-controls"]
fn wasm_storage_batch_failure_restores_the_committed_session() {
    let dir = tempfile::tempdir().unwrap();
    let store = NibliStore::open(&dir.path().join("batch.redb"), "test".into()).unwrap();
    let mut repl = component_repl(Some(store));
    repl.dispatch("dog(Adam).");
    // Inject a real durable collision on the SECOND tentative root. This makes
    // the canonical transaction fail after checking/inserting its first root.
    repl.nibli_store
        .as_mut()
        .unwrap()
        .insert_fact(2, "external collision".into(), vec![])
        .unwrap();
    let journal_len = repl.journal.len();
    assert!(!repl.dispatch("dog(Bob). cat(Carol)."));
    assert_eq!(active_ids(&mut repl), vec![0]);
    assert_eq!(
        records(&mut repl).len(),
        1,
        "failed roots must not become withdrawn history"
    );
    assert_eq!(repl.journal.len(), journal_len);
    assert!(
        repl.nibli_store
            .as_ref()
            .unwrap()
            .get_fact(1)
            .unwrap()
            .is_none()
    );
    assert_eq!(
        repl.nibli_store
            .as_ref()
            .unwrap()
            .total_fact_count()
            .unwrap(),
        2
    );
    repl.shutdown().unwrap();
}

#[test]
#[ignore = "requires the built WASM component; run smoke-host-state-controls"]
fn wasm_recovery_replays_original_configuration_order() {
    let mut repl = component_repl(None);
    // Raw typed buffers are a public replay API. Unlike the KR front-end's
    // fixed-arity compilation, this boundary can preserve a non-strict warning
    // accepted in an earlier profile. Final-strict replay would reject id 1.
    for (id, names) in [(0, vec!["Adam", "Bel"]), (1, vec!["Carol"])] {
        let buffer = NibliBuffer {
            nodes: vec![NibliNode::Predicate((
                "host_arity_fixture".into(),
                names
                    .into_iter()
                    .map(|name| NibliTerm::Constant(name.into()))
                    .collect(),
            ))],
            roots: vec![0],
        };
        repl.pipeline
            .nibli_engine_engine()
            .session()
            .call_assert_buffer_with_id(
                &mut repl.store,
                repl.session_handle,
                &types_logic_buffer_to_wit(&buffer),
                "raw arity fixture",
                id,
            )
            .unwrap()
            .unwrap();
        repl.journal.push(JournalEntry::AssertBuffer {
            buffer,
            label: "raw arity fixture".into(),
            id,
        });
    }
    assert_eq!(active_ids(&mut repl), vec![0, 1]);
    repl.dispatch(":strict on");
    repl.dispatch(":existential-import on");
    repl.dispatch(":depth 23");
    for invalid in ["0", "-1", "1.5", "4294967296"] {
        repl.dispatch(&format!(":depth {invalid}"));
        assert_eq!(repl.max_chain_depth, 23);
    }
    repl.dispatch(":fuel 1");
    repl.dispatch("? dog(Adam).");
    assert!(repl.needs_rebuild, "must induce an actual component trap");
    repl.dispatch(":fuel 50000000000");
    assert_eq!(active_ids(&mut repl), vec![0, 1]);
    let session = repl.pipeline.nibli_engine_engine().session();
    assert_eq!(
        session
            .call_max_chain_depth(&mut repl.store, repl.session_handle)
            .unwrap(),
        23
    );
    assert!(
        session
            .call_existential_import_enabled(&mut repl.store, repl.session_handle)
            .unwrap()
    );
    assert!(repl.strict);
    let mismatch = NibliBuffer {
        nodes: vec![NibliNode::Predicate((
            "host_arity_fixture".into(),
            vec![NibliTerm::Constant("Dora".into())],
        ))],
        roots: vec![0],
    };
    let rejection = repl
        .pipeline
        .nibli_engine_engine()
        .session()
        .call_assert_buffer_with_id(
            &mut repl.store,
            repl.session_handle,
            &types_logic_buffer_to_wit(&mismatch),
            "strict control",
            9,
        )
        .unwrap();
    assert!(
        rejection.is_err(),
        "fixture must distinguish original non-strict acceptance from final strict policy"
    );
    repl.dispatch(":reset");
    assert!(records(&mut repl).is_empty());
    repl.needs_rebuild = true;
    repl.prepare_session().unwrap();
    assert!(records(&mut repl).is_empty());
    assert_eq!(
        repl.pipeline
            .nibli_engine_engine()
            .session()
            .call_max_chain_depth(&mut repl.store, repl.session_handle)
            .unwrap(),
        23
    );
    repl.shutdown().unwrap();
}

#[test]
#[ignore = "requires the built WASM component; run smoke-host-state-controls"]
fn wasm_failed_replay_never_publishes_its_prefix() {
    let mut repl = component_repl(None);
    repl.dispatch("dog(Adam).");
    repl.journal
        .push(JournalEntry::RegisterCompute("not_in_the_corpus".into()));
    repl.store.set_fuel(777_777).unwrap();
    repl.needs_rebuild = true;
    assert!(repl.prepare_session().is_err());
    assert!(repl.needs_rebuild);
    assert_eq!(
        repl.store.get_fuel().unwrap(),
        777_777,
        "candidate replaced the old store before completing replay"
    );
    assert!(
        !repl.dispatch(":facts"),
        "unavailable session should keep host controls usable"
    );
    assert!(repl.needs_rebuild);
    repl.journal.pop();
    assert_eq!(active_ids(&mut repl), vec![0]);
    repl.shutdown().unwrap();
}

#[test]
#[ignore = "requires the built WASM component; run smoke-host-state-controls"]
fn wasm_withdrawn_envelopes_reserve_ids_without_decoding_payloads() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("withdrawn.redb");
    let mut store = NibliStore::open(&path, "test".into()).unwrap();
    store
        .insert_fact(8, "obsolete source".into(), vec![255, 255])
        .unwrap();
    store.retract_fact(8).unwrap();
    let mut repl = component_repl(Some(store));
    repl.replay_persisted().unwrap();
    assert_eq!(
        records(&mut repl),
        vec![(8, "obsolete source".into(), true)]
    );
    repl.dispatch(":assert dog Bob");
    assert_eq!(active_ids(&mut repl), vec![9]);
    repl.dispatch(":retract 9");
    let before = records(&mut repl);
    repl.shutdown().unwrap();
    let mut reopened = component_repl(Some(NibliStore::open(&path, "test".into()).unwrap()));
    reopened.replay_persisted().unwrap();
    assert_eq!(
        records(&mut reopened),
        before,
        "labels/statuses must survive reopening"
    );
    reopened.dispatch("dog(Carol).");
    assert_eq!(active_ids(&mut reopened), vec![10]);
    reopened.needs_rebuild = true;
    reopened.prepare_session().unwrap();
    assert_eq!(records(&mut reopened).len(), 3);
    reopened.shutdown().unwrap();
}

#[test]
#[ignore = "requires the built WASM component; run smoke-host-state-controls"]
fn wasm_ambiguous_commit_requires_reopening() {
    let mut repl = component_repl(None);
    let journal_len = repl.journal.len();
    repl.persistence_failed(StoreError::CommitOutcomeUnknown(
        "injected uncertain commit".into(),
    ));
    assert!(repl.prepare_session().is_err());
    assert!(
        repl.dispatch("dog(Adam)."),
        "ambiguous commit must terminate this session"
    );
    assert_eq!(repl.journal.len(), journal_len);
    assert!(repl.shutdown().is_err());
}
