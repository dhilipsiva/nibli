//! Three-way determinism corpus, V8 leg: the SAME `determinism-corpus.nibli` twin
//! that the native engine (`determinism_corpus_nibli_kr_native`) and the Wasmtime
//! component (`smoke-host-determinism`) run must produce the identical pinned
//! verdicts when the pipeline is compiled to wasm32-unknown-unknown and executed
//! under node/V8 — the browser-class runtime the live playground uses. The
//! `set_language` call survives as a no-op shim exercise (the deployed
//! playground's JS still calls it until the site migration lands). Run via
//! `just verify-wasm-node` (`wasm-pack test --node nibli-wasm`); native
//! `cargo test` skips this file entirely (`#![cfg(target_arch = "wasm32")]`).

#![cfg(target_arch = "wasm32")]

use nibli_wasm::Session;
use wasm_bindgen_test::*;

enum COp {
    Assert(String),
    Query(String, String),
    Retract(usize),
}

/// Parse the shared corpus format (independently reimplemented per runner —
/// the runners must not share code paths beyond the engine itself; since the
/// nibli-session extraction "the engine" INCLUDES the shared CoreSession, so
/// the three-way corpus oracles the three runtime STACKS — native, Wasmtime,
/// V8 — rather than hand-mirrored compile chains).
fn parse_corpus(text: &str) -> Vec<COp> {
    let mut ops: Vec<COp> = Vec::new();
    let mut pending_q: Option<String> = None;
    for raw in text.lines() {
        let line = raw.trim();
        if let Some(ann) = line.strip_prefix("# =>") {
            let q = pending_q
                .take()
                .expect("corpus: `# =>` annotation without a preceding query");
            ops.push(COp::Query(q, ann.trim().to_string()));
        } else if line.is_empty() || line.starts_with('#') {
            continue;
        } else if let Some(q) = line.strip_prefix("? ") {
            assert!(
                pending_q.is_none(),
                "corpus: unannotated query before '{q}'"
            );
            pending_q = Some(q.to_string());
        } else if let Some(k) = line.strip_prefix(":retract ") {
            ops.push(COp::Retract(
                k.trim().parse().expect("corpus: retract index"),
            ));
        } else {
            ops.push(COp::Assert(line.to_string()));
        }
    }
    assert!(pending_q.is_none(), "corpus: trailing unannotated query");
    ops
}

#[wasm_bindgen_test]
fn determinism_corpus_v8() {
    let corpus = include_str!("../../determinism-corpus.nibli");
    let session = Session::new();
    session
        .set_language("klaro")
        .expect("set_language(klaro) must succeed");
    let mut ids: Vec<u64> = Vec::new();
    let mut checked = 0usize;

    for op in parse_corpus(corpus) {
        match op {
            COp::Assert(l) => match session.assert_text(&l) {
                // One id per root (the corpus has no medial `.i`, so each line
                // is a single fact — but extend, don't push, to stay correct).
                Ok(new_ids) => ids.extend(new_ids),
                Err(_) => panic!("assert '{l}' failed under V8"),
            },
            COp::Retract(k) => {
                if session.retract_fact(ids[k]).is_err() {
                    panic!("retract #{k} failed under V8");
                }
            }
            COp::Query(q, expected) => {
                let json = match session.query_with_proof(&q) {
                    Ok(j) => j,
                    Err(_) => panic!("query '{q}' failed under V8"),
                };
                let v: serde_json::Value =
                    serde_json::from_str(&json).expect("query_with_proof returns JSON");
                let status = v["status"].as_str().expect("status field");
                let got = match v["detail"].as_str() {
                    Some(detail) => format!("{status} ({detail})"),
                    None => status.to_string(),
                };
                assert_eq!(
                    got, expected,
                    "V8 verdict for '{q}' diverges from the pinned annotation"
                );
                checked += 1;
            }
        }
    }
    assert!(
        checked >= 15,
        "determinism corpus too small: {checked} queries"
    );
}
