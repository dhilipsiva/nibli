//! Lifecycle and witness contracts under the browser-class V8 runtime.
#![cfg(target_arch = "wasm32")]
use nibli_wasm::Session;
use wasm_bindgen_test::*;

#[wasm_bindgen_test]
fn checked_depth_history_and_certificate_survive_reset() {
    let session = Session::new();
    for depth in [0.0, -1.0, 1.5, f64::NAN, f64::INFINITY, 4294967296.0] {
        assert!(session.set_max_chain_depth(depth).is_err());
        assert_eq!(session.max_chain_depth(), 10);
    }
    session.set_max_chain_depth(17.0).unwrap();
    let id = session.assert_text("dog(Alis).").unwrap()[0];
    let envelope: serde_json::Value =
        serde_json::from_str(&session.certify("dog(Alis).").unwrap()).unwrap();
    assert_eq!(envelope["schema"], 2);
    assert_eq!(envelope["profile"]["max_chain_depth"], 17);
    session.retract_fact(id).unwrap();
    let records: serde_json::Value =
        serde_json::from_str(&session.list_assertion_records().unwrap()).unwrap();
    assert_eq!(records[0]["id"], id.to_string());
    assert_eq!(records[0]["status"], "withdrawn");
    assert_eq!(session.list_facts().unwrap(), "[]");
    session.reset().unwrap();
    assert_eq!(session.max_chain_depth(), 17);
    assert_eq!(session.list_assertion_records().unwrap(), "[]");
}

#[wasm_bindgen_test]
fn generated_individual_domain_agrees_across_query_forms() {
    let session = Session::new();
    session
        .assert_text("dog(Adam). likes(every dog, some cat).")
        .unwrap();
    for (query, expected) in [
        ("likes(Adam, some cat).", "TRUE"),
        ("likes(Adam, no cat).", "FALSE"),
        ("likes(Adam, exactly 1 cat).", "TRUE"),
    ] {
        let answer: serde_json::Value =
            serde_json::from_str(&session.query_with_proof(query).unwrap()).unwrap();
        assert_eq!(answer["status"], expected, "{query}");
    }
    let find: serde_json::Value =
        serde_json::from_str(&session.query_find("likes(Adam, $w).").unwrap()).unwrap();
    assert_eq!(find["bindings"].as_array().unwrap().len(), 1);
}

#[wasm_bindgen_test]
fn quoted_individual_witnesses_remain_opaque() {
    let session = Session::new();
    session
        .assert_text("person(Adam). entitled(every person, event { eats(some cat) }).")
        .unwrap();
    for (query, expected) in [
        ("entitled(Adam, event { eats(some cat) }).", "TRUE"),
        ("cat(some cat).", "FALSE"),
        ("eats(some cat).", "FALSE"),
        ("cat(exactly 0 cat).", "TRUE"),
    ] {
        let answer: serde_json::Value =
            serde_json::from_str(&session.query_with_proof(query).unwrap()).unwrap();
        assert_eq!(answer["status"], expected, "{query}");
    }
    let find: serde_json::Value =
        serde_json::from_str(&session.query_find("cat($x).").unwrap()).unwrap();
    assert!(find["bindings"].as_array().unwrap().is_empty());
}
