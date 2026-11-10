//! Independent source-scope controls for the default teaching corpora.
#[path = "../examples/support/case_studies.rs"]
mod cases;
fn root() -> &'static std::path::Path {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
}
#[test]
fn gdpr_reviewed_scope_controls() {
    for materialize in [false, true] {
        cases::run(root(), "gdpr", materialize, false).unwrap();
    }
}
#[test]
fn drug_patient_episode_controls() {
    for materialize in [false, true] {
        cases::run(root(), "drug", materialize, false).unwrap();
    }
}
#[test]
fn manifests_reject_missing_ambiguous_or_unattributed_inputs() {
    let original = cases::manifest(root(), "gdpr").unwrap();
    let mut missing = original.clone();
    missing["scopes"][0]["required_assertions"][0] = serde_json::json!("missing");
    assert!(cases::validate_manifest(root(), &missing).is_err());
    let mut ambiguous = original.clone();
    ambiguous["scopes"][0]["unique_fields"][0]["values"] =
        serde_json::json!(["ControllerA", "ControllerB"]);
    assert!(cases::validate_manifest(root(), &ambiguous).is_err());
    let mut mismatched = original.clone();
    mismatched["scopes"][0]["unique_fields"][0]["values"] = serde_json::json!(["ControllerB"]);
    assert!(cases::validate_manifest(root(), &mismatched).is_err());
    let mut unattributed = original;
    unattributed["assertions"][0]["sources"] = serde_json::json!([]);
    assert!(cases::validate_manifest(root(), &unattributed).is_err());
}
