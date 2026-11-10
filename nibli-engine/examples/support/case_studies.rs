//! Shared native case-study runner. Expectations are authored independently in JSON.
use nibli_engine::{NibliEngine, validate_envelope};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

fn string<'a>(v: &'a Value, key: &str) -> Result<&'a str, String> {
    v[key]
        .as_str()
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("missing {key}"))
}

pub fn manifest(root: &Path, name: &str) -> Result<Value, String> {
    let path = root
        .join("examples/case-studies")
        .join(name)
        .join("manifest.json");
    let value: Value = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    validate_manifest(root, &value)?;
    Ok(value)
}

pub fn validate_manifest(root: &Path, value: &Value) -> Result<(), String> {
    if value["schema"] != 1 {
        return Err("unsupported manifest schema".into());
    }
    let corpus = string(value, "corpus")?;
    if !matches!(corpus, "gdpr.nibli" | "drug-interactions.nibli") {
        return Err("unrecognized case-study corpus".into());
    }
    let text = std::fs::read_to_string(root.join(corpus)).map_err(|e| e.to_string())?;
    let statements: Vec<_> = text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect();
    let sources: BTreeSet<_> = value["sources"]
        .as_array()
        .ok_or("missing sources")?
        .iter()
        .map(|s| string(s, "id"))
        .collect::<Result<_, _>>()?;
    let rows = value["assertions"].as_array().ok_or("missing assertions")?;
    if rows.len() != statements.len() {
        return Err("corpus/manifest statement count differs".into());
    }
    let mut ids = BTreeSet::new();
    for (row, expected) in rows.iter().zip(&statements) {
        if !ids.insert(string(row, "id")?) {
            return Err("duplicate source id".into());
        }
        if string(row, "statement")? != *expected {
            return Err("corpus/manifest statement differs".into());
        }
        string(row, "meaning")?;
        let refs = row["sources"]
            .as_array()
            .ok_or("missing source references")?;
        if refs.is_empty()
            || refs
                .iter()
                .any(|r| !r.as_str().is_some_and(|r| sources.contains(r)))
        {
            return Err("unknown or empty source reference".into());
        }
    }
    // Case bindings are a validated input contract. Labels and names never infer actors.
    for scope in value["scopes"]
        .as_array()
        .ok_or("missing scope inventory")?
    {
        let scope_id = string(scope, "id")?;
        let expected = scope["required_assertions"]
            .as_array()
            .ok_or("missing scope bindings")?;
        if expected.is_empty() {
            return Err(format!("empty scope {scope_id}"));
        }
        for binding in expected {
            let id = binding
                .as_str()
                .ok_or("scope binding must be a source id")?;
            if !ids.contains(id) {
                return Err(format!("missing scope binding {id}"));
            }
        }
        for field in scope["unique_fields"]
            .as_array()
            .ok_or("missing unique fields")?
        {
            let values = field["values"].as_array().ok_or("missing field values")?;
            if values.len() != 1 || values[0].as_str().is_none_or(str::is_empty) {
                return Err(format!(
                    "scope {scope_id} requires one {}",
                    string(field, "name")?
                ));
            }
            let predicate = string(field, "predicate")?;
            let selector = field["selector"]
                .as_array()
                .ok_or("missing binding selector")?;
            let index = field["value_index"]
                .as_u64()
                .ok_or("missing binding place")? as usize;
            if index >= selector.len() {
                return Err("binding place outside selector".into());
            }
            let prefix = format!("{predicate}(");
            let mut actual = BTreeSet::new();
            for line in &statements {
                let Some(body) = line
                    .strip_prefix(&prefix)
                    .and_then(|s| s.strip_suffix(")."))
                else {
                    continue;
                };
                let args: Vec<_> = body.split(',').map(str::trim).collect();
                if args.len() == selector.len()
                    && args
                        .iter()
                        .zip(selector)
                        .all(|(a, s)| s.is_null() || s.as_str() == Some(*a))
                {
                    actual.insert(args[index]);
                }
            }
            if actual.len() != 1 || !actual.contains(values[0].as_str().unwrap()) {
                return Err(format!(
                    "scope {scope_id} {} does not match unique source binding",
                    string(field, "name")?
                ));
            }
        }
    }
    Ok(())
}

pub fn run(root: &Path, name: &str, materialize: bool, captures: bool) -> Result<Value, String> {
    let manifest = manifest(root, name)?;
    let path = root
        .join("examples/case-studies")
        .join(name)
        .join("scenarios.json");
    let scenarios: Value = serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let mut reports = Vec::new();
    for scenario in scenarios.as_array().ok_or("scenarios must be an array")? {
        let title = string(scenario, "name")?;
        let engine = NibliEngine::new();
        engine.set_materialization(materialize);
        engine.set_strict(false);
        engine
            .set_existential_import(false)
            .map_err(|e| e.to_string())?;
        engine.set_max_chain_depth(10).map_err(|e| e.to_string())?;
        let mut ids = BTreeMap::new();
        for row in manifest["assertions"].as_array().unwrap() {
            let assigned = engine
                .assert_text(string(row, "statement")?)
                .map_err(|e| format!("{title}: load {}: {e}", row["id"]))?;
            if assigned.len() != 1 {
                return Err("source record must contain exactly one assertion".into());
            }
            ids.insert(string(row, "id")?.to_owned(), assigned[0]);
        }
        let mut steps = Vec::new();
        for action in scenario["steps"]
            .as_array()
            .ok_or("missing scenario steps")?
        {
            match string(action, "op")? {
                "assert" => {
                    let id = string(action, "id")?;
                    if ids.contains_key(id) {
                        return Err(format!("duplicate operation id {id}"));
                    }
                    let assigned = engine
                        .assert_text(string(action, "text")?)
                        .map_err(|e| format!("{title}: {e}"))?;
                    if assigned.len() != 1 {
                        return Err("operation requires one assertion".into());
                    }
                    ids.insert(id.to_owned(), assigned[0]);
                    steps.push(json!({"op":"assert","source":id,"runtime_id":assigned[0],"text":action["text"]}));
                }
                "retract" => {
                    let id = string(action, "id")?;
                    let runtime = *ids
                        .get(id)
                        .ok_or_else(|| format!("unknown source id {id}"))?;
                    engine.retract_fact(runtime).map_err(|e| e.to_string())?;
                    steps.push(json!({"op":"retract","source":id,"runtime_id":runtime}));
                }
                "reject" => {
                    if engine.assert_text(string(action, "text")?).is_ok() {
                        return Err(format!("{title}: protected assertion accepted"));
                    }
                    steps.push(json!({"op":"reject","text":action["text"],"rejected":true}));
                }
                "query" => {
                    let query = string(action, "text")?;
                    let expected = string(action, "expected")?;
                    let result = engine
                        .query_holds(query)
                        .map_err(|e| format!("{title}: {query}: {e}"))?;
                    let actual = result.status_label();
                    if actual != expected {
                        return Err(format!(
                            "{title}: {query}: expected {expected}, got {result:?}"
                        ));
                    }
                    let mut row = json!({"op":"query","query":query,"expected":expected,"actual":actual,"meaning":action["meaning"]});
                    if captures {
                        let cert = engine.certify_text(query).map_err(|e| e.to_string())?;
                        validate_envelope(&cert).map_err(|e| format!("invalid envelope: {e:?}"))?;
                        row["certificate"] =
                            serde_json::to_value(&cert).map_err(|e| e.to_string())?;
                        let (_, proof, _) = engine
                            .query_text_with_proof(query)
                            .map_err(|e| e.to_string())?;
                        row["proof"] = json!(proof);
                        row["source_ids"] = json!(ids);
                    }
                    steps.push(row);
                }
                other => return Err(format!("unknown operation {other}")),
            }
        }
        reports.push(json!({"scenario":title,"steps":steps}));
    }
    Ok(
        json!({"schema":1,"case_study":name,"materialization":materialize,"depth":10,"strict":false,"existential_import":false,"runtime":"native","package_version":env!("CARGO_PKG_VERSION"),"scenario_count":reports.len(),"scenarios":reports}),
    )
}
