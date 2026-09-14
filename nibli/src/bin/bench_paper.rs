//! Private, release-only research driver. Workload generation and expected
//! answers live outside Rust so this binary cannot manufacture its own oracle.
//! JSON Lines are flushed after each phase, preserving partial timeout evidence.
use nibli_engine::{NibliEngine, validate_envelope};
use serde::Deserialize;
use serde_json::{Value, json};
use std::io::Write;
use std::path::Path;
use std::time::Instant;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    statements: Vec<String>,
    queries: Vec<String>,
    depth: u32,
    materialization: bool,
    mode: String,
    #[serde(default)]
    updates: Vec<Update>,
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Update {
    Retract { index: usize },
    Assert { text: String },
    Reopen,
}

fn emit(value: Value) -> Result<(), String> {
    println!("{value}");
    std::io::stdout().flush().map_err(|e| e.to_string())
}

fn configure(engine: &NibliEngine, request: &Request) -> Result<(), String> {
    engine.set_verbose(false);
    engine.set_materialization(request.materialization);
    engine
        .set_max_chain_depth(request.depth)
        .map_err(|e| e.to_string())
}

fn queries(engine: &NibliEngine, request: &Request, stage: usize) -> Result<(), String> {
    for (index, query) in request.queries.iter().enumerate() {
        let start = Instant::now();
        if request.mode == "verdict" {
            let result = engine.query_holds(query).map_err(|e| e.to_string())?;
            let elapsed = start.elapsed().as_secs_f64() * 1000.0;
            emit(json!({"phase":"query", "stage":stage, "index":index,
                "ms":elapsed, "verdict":result.status_label(), "result":result}))?;
        } else {
            let envelope = engine.certify_text(query).map_err(|e| e.to_string())?;
            let elapsed = start.elapsed().as_secs_f64() * 1000.0;
            let validation_start = Instant::now();
            let coherence = validate_envelope(&envelope);
            let validation_ms = validation_start.elapsed().as_secs_f64() * 1000.0;
            let serialization_start = Instant::now();
            let encoded = serde_json::to_vec(&envelope).map_err(|e| e.to_string())?;
            let serialization_ms = serialization_start.elapsed().as_secs_f64() * 1000.0;
            emit(json!({"phase":"certificate", "stage":stage, "index":index,
                "ms":elapsed, "validation_ms":validation_ms,
                "serialization_ms":serialization_ms, "bytes":encoded.len(),
                "steps":envelope.trace.steps.len(),
                "verdict":envelope.result.status_label(), "envelope":envelope,
                "coherent":coherence.is_ok(), "coherence_errors":coherence.err()}))?;
        }
    }
    Ok(())
}

fn run() -> Result<(), String> {
    if cfg!(debug_assertions) {
        return Err("paper measurements require a release build".into());
    }
    let args: Vec<String> = std::env::args().collect();
    if !(2..=3).contains(&args.len()) {
        return Err("usage: nibli-bench-paper REQUEST.json [NEW-DATABASE]".into());
    }
    let request: Request =
        serde_json::from_slice(&std::fs::read(&args[1]).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    if !["verdict", "certificate", "updates"].contains(&request.mode.as_str()) {
        return Err("unknown measurement mode".into());
    }
    let database = args.get(2).map(Path::new);
    if database.is_some_and(Path::exists) {
        return Err("refusing to measure into an existing database".into());
    }
    if !request.updates.is_empty() && database.is_none() {
        return Err("update/reopen measurements require a fresh database".into());
    }
    let start = Instant::now();
    let mut engine = match database {
        Some(path) => NibliEngine::open(path)?,
        None => NibliEngine::new(),
    };
    configure(&engine, &request)?;
    emit(json!({"phase":"open", "ms":start.elapsed().as_secs_f64()*1000.0}))?;
    let start = Instant::now();
    let mut ids = Vec::new();
    // One assertion per source statement, identical for every run. Preserve IDs
    // for the update script; do not assume a rejected input consumed an ID.
    for statement in &request.statements {
        let allocated = engine.assert_text(statement).map_err(|e| e.to_string())?;
        if allocated.len() != 1 {
            return Err("each protocol statement must allocate exactly one assertion ID".into());
        }
        ids.push(allocated[0]);
    }
    emit(
        json!({"phase":"load", "ms":start.elapsed().as_secs_f64()*1000.0,
        "ids":ids, "statements":request.statements.len()}),
    )?;
    queries(&engine, &request, 0)?;
    for (i, update) in request.updates.iter().enumerate() {
        let start = Instant::now();
        let phase = match update {
            Update::Retract { index } => {
                let id = *ids.get(*index).ok_or("update index out of range")?;
                engine.retract_fact(id).map_err(|e| e.to_string())?;
                "withdrawal"
            }
            Update::Assert { text } => {
                let allocated = engine.assert_text(text).map_err(|e| e.to_string())?;
                if allocated.len() != 1 {
                    return Err("each reassertion must allocate one ID".into());
                }
                ids.push(allocated[0]);
                "reassertion"
            }
            Update::Reopen => {
                drop(engine);
                engine = NibliEngine::open(database.ok_or("reopen requires database")?)?;
                configure(&engine, &request)?;
                "reopen"
            }
        };
        emit(json!({"phase":phase, "stage":i+1,
            "ms":start.elapsed().as_secs_f64()*1000.0, "ids":ids}))?;
        queries(&engine, &request, i + 1)?;
    }
    emit(json!({"phase":"complete"}))
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            let _ = emit(json!({"phase":"error", "message":error}));
            std::process::ExitCode::FAILURE
        }
    }
}
