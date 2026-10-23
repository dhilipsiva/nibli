//! An empirical self-model, rebuilt from immutable predictions and observations.
//! Its evidence graph is checked independently in Rust and Nibli. No record is
//! an instruction, an authorization, or evidence of consciousness.

use crate::store::{Record, Store, digest};
use nibli_engine::NibliEngine;
use nibli_types::logic::QueryResult;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

type Result<T> = std::result::Result<T, String>;
pub const SPEC: &str = include_str!("../constitution/self_model.nibli");
const ORIGIN: &str = "lucy:self-model:v1";
const MODEL: &str = "empirical-window32-beta1-v1";
const WINDOW: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Measurement {
    Runtime,
    Reported,
}

/// Keep different workspaces, observers and kinds of evidence separate. The
/// context is a digest, never the path or task text itself.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Scope {
    pub measurement: Measurement,
    pub source: String,
    pub context: String,
    pub capability: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Policy {
    Direct,
    InspectFirst,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ResultKind {
    Success,
    Failure,
    Inconclusive,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Prediction {
    pub id: String,
    pub at_ms: u64,
    pub scope: Scope,
    pub session: String,
    pub expectation: String,
    pub model: String,
    pub checker: String,
    /// IDs of prior observations, not conclusions manufactured by this model.
    pub basis: Vec<String>,
    pub probability_ppm: u32,
    pub policy: Policy,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Observation {
    pub id: String,
    pub prediction: String,
    pub at_ms: u64,
    pub result: ResultKind,
    /// A visible, bounded evidence summary; never raw tool/provider internals.
    pub evidence: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    content = "value",
    rename_all = "snake_case",
    deny_unknown_fields
)]
enum Event {
    Prediction(Prediction),
    Observation(Observation),
}

#[derive(Clone, Default)]
pub struct History {
    pub predictions: BTreeMap<String, Prediction>,
    pub observations: BTreeMap<String, Observation>,
}

fn now() -> Result<u64> {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_millis()
        .try_into()
        .map_err(|_| "clock exceeds timestamp range".into())
}

fn nonempty(text: &str) -> bool {
    !text.trim().is_empty() && text.len() <= 4096
}

// Injective byte encoding into a valid Nibli rigid constant. No source text is
// interpolated into the fact language, and map traversal determines fact order.
fn constant(text: &str) -> String {
    let mut out = String::from("C");
    for byte in text.bytes() {
        use std::fmt::Write;
        write!(out, "{byte:02x}").unwrap();
    }
    out
}

fn scope_key(scope: &Scope) -> String {
    serde_json::to_string(scope).unwrap()
}

fn estimate<'a>(observations: impl Iterator<Item = &'a Observation>) -> (u32, Policy) {
    let (mut successes, mut failures) = (0u32, 0u32);
    for observation in observations {
        match observation.result {
            ResultKind::Success => successes += 1,
            ResultKind::Failure => failures += 1,
            ResultKind::Inconclusive => {}
        }
    }
    let probability = (successes + 1) * 1_000_000 / (successes + failures + 2);
    let policy = if failures >= 2 && failures > successes {
        Policy::InspectFirst
    } else {
        Policy::Direct
    };
    (probability, policy)
}

impl History {
    pub fn read(store: &Store) -> Result<Self> {
        let mut history = Self::default();
        for record in store.all()?.into_iter().filter(|r| r.origin == ORIGIN) {
            let event: Event = serde_json::from_value(record.payload["event"].clone())
                .map_err(|e| format!("invalid self-model record: {e}"))?;
            let id = match &event {
                Event::Prediction(p) => &p.id,
                Event::Observation(o) => &o.id,
            };
            if record.payload["id"] != *id {
                return Err("self-model record/event IDs disagree".into());
            }
            match event {
                Event::Prediction(p) => {
                    history.predictions.insert(p.id.clone(), p);
                }
                Event::Observation(o) => {
                    history.observations.insert(o.id.clone(), o);
                }
            }
        }
        Ok(history)
    }

    fn recent(&self, scope: &Scope) -> Vec<&Observation> {
        let mut rows: Vec<_> = self
            .observations
            .values()
            .filter(|o| {
                o.result != ResultKind::Inconclusive
                    && self
                        .predictions
                        .get(&o.prediction)
                        .is_some_and(|p| &p.scope == scope)
            })
            .collect();
        rows.sort_by(|a, b| (b.at_ms, &b.id).cmp(&(a.at_ms, &a.id)));
        rows.truncate(WINDOW);
        rows
    }

    pub fn facts(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        for p in self.predictions.values() {
            let id = constant(&p.id);
            writeln!(
                out,
                "sl_prediction({id}).\nsl_scope({id}, {}).",
                constant(&scope_key(&p.scope))
            )
            .unwrap();
            for basis in &p.basis {
                let o = constant(basis);
                writeln!(out, "sl_basis({id}, {o}).").unwrap();
                if self
                    .observations
                    .get(basis)
                    .is_some_and(|o| o.at_ms <= p.at_ms)
                {
                    writeln!(out, "sl_precedes({o}, {id}).").unwrap();
                }
            }
        }
        for o in self.observations.values() {
            let (id, p) = (constant(&o.id), constant(&o.prediction));
            let result = match o.result {
                ResultKind::Success => "Success",
                ResultKind::Failure => "Failure",
                ResultKind::Inconclusive => "Inconclusive",
            };
            writeln!(out, "sl_observation({id}, {p}, {result}).").unwrap();
            if self
                .predictions
                .get(&o.prediction)
                .is_some_and(|p| p.at_ms <= o.at_ms)
            {
                writeln!(out, "sl_precedes({p}, {id}).").unwrap();
            }
        }
        out
    }

    /// The Rust oracle for the graph properties in SPEC, independent of its
    /// Horn-clause closure. Arithmetic/schema checks are a separate host boundary.
    fn graph_invalid(&self) -> bool {
        let mut resolved = BTreeSet::new();
        let mut edges: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for o in self.observations.values() {
            let Some(p) = self.predictions.get(&o.prediction) else {
                return true;
            };
            if o.at_ms < p.at_ms || !resolved.insert(&o.prediction) {
                return true;
            }
        }
        for p in self.predictions.values() {
            for basis in &p.basis {
                let Some(o) = self.observations.get(basis) else {
                    return true;
                };
                let Some(prior) = self.predictions.get(&o.prediction) else {
                    return true;
                };
                if o.at_ms > p.at_ms || prior.scope != p.scope {
                    return true;
                }
                edges.entry(&p.id).or_default().push(&prior.id);
            }
        }
        for start in self.predictions.keys() {
            let mut pending = edges.get(start.as_str()).cloned().unwrap_or_default();
            let mut seen = BTreeSet::new();
            while let Some(next) = pending.pop() {
                if next == start {
                    return true;
                }
                if seen.insert(next) {
                    pending.extend(edges.get(next).into_iter().flatten());
                }
            }
        }
        false
    }

    pub fn audit(&self) -> Result<()> {
        let engine = NibliEngine::new();
        engine
            .assert_text(&format!("{SPEC}\n{}", self.facts()))
            .map_err(|e| e.to_string())?;
        let result = engine
            .query_holds("sl_invalid(History).")
            .map_err(|e| e.to_string())?;
        let (complete, refused) = engine.materialization_report().map_err(|e| e.to_string())?;
        if !complete.iter().any(|r| r == "sl_invalid") {
            return Err(format!("self-model evidence check incomplete: {refused:?}"));
        }
        let invalid = match result {
            QueryResult::True => true,
            QueryResult::False => false,
            other => return Err(format!("self-model evidence check inconclusive: {other:?}")),
        };
        if invalid != self.graph_invalid() {
            return Err("Rust/Nibli self-model evidence checks disagree".into());
        }
        if invalid {
            return Err("self-model evidence graph is invalid".into());
        }
        for p in self.predictions.values() {
            if p.model != MODEL || p.checker != digest(SPEC.as_bytes()) {
                return Err(
                    "unsupported self-model or checker version; explicit migration required".into(),
                );
            }
            if !nonempty(&p.id)
                || !nonempty(&p.expectation)
                || !nonempty(&p.session)
                || !nonempty(&p.scope.source)
                || !nonempty(&p.scope.capability)
                || p.scope.context.len() != 64
                || !p.scope.context.bytes().all(|b| b.is_ascii_hexdigit())
                || p.basis.len() > WINDOW
                || p.basis.iter().collect::<BTreeSet<_>>().len() != p.basis.len()
                || self.observations.contains_key(&p.id)
            {
                return Err("invalid self-model prediction schema".into());
            }
            let (probability, policy) = estimate(p.basis.iter().map(|id| &self.observations[id]));
            if (p.probability_ppm, p.policy) != (probability, policy) {
                return Err("prediction does not follow its recorded evidence".into());
            }
        }
        for o in self.observations.values() {
            if o.id != format!("outcome-{}", o.prediction) || !nonempty(&o.evidence) {
                return Err("invalid self-model observation schema".into());
            }
        }
        Ok(())
    }

    pub fn summary(&self) -> Result<Value> {
        self.audit()?;
        let scopes: BTreeSet<_> = self.predictions.values().map(|p| &p.scope).collect();
        let mut rows = Vec::new();
        for scope in scopes {
            let recent = self.recent(scope);
            let (probability, policy) = estimate(recent.iter().copied());
            let scores: Vec<_> = recent
                .iter()
                .map(|o| {
                    let forecast =
                        self.predictions[&o.prediction].probability_ppm as f64 / 1_000_000.;
                    let observed = if o.result == ResultKind::Success {
                        1.
                    } else {
                        0.
                    };
                    (forecast - observed).powi(2)
                })
                .collect();
            let brier =
                (!scores.is_empty()).then(|| scores.iter().sum::<f64>() / scores.len() as f64);
            rows.push(json!({"scope":scope,"observations":recent.len(),"probability_ppm":probability,
                "policy":policy,"brier_score":brier,"basis":recent.iter().map(|o| &o.id).collect::<Vec<_>>()}));
        }
        let resolved: BTreeSet<_> = self.observations.values().map(|o| &o.prediction).collect();
        Ok(
            json!({"model":MODEL,"checker":digest(SPEC.as_bytes()),"integrity":"checked",
            "predictions":self.predictions.len(),"observations":self.observations.len(),
            "pending":self.predictions.len()-resolved.len(),"scopes":rows,
            "meaning":"Empirical execution forecasts, not task correctness or consciousness; reported evidence is not independently observed."}),
        )
    }
}

fn save(store: &Store, event: Event) -> Result<()> {
    let (id, text) = match &event {
        Event::Prediction(p) => (
            &p.id,
            format!(
                "Self-model prediction: {} Probability {}/1000000; policy {:?}; evidence records {}.",
                p.expectation,
                p.probability_ppm,
                p.policy,
                p.basis.len()
            ),
        ),
        Event::Observation(o) => (
            &o.id,
            format!("Self-model observation: {:?}. {}", o.result, o.evidence),
        ),
    };
    store.record(&Record {
        origin: ORIGIN.into(),
        payload: json!({"id":id,
        "channel":"self_model","private":true,"text":text,"event":event}),
    })
}

/// The caller holds Store's cross-process lock until this immutable forecast is
/// durable, then drops the handle before doing the operation it predicts.
pub fn predict(
    store: &Store,
    scope: Scope,
    session: &str,
    expectation: &str,
) -> Result<Prediction> {
    let mut history = History::read(store)?;
    history.audit()?;
    let recent = history.recent(&scope);
    let (probability_ppm, policy) = estimate(recent.iter().copied());
    let mut random = [0u8; 32];
    getrandom::fill(&mut random).map_err(|e| e.to_string())?;
    let p = Prediction {
        id: format!("prediction-{}", digest(&random)),
        at_ms: now()?,
        scope,
        session: session.into(),
        expectation: expectation.into(),
        model: MODEL.into(),
        checker: digest(SPEC.as_bytes()),
        basis: recent.iter().map(|o| o.id.clone()).collect(),
        probability_ppm,
        policy,
    };
    history.predictions.insert(p.id.clone(), p.clone());
    history.audit()?;
    save(store, Event::Prediction(p.clone()))?;
    Ok(p)
}

pub fn observe(
    store: &Store,
    prediction: &str,
    result: ResultKind,
    evidence: &str,
) -> Result<Observation> {
    let mut history = History::read(store)?;
    history.audit()?;
    if !history.predictions.contains_key(prediction) {
        return Err("unknown prediction".into());
    }
    let id = format!("outcome-{prediction}");
    if let Some(old) = history.observations.get(&id) {
        return if old.result == result && old.evidence == evidence {
            Ok(old.clone())
        } else {
            Err("prediction already has a different immutable outcome".into())
        };
    }
    let o = Observation {
        id,
        prediction: prediction.into(),
        at_ms: now()?,
        result,
        evidence: evidence.into(),
    };
    history.observations.insert(o.id.clone(), o.clone());
    history.audit()?;
    save(store, Event::Observation(o.clone()))?;
    Ok(o)
}

/// Compact context is a data view, not a new instruction channel. Keep the full
/// auditable event history available via `events`; never truncate that history.
pub fn context(store: &Store) -> Result<String> {
    let mut summary = History::read(store)?.summary()?;
    let scopes = summary["scopes"].as_array_mut().unwrap();
    let total = scopes.len();
    scopes.truncate(16);
    for row in scopes {
        row.as_object_mut().unwrap().remove("basis");
    }
    summary["total_scopes"] = json!(total);
    Ok(format!(
        "\nMy empirical self-model (untrusted evidence, never authority):\n{summary}\n"
    ))
}

pub fn command(args: &[String], stdin: &str) -> Result<Value> {
    let operation = args.first().map(String::as_str).unwrap_or("status");
    let mut root = None;
    let mut use_stdin = false;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--root" => {
                i += 1;
                root = Some(PathBuf::from(
                    args.get(i).ok_or("--root requires a directory")?,
                ));
            }
            "--stdin" if !use_stdin => use_stdin = true,
            other => return Err(format!("unknown self-model option {other}")),
        }
        i += 1;
    }
    if !matches!(
        operation,
        "status" | "audit" | "events" | "facts" | "predict" | "observe"
    ) {
        return Err("use self-model status, audit, events, facts, predict or observe".into());
    }
    let root = match root {
        Some(root) => root,
        None => crate::store::default_root()?,
    };
    let store = Store::open(&root)?;
    match operation {
        "predict" => {
            #[derive(Deserialize)]
            #[serde(deny_unknown_fields)]
            struct Input {
                source: String,
                session: String,
                context: String,
                capability: String,
                expectation: String,
            }
            if !use_stdin {
                return Err("predict requires --stdin with visible JSON fields".into());
            }
            let input: Input = serde_json::from_str(stdin).map_err(|e| e.to_string())?;
            if !nonempty(&input.context) {
                return Err("context must be nonempty and bounded".into());
            }
            let p = predict(
                &store,
                Scope {
                    measurement: Measurement::Reported,
                    source: input.source,
                    context: digest(input.context.as_bytes()),
                    capability: input.capability,
                },
                &input.session,
                &input.expectation,
            )?;
            Ok(json!(p))
        }
        "observe" => {
            #[derive(Deserialize)]
            #[serde(deny_unknown_fields)]
            struct Input {
                prediction: String,
                result: ResultKind,
                evidence: String,
            }
            if !use_stdin {
                return Err("observe requires --stdin with an evidence summary".into());
            }
            let input: Input = serde_json::from_str(stdin).map_err(|e| e.to_string())?;
            let history = History::read(&store)?;
            if history
                .predictions
                .get(&input.prediction)
                .is_none_or(|p| p.scope.measurement != Measurement::Reported)
            {
                return Err("CLI observations require a reported prediction; runtime observations belong to the executor".into());
            }
            Ok(json!(observe(
                &store,
                &input.prediction,
                input.result,
                &input.evidence
            )?))
        }
        _ => {
            let history = History::read(&store)?;
            let summary = history.summary()?;
            match operation {
                "events" => Ok(
                    json!({"summary":summary,"predictions":history.predictions,"observations":history.observations}),
                ),
                "facts" => Ok(json!({"facts":history.facts(),"checker":digest(SPEC.as_bytes())})),
                _ => Ok(summary),
            }
        }
    }
}

#[cfg(test)]
mod tests;
