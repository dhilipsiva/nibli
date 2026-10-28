//! Exhaustive finite-domain verification of structurally extracted Rust.
//! The trusted normalizer supplies syntax, never execution results. This is
//! independent of Lean, but is not a proof of the extractor or this engine.
use nibli_session::CoreSession;
use nibli_types::logic::LogicalTerm;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

pub const SPEC: &str = include_str!("../spec/rust_verdicts.nibli");
const INPUTS: &[(&str, usize)] = &[
    ("rv_argument", 3),
    ("rv_barrier", 4),
    ("rv_case", 2),
    ("rv_construct", 3),
    ("rv_construct_expr", 4),
    ("rv_distinct", 2),
    ("rv_enum", 2),
    ("rv_equal_expr", 4),
    ("rv_field_value", 3),
    ("rv_guard_test", 3),
    ("rv_guard_join", 3),
    ("rv_guard_start", 1),
    ("rv_input", 3),
    ("rv_literal", 3),
    ("rv_not_expr", 3),
    ("rv_path", 4),
    ("rv_payload_expr", 4),
    ("rv_tag_expr", 3),
    ("rv_trap", 4),
    ("rv_type", 2),
];

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Fact {
    pub relation: String,
    pub arguments: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Case {
    pub id: String,
    pub root: String,
    pub inputs: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Path {
    pub id: String,
    pub root: String,
    pub kind: String,
    pub detail: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Bundle {
    pub schema: u32,
    pub domain: Vec<String>,
    pub cases: Vec<Case>,
    pub paths: Vec<Path>,
    pub locations: BTreeMap<String, serde_json::Value>,
    pub facts: Vec<Fact>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Verified,
    Counterexample,
    Inconclusive,
}

impl Status {
    pub fn exit_code(&self) -> i32 {
        match self {
            Self::Verified => 0,
            Self::Counterexample => 1,
            Self::Inconclusive => 2,
        }
    }
}

#[derive(Serialize)]
pub struct CaseReport {
    pub case: Case,
    pub status: Status,
    pub actual: Vec<String>,
    pub expected: Vec<String>,
    pub selected_paths: Vec<String>,
    /// Source-linked observations, replayed against the complete Nibli model.
    /// These are not kernel-checked proof objects or asserted premises.
    pub trace: EvaluationTrace,
}

#[derive(Serialize)]
pub struct Observation {
    pub query: String,
    pub holds: bool,
}

#[derive(Serialize)]
pub struct EvaluationTrace {
    pub structural_facts: Vec<usize>,
    pub observations: Vec<Observation>,
}

#[derive(Serialize)]
pub struct Report {
    pub schema: u32,
    pub status: Status,
    pub verification_kind: &'static str,
    pub self_check_equivalence_verified: bool,
    pub evidence_kind: &'static str,
    pub complete_relations: Vec<String>,
    pub engine_version: &'static str,
    pub input_values: usize,
    pub expected_executions: usize,
    pub facts: usize,
    pub elapsed_seconds: f64,
    pub cases: Vec<CaseReport>,
    pub locations: BTreeMap<String, serde_json::Value>,
}

fn quote(text: &str) -> String {
    serde_json::to_string(text).expect("string serialization")
}
fn query(relation: &str, args: &[&str]) -> String {
    format!(
        "{relation}({}).",
        args.iter().map(|s| quote(s)).collect::<Vec<_>>().join(",")
    )
}

impl Bundle {
    /// Structural completeness is checked before allocating a knowledge base.
    /// In particular, omitting a case cannot shrink the claimed input universe.
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != 1
            || self.domain.is_empty()
            || self.domain.len() > 256
            || self.facts.len() > 200_000
        {
            return Err("unsupported schema or bundle size".into());
        }
        let domain: BTreeSet<_> = self.domain.iter().cloned().collect();
        if domain.len() != self.domain.len() {
            return Err("duplicate domain value".into());
        }
        let mut facts = BTreeSet::new();
        for f in &self.facts {
            if !INPUTS.contains(&(f.relation.as_str(), f.arguments.len())) {
                return Err(format!("unadmitted input predicate/arity: {}", f.relation));
            }
            if f.arguments.iter().any(|a| {
                a.is_empty() || a.len() > 1024 || !a.is_ascii() || a.chars().any(char::is_control)
            }) {
                return Err("invalid structural constant".into());
            }
            if !facts.insert((f.relation.clone(), f.arguments.clone())) {
                return Err("duplicate input fact".into());
            }
        }
        let rows = |rel: &str| -> BTreeSet<Vec<String>> {
            facts
                .iter()
                .filter(|(r, _)| r == rel)
                .map(|(_, a)| a.clone())
                .collect()
        };
        let declared: BTreeSet<_> = rows("rv_type")
            .into_iter()
            .filter(|a| a[1] == "QueryResult")
            .map(|a| a[0].clone())
            .collect();
        if domain != declared {
            return Err("domain differs from extracted type facts".into());
        }
        let mut required = BTreeSet::new();
        for a in &domain {
            required.insert(("not".to_owned(), vec![a.clone()]));
            for b in &domain {
                for root in ["and", "or"] {
                    required.insert((root.to_owned(), vec![a.clone(), b.clone()]));
                }
            }
        }
        let observed: BTreeSet<_> = self
            .cases
            .iter()
            .map(|c| (c.root.clone(), c.inputs.clone()))
            .collect();
        let ids: BTreeSet<_> = self.cases.iter().map(|c| &c.id).collect();
        if observed != required
            || observed.len() != self.cases.len()
            || ids.len() != self.cases.len()
        {
            return Err("case coverage is missing, duplicated, or outside the domain".into());
        }
        let case_rows = self
            .cases
            .iter()
            .map(|c| vec![c.id.clone(), c.root.clone()])
            .collect();
        let input_rows = self
            .cases
            .iter()
            .flat_map(|c| {
                c.inputs
                    .iter()
                    .enumerate()
                    .map(|(i, v)| vec![c.id.clone(), i.to_string(), v.clone()])
            })
            .collect();
        if rows("rv_case") != case_rows || rows("rv_input") != input_rows {
            return Err("case/input facts differ from inventory".into());
        }
        let path_ids: BTreeSet<_> = self.paths.iter().map(|p| &p.id).collect();
        if path_ids.len() != self.paths.len() {
            return Err("duplicate path id".into());
        }
        for (kind, rel) in [
            ("return", "rv_path"),
            ("blocked", "rv_barrier"),
            ("panic", "rv_trap"),
        ] {
            let declared: BTreeSet<_> = self
                .paths
                .iter()
                .filter(|p| p.kind == kind)
                .map(|p| (p.id.clone(), p.root.clone(), p.detail.clone()))
                .collect();
            let actual: BTreeSet<_> = rows(rel)
                .into_iter()
                .map(|r| (r[0].clone(), r[1].clone(), r[3].clone()))
                .collect();
            if declared != actual {
                return Err("path facts differ from inventory".into());
            }
        }
        if self.paths.iter().any(|p| {
            !["return", "blocked", "panic"].contains(&p.kind.as_str())
                || !["and", "or", "not"].contains(&p.root.as_str())
                || !self.locations.contains_key(&p.id)
        }) {
            return Err("unsupported path or missing source location".into());
        }
        // Missing definitions cannot make an inconvenient path disappear.
        let mut nodes = BTreeMap::new();
        let mut guards = BTreeMap::new();
        let mut paths = BTreeMap::new();
        for fact in &self.facts {
            let table = match fact.relation.as_str() {
                "rv_argument" | "rv_literal" | "rv_tag_expr" | "rv_payload_expr"
                | "rv_construct_expr" | "rv_equal_expr" | "rv_not_expr" => &mut nodes,
                "rv_guard_start" | "rv_guard_test" | "rv_guard_join" => &mut guards,
                "rv_path" | "rv_barrier" | "rv_trap" => &mut paths,
                _ => continue,
            };
            if table.insert(fact.arguments[0].as_str(), fact).is_some() {
                return Err("duplicate structural definition".into());
            }
        }
        for fact in nodes.values() {
            let a = &fact.arguments;
            if !["and", "or", "not"].contains(&a[1].as_str()) {
                return Err("unknown expression root".into());
            }
            if fact.relation == "rv_argument" && !(a[2] == "0" || a[2] == "1" && a[1] != "not") {
                return Err("invalid argument index".into());
            }
            for &index in dependencies(&fact.relation) {
                let dependency = nodes
                    .get(a[index].as_str())
                    .ok_or("missing expression dependency")?;
                if dependency.arguments[1] != a[1] {
                    return Err("cross-root expression dependency".into());
                }
            }
        }
        for fact in guards.values() {
            let a = &fact.arguments;
            if fact.relation == "rv_guard_test" && !nodes.contains_key(a[1].as_str()) {
                return Err("missing guard expression".into());
            }
            if fact.relation == "rv_guard_join"
                && (!guards.contains_key(a[1].as_str()) || !guards.contains_key(a[2].as_str()))
            {
                return Err("missing guard dependency".into());
            }
        }
        for fact in paths.values() {
            let a = &fact.arguments;
            if !guards.contains_key(a[2].as_str()) {
                return Err("missing path guard".into());
            }
            if fact.relation == "rv_path"
                && nodes
                    .get(a[3].as_str())
                    .is_none_or(|n| n.arguments[1] != a[1])
            {
                return Err("missing or cross-root return expression".into());
            }
        }
        // Iterative graph removal avoids recursive validation on hostile input.
        let mut remaining: BTreeMap<_, BTreeSet<_>> = nodes
            .values()
            .chain(guards.values())
            .map(|f| {
                (
                    f.arguments[0].as_str(),
                    dependencies(&f.relation)
                        .iter()
                        .map(|&i| f.arguments[i].as_str())
                        .collect(),
                )
            })
            .collect();
        if remaining.len() != nodes.len() + guards.len() {
            return Err("ambiguous expression/guard id".into());
        }
        while !remaining.is_empty() {
            let ready: BTreeSet<_> = remaining
                .iter()
                .filter(|(_, d)| d.is_empty())
                .map(|(&id, _)| id)
                .collect();
            if ready.is_empty() {
                return Err("cyclic structural definitions".into());
            }
            remaining.retain(|id, _| !ready.contains(id));
            for deps in remaining.values_mut() {
                deps.retain(|id| !ready.contains(id));
            }
        }
        Ok(())
    }

    pub fn facts_text(&self) -> String {
        self.facts
            .iter()
            .map(|f| {
                query(
                    &f.relation,
                    &f.arguments.iter().map(String::as_str).collect::<Vec<_>>(),
                ) + "\n"
            })
            .collect()
    }
}

fn dependencies(relation: &str) -> &'static [usize] {
    match relation {
        "rv_path" => &[2, 3],
        "rv_barrier" | "rv_trap" => &[2],
        "rv_guard_join" => &[1, 2],
        "rv_guard_test" => &[1],
        "rv_equal_expr" => &[2, 3],
        "rv_payload_expr" | "rv_tag_expr" | "rv_not_expr" => &[2],
        "rv_construct_expr" => &[3],
        _ => &[],
    }
}

pub fn session(bundle: &Bundle) -> Result<CoreSession, String> {
    bundle.validate()?;
    load(bundle)
}

fn load(bundle: &Bundle) -> Result<CoreSession, String> {
    let compiler = CoreSession::new();
    let mut compiled = Vec::new();
    for statement in nibli_kr::parser::parse_statements(SPEC).map_err(|e| format!("{e:?}"))? {
        let text = &SPEC[statement.span];
        compiled.push((
            compiler
                .compile_text(text)
                .map_err(|e| format!("{text}: {e:?}"))?,
            text.to_owned(),
        ));
    }
    for fact in &bundle.facts {
        let args = fact
            .arguments
            .iter()
            .cloned()
            .map(LogicalTerm::Constant)
            .collect::<Vec<_>>();
        let buffer = nibli_semantics::compile_injected_fact(&fact.relation, &args)
            .map_err(|e| format!("{e:?}"))?;
        compiled.push((
            buffer,
            query(
                &fact.relation,
                &fact
                    .arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            ),
        ));
    }
    let (kb, _) =
        nibli_reason::KnowledgeBase::from_compiled_batch(compiled).map_err(|e| format!("{e:?}"))?;
    let session = CoreSession::with_kb(kb);
    session.set_strict(true);
    session
        .set_existential_import(false)
        .map_err(|e| format!("{e:?}"))?;
    session
        .set_max_chain_depth(256)
        .map_err(|e| format!("{e:?}"))?;
    Ok(session)
}

/// A syntactic dependency slice, not an evaluation or a proof. It includes
/// every expression/guard dependency of the selected path. No derived result
/// is inserted; Nibli must reconstruct that path's execution from these facts.
fn structural_slice(bundle: &Bundle, case: &str, paths: &[String]) -> BTreeSet<usize> {
    let mut selected = BTreeSet::new();
    let mut pending = paths.to_vec();
    let mut visited = BTreeSet::new();
    for (i, fact) in bundle.facts.iter().enumerate() {
        if [
            "rv_type",
            "rv_enum",
            "rv_distinct",
            "rv_field_value",
            "rv_construct",
        ]
        .contains(&fact.relation.as_str())
            || (["rv_case", "rv_input"].contains(&fact.relation.as_str())
                && fact.arguments[0] == case)
        {
            selected.insert(i);
        }
    }
    while let Some(id) = pending.pop() {
        if !visited.insert(id.clone()) {
            continue;
        }
        for (i, fact) in bundle
            .facts
            .iter()
            .enumerate()
            .filter(|(_, f)| f.arguments[0] == id)
        {
            let a = &fact.arguments;
            selected.insert(i);
            pending.extend(dependencies(&fact.relation).iter().map(|&n| a[n].clone()));
        }
    }
    selected
}

pub fn verify(bundle: &Bundle) -> Result<Report, String> {
    let started = Instant::now();
    let session = session(bundle)?;
    eprintln!(
        "Loaded {} structural facts in {:.3}s",
        bundle.facts.len(),
        started.elapsed().as_secs_f64()
    );
    // Request saturation before enumerating positive paths. Otherwise the
    // ordinary backward search may explore exponentially many incompatible
    // syntactic branches before it reaches a negated completeness condition.
    session
        .query_text(&format!("~{}", query("rv_case_ok", &[&bundle.cases[0].id])))
        .map_err(|e| format!("materialization request: {e:?}"))?;
    let (complete_relations, refused) = session
        .materialization_report()
        .map_err(|e| format!("{e:?}"))?;
    if !refused.is_empty() {
        return Err(format!("incomplete model: {refused:?}"));
    }
    eprintln!(
        "Materialized {} relations in {:.3}s",
        complete_relations.len(),
        started.elapsed().as_secs_f64()
    );
    let mut expression_values = BTreeSet::from(["bool:true".to_owned(), "bool:false".to_owned()]);
    for fact in &bundle.facts {
        match fact.relation.as_str() {
            "rv_type" => {
                expression_values.insert(fact.arguments[0].clone());
            }
            "rv_enum" => {
                expression_values.extend(fact.arguments.iter().cloned());
            }
            "rv_literal" => {
                expression_values.insert(fact.arguments[2].clone());
            }
            _ => {}
        }
    }
    let holds = |relation: &str, args: &[&str]| {
        crate::static_check::verdict(&session, &query(relation, args))
    };
    let mut reports = Vec::new();
    for (index, case) in bundle.cases.iter().enumerate() {
        if index % 25 == 0 {
            eprintln!("Checking case {index}/{}", bundle.cases.len());
        }
        // This query requests the complete stratified cone, including failures.
        let checked = holds("rv_case_ok", &[&case.id])?;
        let mut actual = Vec::new();
        let mut expected = Vec::new();
        for value in &bundle.domain {
            if holds("rv_return", &[&case.id, value])? {
                actual.push(value.clone());
            }
            if holds("rv_expected", &[&case.id, value])? {
                expected.push(value.clone());
            }
        }
        let blocked = holds("rv_blocked", &[&case.id])?;
        let panicked = holds("rv_panicked", &[&case.id])?;
        let mismatch = holds("rv_mismatch", &[&case.id])?;
        let conflict = holds("rv_conflict", &[&case.id])?;
        let mut status =
            if blocked || conflict || expected.len() != 1 || (!panicked && actual.len() != 1) {
                Status::Inconclusive
            } else if panicked || mismatch {
                Status::Counterexample
            } else if checked && actual == expected {
                Status::Verified
            } else {
                Status::Inconclusive
            };
        let mut selected_paths = Vec::new();
        for path in bundle.paths.iter().filter(|p| p.root == case.root) {
            let rel = match path.kind.as_str() {
                "return" => "rv_path_hit",
                "panic" => "rv_trap_hit",
                _ => "rv_barrier_hit",
            };
            if holds(rel, &[&case.id, &path.id])? {
                selected_paths.push(path.id.clone());
            }
        }
        if selected_paths.len() != 1 {
            status = Status::Inconclusive;
        }
        let structural_facts = structural_slice(bundle, &case.id, &selected_paths);
        let mut observations = Vec::new();
        // Record the complete execution decision, including false candidates.
        // Every observation is queried from Nibli, never used as an assertion.
        for relation in [
            "rv_case_ok",
            "rv_blocked",
            "rv_panicked",
            "rv_mismatch",
            "rv_conflict",
        ] {
            observations.push(Observation {
                query: query(relation, &[&case.id]),
                holds: holds(relation, &[&case.id])?,
            });
        }
        for value in &bundle.domain {
            for relation in ["rv_return", "rv_expected"] {
                observations.push(Observation {
                    query: query(relation, &[&case.id, value]),
                    holds: holds(relation, &[&case.id, value])?,
                });
            }
        }
        for path in bundle.paths.iter().filter(|p| p.root == case.root) {
            let relation = match path.kind.as_str() {
                "return" => "rv_path_hit",
                "panic" => "rv_trap_hit",
                _ => "rv_barrier_hit",
            };
            observations.push(Observation {
                query: query(relation, &[&case.id, &path.id]),
                holds: holds(relation, &[&case.id, &path.id])?,
            });
        }
        for &index in &structural_facts {
            let fact = &bundle.facts[index];
            let id = &fact.arguments[0];
            if ["rv_guard_start", "rv_guard_join", "rv_guard_test"]
                .contains(&fact.relation.as_str())
            {
                let ok = holds("rv_guard_ok", &[&case.id, id])?;
                observations.push(Observation {
                    query: query("rv_guard_ok", &[&case.id, id]),
                    holds: ok,
                });
                if !ok {
                    status = Status::Inconclusive;
                }
            } else if [
                "rv_argument",
                "rv_literal",
                "rv_tag_expr",
                "rv_payload_expr",
                "rv_construct_expr",
                "rv_equal_expr",
                "rv_not_expr",
            ]
            .contains(&fact.relation.as_str())
            {
                let mut values = 0;
                for value in &expression_values {
                    let ok = holds("rv_eval", &[&case.id, id, value])?;
                    if ok {
                        values += 1;
                        observations.push(Observation {
                            query: query("rv_eval", &[&case.id, id, value]),
                            holds: ok,
                        });
                    }
                }
                if values != 1 {
                    status = Status::Inconclusive;
                }
            }
        }
        reports.push(CaseReport {
            case: case.clone(),
            status,
            actual,
            expected,
            selected_paths,
            trace: EvaluationTrace {
                structural_facts: structural_facts.into_iter().collect(),
                observations,
            },
        });
    }
    let status = if reports.iter().any(|r| r.status == Status::Counterexample) {
        Status::Counterexample
    } else if reports.iter().any(|r| r.status == Status::Inconclusive) {
        Status::Inconclusive
    } else {
        Status::Verified
    };
    Ok(Report {
        schema: 1,
        status,
        verification_kind: "exhaustive_finite_domain",
        self_check_equivalence_verified: false,
        evidence_kind: "replayable_model_observations",
        complete_relations,
        engine_version: env!("CARGO_PKG_VERSION"),
        input_values: bundle.domain.len(),
        expected_executions: bundle.cases.len(),
        facts: bundle.facts.len(),
        elapsed_seconds: started.elapsed().as_secs_f64(),
        cases: reports,
        locations: bundle.locations.clone(),
    })
}

/// Replay all observations and coverage checks from structural inputs. This
/// trusts the same Nibli evaluator, not a separate proof kernel. Reports do not
/// become premises, and missing/tampered observations fail comparison.
pub fn replay(bundle: &Bundle, expected: &serde_json::Value) -> Result<Report, String> {
    let report = verify(bundle)?;
    let mut observed = serde_json::to_value(&report).map_err(|e| e.to_string())?;
    let mut expected = expected.clone();
    for value in [&mut observed, &mut expected] {
        value
            .as_object_mut()
            .ok_or("expected a report object")?
            .remove("elapsed_seconds");
    }
    if observed != expected {
        return Err("replayed Nibli observations differ from the saved report".into());
    }
    Ok(report)
}
