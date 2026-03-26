//! Native nibli engine library: calls gerna/smuni/logji directly as Rust crates.
//! No WASM, no Wasmtime — full stack traces for debugging.
#![allow(dead_code)]

use std::cell::RefCell;
use std::collections::HashSet;
use std::path::Path;

use nibli_protocol::{
    LogicalTerm as LogicalTermJson, ProofRule as ProofRuleJson, ProofStep as ProofStepJson,
    ProofTrace as ProofTraceJson,
};
use nibli_store::{NibliStore, StoredLogicBuffer, StoredLogicNode, StoredLogicalTerm};

pub use nibli_types::logic::{
    FactSummary as EngineFactSummary, LogicalTerm as EngineLogicalTerm,
    WitnessBinding as EngineWitnessBinding,
};

use nibli_types::error::NibliError as PipelineError;
use nibli_types::logic as logji_logic;

// ═══════════════════════════════════════════════════════════════════════
// ERROR FORMATTING
// ═══════════════════════════════════════════════════════════════════════

fn format_error(e: &PipelineError) -> String {
    match e {
        PipelineError::Syntax(d) => {
            format!("[Syntax Error] line {}:{}: {}", d.line, d.column, d.message)
        }
        PipelineError::Semantic(m) => format!("[Semantic Error] {}", m),
        PipelineError::Reasoning(m) => format!("[Reasoning Error] {}", m),
        PipelineError::Backend((k, m)) => format!("[Backend Error] {} — {}", k, m),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// PROOF TRACE CONVERSION (WIT types → nibli-protocol wire types)
// ═══════════════════════════════════════════════════════════════════════

fn term_to_json(term: &logji_logic::LogicalTerm) -> LogicalTermJson {
    match term {
        logji_logic::LogicalTerm::Constant(s) => LogicalTermJson {
            kind: "constant".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Variable(s) => LogicalTermJson {
            kind: "variable".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Description(s) => LogicalTermJson {
            kind: "description".to_string(),
            value: Some(s.clone()),
            number: None,
        },
        logji_logic::LogicalTerm::Number(n) => LogicalTermJson {
            kind: "number".to_string(),
            value: None,
            number: Some(*n),
        },
        logji_logic::LogicalTerm::Unspecified => LogicalTermJson {
            kind: "unspecified".to_string(),
            value: None,
            number: None,
        },
    }
}

fn rule_to_json(rule: &logji_logic::ProofRule) -> ProofRuleJson {
    match rule {
        logji_logic::ProofRule::Conjunction => ProofRuleJson::Conjunction,
        logji_logic::ProofRule::DisjunctionCheck(s) => {
            ProofRuleJson::DisjunctionCheck { detail: s.clone() }
        }
        logji_logic::ProofRule::DisjunctionIntro(s) => {
            ProofRuleJson::DisjunctionIntro { side: s.clone() }
        }
        logji_logic::ProofRule::Negation => ProofRuleJson::Negation,
        logji_logic::ProofRule::ModalPassthrough(s) => {
            ProofRuleJson::ModalPassthrough { kind: s.clone() }
        }
        logji_logic::ProofRule::ExistsWitness((var, term)) => ProofRuleJson::ExistsWitness {
            var: var.clone(),
            term: term_to_json(term),
        },
        logji_logic::ProofRule::ExistsFailed => ProofRuleJson::ExistsFailed,
        logji_logic::ProofRule::ForallVacuous => ProofRuleJson::ForallVacuous,
        logji_logic::ProofRule::ForallVerified(entities) => ProofRuleJson::ForallVerified {
            entities: entities.iter().map(term_to_json).collect(),
        },
        logji_logic::ProofRule::ForallCounterexample(term) => ProofRuleJson::ForallCounterexample {
            entity: term_to_json(term),
        },
        logji_logic::ProofRule::CountResult((expected, actual)) => ProofRuleJson::CountResult {
            expected: *expected,
            actual: *actual,
        },
        logji_logic::ProofRule::PredicateCheck((method, detail)) => ProofRuleJson::PredicateCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::ComputeCheck((method, detail)) => ProofRuleJson::ComputeCheck {
            method: method.clone(),
            detail: detail.clone(),
        },
        logji_logic::ProofRule::Asserted(fact) => ProofRuleJson::Asserted { fact: fact.clone() },
        logji_logic::ProofRule::Derived((label, fact)) => ProofRuleJson::Derived {
            label: label.clone(),
            fact: fact.clone(),
        },
        logji_logic::ProofRule::ProofRef(fact) => ProofRuleJson::ProofRef { fact: fact.clone() },
    }
}

fn proof_trace_to_wire(trace: &logji_logic::ProofTrace) -> ProofTraceJson {
    ProofTraceJson {
        steps: trace
            .steps
            .iter()
            .map(|step| ProofStepJson {
                rule: rule_to_json(&step.rule),
                holds: step.holds,
                children: step.children.clone(),
            })
            .collect(),
        root: trace.root,
    }
}

pub fn display_term(term: &EngineLogicalTerm) -> String {
    term_to_json(term).trace_display()
}

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════
// STORE CONVERSIONS: logji <-> nibli-store mirror types
// ═══════════════════════════════════════════════════════════════════════

fn term_to_stored(t: &logji_logic::LogicalTerm) -> StoredLogicalTerm {
    match t {
        logji_logic::LogicalTerm::Variable(v) => StoredLogicalTerm::Variable(v.clone()),
        logji_logic::LogicalTerm::Constant(c) => StoredLogicalTerm::Constant(c.clone()),
        logji_logic::LogicalTerm::Description(d) => StoredLogicalTerm::Description(d.clone()),
        logji_logic::LogicalTerm::Unspecified => StoredLogicalTerm::Unspecified,
        logji_logic::LogicalTerm::Number(n) => StoredLogicalTerm::Number(*n),
    }
}

fn term_from_stored(t: &StoredLogicalTerm) -> logji_logic::LogicalTerm {
    match t {
        StoredLogicalTerm::Variable(v) => logji_logic::LogicalTerm::Variable(v.clone()),
        StoredLogicalTerm::Constant(c) => logji_logic::LogicalTerm::Constant(c.clone()),
        StoredLogicalTerm::Description(d) => logji_logic::LogicalTerm::Description(d.clone()),
        StoredLogicalTerm::Unspecified => logji_logic::LogicalTerm::Unspecified,
        StoredLogicalTerm::Number(n) => logji_logic::LogicalTerm::Number(*n),
    }
}

fn node_to_stored(n: &logji_logic::LogicNode) -> StoredLogicNode {
    match n {
        logji_logic::LogicNode::Predicate((rel, args)) => {
            StoredLogicNode::Predicate(rel.clone(), args.iter().map(term_to_stored).collect())
        }
        logji_logic::LogicNode::ComputeNode((rel, args)) => {
            StoredLogicNode::ComputeNode(rel.clone(), args.iter().map(term_to_stored).collect())
        }
        logji_logic::LogicNode::AndNode((l, r)) => StoredLogicNode::And(*l, *r),
        logji_logic::LogicNode::OrNode((l, r)) => StoredLogicNode::Or(*l, *r),
        logji_logic::LogicNode::NotNode(id) => StoredLogicNode::Not(*id),
        logji_logic::LogicNode::ExistsNode((v, b)) => StoredLogicNode::Exists(v.clone(), *b),
        logji_logic::LogicNode::ForAllNode((v, b)) => StoredLogicNode::ForAll(v.clone(), *b),
        logji_logic::LogicNode::PastNode(id) => StoredLogicNode::Past(*id),
        logji_logic::LogicNode::PresentNode(id) => StoredLogicNode::Present(*id),
        logji_logic::LogicNode::FutureNode(id) => StoredLogicNode::Future(*id),
        logji_logic::LogicNode::ObligatoryNode(id) => StoredLogicNode::Obligatory(*id),
        logji_logic::LogicNode::PermittedNode(id) => StoredLogicNode::Permitted(*id),
        logji_logic::LogicNode::CountNode((v, c, b)) => StoredLogicNode::Count(v.clone(), *c, *b),
    }
}

fn node_from_stored(n: &StoredLogicNode) -> logji_logic::LogicNode {
    match n {
        StoredLogicNode::Predicate(rel, args) => logji_logic::LogicNode::Predicate((
            rel.clone(),
            args.iter().map(term_from_stored).collect(),
        )),
        StoredLogicNode::ComputeNode(rel, args) => logji_logic::LogicNode::ComputeNode((
            rel.clone(),
            args.iter().map(term_from_stored).collect(),
        )),
        StoredLogicNode::And(l, r) => logji_logic::LogicNode::AndNode((*l, *r)),
        StoredLogicNode::Or(l, r) => logji_logic::LogicNode::OrNode((*l, *r)),
        StoredLogicNode::Not(id) => logji_logic::LogicNode::NotNode(*id),
        StoredLogicNode::Exists(v, b) => logji_logic::LogicNode::ExistsNode((v.clone(), *b)),
        StoredLogicNode::ForAll(v, b) => logji_logic::LogicNode::ForAllNode((v.clone(), *b)),
        StoredLogicNode::Past(id) => logji_logic::LogicNode::PastNode(*id),
        StoredLogicNode::Present(id) => logji_logic::LogicNode::PresentNode(*id),
        StoredLogicNode::Future(id) => logji_logic::LogicNode::FutureNode(*id),
        StoredLogicNode::Obligatory(id) => logji_logic::LogicNode::ObligatoryNode(*id),
        StoredLogicNode::Permitted(id) => logji_logic::LogicNode::PermittedNode(*id),
        StoredLogicNode::Count(v, c, b) => logji_logic::LogicNode::CountNode((v.clone(), *c, *b)),
    }
}

fn buf_to_stored(buf: &logji_logic::LogicBuffer) -> StoredLogicBuffer {
    StoredLogicBuffer {
        nodes: buf.nodes.iter().map(node_to_stored).collect(),
        roots: buf.roots.clone(),
    }
}

fn buf_from_stored(stored: &StoredLogicBuffer) -> logji_logic::LogicBuffer {
    logji_logic::LogicBuffer {
        nodes: stored.nodes.iter().map(node_from_stored).collect(),
        roots: stored.roots.clone(),
    }
}

// ═══════════════════════════════════════════════════════════════════════
// ENGINE WRAPPER
// ═══════════════════════════════════════════════════════════════════════

pub struct NibliEngine {
    kb: logji::KnowledgeBase,
    compute_predicates: HashSet<String>,
    store: RefCell<Option<NibliStore>>,
}

impl Default for NibliEngine {
    fn default() -> Self {
        Self::new()
    }
}

impl NibliEngine {
    fn default_compute_predicates() -> HashSet<String> {
        let mut preds = HashSet::new();
        preds.insert("pilji".to_string());
        preds.insert("sumji".to_string());
        preds.insert("dilcu".to_string());
        preds
    }

    /// Create an engine without persistence (existing behavior).
    pub fn new() -> Self {
        println!("Native engine ready");
        NibliEngine {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(None),
        }
    }

    /// Create an engine with disk persistence at the given path.
    /// Replays all persisted facts into the in-memory KB on open.
    pub fn open(db_path: &Path) -> Result<Self, String> {
        let store = NibliStore::open(db_path, "local".to_string())
            .map_err(|e| format!("Store error: {e}"))?;
        let engine = NibliEngine {
            kb: logji::KnowledgeBase::new(),
            compute_predicates: Self::default_compute_predicates(),
            store: RefCell::new(Some(store)),
        };
        engine.replay_from_store()?;
        println!("Native engine ready (persistent: {})", db_path.display());
        Ok(engine)
    }

    /// Replay all persisted facts into the in-memory KB.
    fn replay_from_store(&self) -> Result<(), String> {
        let store = self.store.borrow();
        let store = store.as_ref().unwrap();
        let facts = store
            .all_active_facts()
            .map_err(|e| format!("Store error: {e}"))?;
        for fact in &facts {
            let stored_buf: StoredLogicBuffer = postcard::from_bytes(&fact.payload)
                .map_err(|e| format!("Deserialize error: {e}"))?;
            let buf = buf_from_stored(&stored_buf);
            self.kb
                .assert_fact_with_id(buf, fact.label.clone(), fact.id)
                .map_err(|e| format!("Replay error: {e}"))?;
        }
        if !facts.is_empty() {
            println!("[Store] Replayed {} persisted facts", facts.len());
        }
        Ok(())
    }

    /// Validate Lojban text without asserting — returns Ok if it parses and compiles.
    pub fn validate(&self, text: &str) -> Result<(), String> {
        self.compile_text(text)
            .map(|_| ())
            .map_err(|e| format_error(&e))
    }

    pub fn register_compute_predicate(&mut self, name: String) {
        self.compute_predicates.insert(name);
    }

    fn compile_text(&self, input: &str) -> Result<logji_logic::LogicBuffer, PipelineError> {
        let parse_result = gerna::parse_text_native(input.to_string())?;

        if parse_result.buffer.roots.is_empty() && !parse_result.errors.is_empty() {
            let first = &parse_result.errors[0];
            return Err(PipelineError::Syntax(nibli_types::error::SyntaxDetail {
                message: parse_result
                    .errors
                    .iter()
                    .map(|e| e.message.clone())
                    .collect::<Vec<_>>()
                    .join("; "),
                line: first.line,
                column: first.column,
            }));
        }

        if !parse_result.errors.is_empty() {
            let warnings: Vec<String> = parse_result
                .errors
                .iter()
                .map(|e| e.message.clone())
                .collect();
            return Err(PipelineError::Syntax(nibli_types::error::SyntaxDetail {
                message: format!(
                    "Assertion aborted: {} sentence(s) failed to parse: {}",
                    warnings.len(),
                    warnings.join("; ")
                ),
                line: 0,
                column: 0,
            }));
        }

        let mut buf = smuni::compile_from_gerna_ast(parse_result.buffer)?;
        logji::transform_compute_nodes(&mut buf, &self.compute_predicates);
        Ok(buf)
    }

    /// Reset the knowledge base, clearing all facts and rules.
    pub fn reset(&self) {
        self.kb.reset().ok();
        if let Ok(mut store) = self.store.try_borrow_mut()
            && let Some(s) = store.as_mut()
        {
            let _ = s.clear();
        }
    }

    pub fn assert_text(&self, text: &str) -> Result<u64, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let label = text.to_string();
        let mut store = self
            .store
            .try_borrow_mut()
            .map_err(|_| "Store error: persistence state is already borrowed".to_string())?;

        if let Some(s) = store.as_mut() {
            let payload = postcard::to_allocvec(&buf_to_stored(&buf))
                .map_err(|e| format!("Serialize error: {e}"))?;
            let fact_id = s.next_fact_id().map_err(|e| format!("Store error: {e}"))?;
            s.insert_fact(fact_id, label.clone(), payload)
                .map_err(|e| format!("Store error: {e}"))?;
            if let Err(err) = self.kb.assert_fact_with_id(buf, label, fact_id) {
                return match s.delete_fact(fact_id) {
                    Ok(()) => Err(err),
                    Err(rollback_err) => Err(format!("{err}; rollback failed: {rollback_err}")),
                };
            }
            Ok(fact_id)
        } else {
            self.kb
                .assert_fact(buf, label)
                .map_err(|e| format_error(&e))
        }
    }

    pub fn assert_fact_direct(
        &self,
        relation: String,
        args: Vec<EngineLogicalTerm>,
    ) -> Result<u64, String> {
        let label = format!(":assert {}", relation);
        let buf = logji_logic::LogicBuffer {
            nodes: vec![logji_logic::LogicNode::Predicate((relation, args))],
            roots: vec![0],
        };
        self.kb
            .assert_fact(buf, label)
            .map_err(|e| format_error(&e))
    }

    pub fn query_text_with_proof(&self, text: &str) -> Result<(bool, String, String), String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let (holds, trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| format_error(&e))?;
        let wire = proof_trace_to_wire(&trace);
        let formatted = wire.to_pretty_text();
        let json = wire.to_json();
        Ok((holds, formatted, json))
    }

    /// Check if a Lojban query holds in the KB (simple boolean check).
    pub fn query_holds(&self, text: &str) -> Result<bool, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        let (holds, _trace) = self
            .kb
            .query_entailment_with_proof(buf)
            .map_err(|e| format_error(&e))?;
        Ok(holds)
    }

    pub fn query_find_text(&self, text: &str) -> Result<Vec<Vec<EngineWitnessBinding>>, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        self.kb.query_find(buf).map_err(|e| format_error(&e))
    }

    pub fn compile_debug(&self, text: &str) -> Result<String, String> {
        let buf = self.compile_text(text).map_err(|e| format_error(&e))?;
        Ok(logji::repr::debug_logic(&buf))
    }

    pub fn list_facts(&self) -> Result<Vec<EngineFactSummary>, String> {
        self.kb.list_facts().map_err(|e| format_error(&e))
    }

    pub fn retract_fact(&self, id: u64) -> Result<(), String> {
        self.kb.retract_fact(id).map_err(|e| format_error(&e))
    }
}

#[cfg(test)]
mod tests {
    use super::NibliEngine;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn temp_db_path(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("nibli_engine_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{name}.redb"))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    #[test]
    fn persistent_assert_does_not_mutate_kb_when_store_is_unavailable() {
        let path = temp_db_path("atomic_assert_store_busy");
        cleanup(&path);

        let engine = NibliEngine::open(&path).expect("Persistent engine should open");
        let _borrow = engine.store.borrow();

        let err = engine
            .assert_text("lo gerku cu barda")
            .expect_err("Store borrow conflict should abort assertion");
        assert!(
            err.contains("Store error"),
            "Expected store error, got: {err}"
        );
        assert!(
            !engine
                .query_holds("lo gerku cu barda")
                .expect("Query should still run"),
            "Failed persistent assertions must not leak into the live KB"
        );

        drop(_borrow);
        let store = engine.store.borrow();
        let facts = store
            .as_ref()
            .unwrap()
            .all_active_facts()
            .expect("Store should remain empty");
        assert!(
            facts.is_empty(),
            "Failed persistent assertions must not leak into the store"
        );

        drop(store);
        cleanup(&path);
    }
}
