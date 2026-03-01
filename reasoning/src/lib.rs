//! Reasoning engine: FOL assertion and query via egglog e-graph equality saturation.
//!
//! This is the core inference component of Nibli. It maintains a stateful knowledge
//! base backed by an egglog e-graph and provides:
//!
//! - **Fact assertion** — Ground predicates asserted as `(IsTrue (Pred "rel" ...))` facts.
//!   Universal quantifiers compile to native egglog rewrite rules with O(K) hash-join matching.
//! - **Entailment queries** — Recursive formula checking via [`check_formula_holds`] with
//!   structural rewrites (commutativity, De Morgan, double negation) and inference rules
//!   (conjunction elimination/introduction, disjunctive syllogism, modus ponens/tollens).
//! - **Proof traces** — [`check_formula_holds_traced`] builds a proof tree recording which
//!   rule/axiom was applied at each step (15 proof rule variants). Multi-hop derivation
//!   provenance traces derived facts through universal rule chains via backward-chaining.
//! - **Witness extraction** — [`find_witnesses`] returns all satisfying entity bindings for
//!   existential variables.
//! - **Compute dispatch** — `ComputeNode` predicates are forwarded to the host-provided
//!   `compute-backend` WIT interface for external evaluation.
//!
//! The knowledge base uses `RefCell` (not `Mutex`) — single-threaded WASI, no global state.

#[allow(warnings)]
mod bindings;

use crate::bindings::exports::lojban::nesy::reasoning::{Guest, GuestKnowledgeBase};
use crate::bindings::lojban::nesy::error_types::NibliError;
use crate::bindings::lojban::nesy::logic_types::{
    FactSummary, LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofStep, ProofTrace,
    WitnessBinding,
};
use egglog::EGraph;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

// ─── Knowledge Base State ────────────────────────────────────────

/// Registry entry for a SkolemFn created by native rule compilation.
/// Used by query-side existential checking to generate SkolemFn witness terms.
#[derive(Clone)]
struct SkolemFnEntry {
    base_name: String,
    dep_count: usize,
}

/// Prefix used for dependent Skolem placeholder variables.
/// A dependent Skolem is an ∃ variable nested under a ∀.
const SKDEP_PREFIX: &str = "__skdep__";

/// Records the structure of a compiled universal rule for backward-chaining provenance.
/// Templates use bare pattern variables (e.g., `x__v0`) instead of bound values.
#[derive(Clone)]
struct UniversalRuleRecord {
    /// Human-readable label, e.g. "gerku → danlu"
    label: String,
    /// S-expression templates for the rule's conditions (without `(IsTrue ...)` wrapper).
    condition_templates: Vec<String>,
    /// S-expression templates for the rule's conclusions (without `(IsTrue ...)` wrapper).
    conclusion_templates: Vec<String>,
    /// Pattern variable names used in templates, e.g. ["x__v0"].
    pattern_var_names: Vec<String>,
}

/// Registry entry for a single asserted fact, supporting retraction and rebuild.
#[derive(Clone)]
struct FactRecord {
    id: u64,
    buffer: LogicBuffer,
    label: String,
    retracted: bool,
}

/// All mutable KB state behind a single RefCell.
struct KnowledgeBaseInner {
    egraph: EGraph,
    skolem_counter: usize,
    known_entities: HashSet<String>,
    /// Known description terms (from `le` gadri), tracked separately for InDomain.
    known_descriptions: HashSet<String>,
    known_rules: HashSet<String>,
    skolem_fn_registry: Vec<SkolemFnEntry>,
    /// Ground facts directly asserted by the user (for provenance tracking).
    asserted_sexps: HashSet<String>,
    /// Compiled universal rule templates (for backward-chaining provenance).
    universal_rules: Vec<UniversalRuleRecord>,
    /// Monotonically increasing fact ID counter.
    fact_counter: u64,
    /// Registry of all asserted facts (including retracted ones, for ID stability).
    fact_registry: Vec<FactRecord>,
    /// Suppresses diagnostic prints during rebuild replay.
    rebuilding: bool,
}

impl KnowledgeBaseInner {
    fn new() -> Self {
        Self {
            egraph: make_fresh_egraph(),
            skolem_counter: 0,
            known_entities: HashSet::new(),
            known_descriptions: HashSet::new(),
            known_rules: HashSet::new(),
            skolem_fn_registry: Vec::new(),
            asserted_sexps: HashSet::new(),
            universal_rules: Vec::new(),
            fact_counter: 0,
            fact_registry: Vec::new(),
            rebuilding: false,
        }
    }

    fn reset(&mut self) {
        self.egraph = make_fresh_egraph();
        self.skolem_counter = 0;
        self.known_entities.clear();
        self.known_descriptions.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
        self.asserted_sexps.clear();
        self.universal_rules.clear();
        self.fact_counter = 0;
        self.fact_registry.clear();
        self.rebuilding = false;
    }

    fn fresh_fact_id(&mut self) -> u64 {
        let id = self.fact_counter;
        self.fact_counter += 1;
        id
    }

    fn fresh_skolem(&mut self) -> String {
        let sk = format!("sk_{}", self.skolem_counter);
        self.skolem_counter += 1;
        sk
    }

    fn note_entity(&mut self, name: &str) {
        let is_new = self.known_entities.insert(name.to_string());
        if is_new {
            let cmd = format!("(InDomain (Const \"{}\"))", name);
            self.egraph.parse_and_run_program(None, &cmd).ok();
        }
    }

    fn note_description(&mut self, name: &str) {
        let is_new = self.known_descriptions.insert(name.to_string());
        if is_new {
            let cmd = format!("(InDomain (Desc \"{}\"))", name);
            self.egraph.parse_and_run_program(None, &cmd).ok();
        }
    }

    /// Return all known domain members as (s-expression, LogicalTerm) pairs.
    /// Includes both Const entities and Desc description terms.
    fn all_domain_members(&self) -> Vec<(String, LogicalTerm)> {
        let mut members = Vec::new();
        for e in &self.known_entities {
            members.push((
                format!("(Const \"{}\")", e),
                LogicalTerm::Constant(e.clone()),
            ));
        }
        for d in &self.known_descriptions {
            members.push((
                format!("(Desc \"{}\")", d),
                LogicalTerm::Description(d.clone()),
            ));
        }
        members
    }
}

/// The WIT-exported resource type.
/// wit-bindgen generates `&self` for methods, so RefCell provides mutability.
pub struct KnowledgeBase {
    inner: RefCell<KnowledgeBaseInner>,
}

/// The egglog schema and inference rules, shared between init and reset.
const SCHEMA: &str = r#"
    ;; ═══════════════════════════════════════════════════
    ;; Lojban NeSy Engine — FOL Schema & Rules
    ;; Phase 7: Native egglog rules for universals
    ;; ═══════════════════════════════════════════════════

    ;; Atomic Terms
    ;; SkolemFn: dependent Skolem witness — (SkolemFn "sk_N" dep_term)
    ;; For single dependency: dep_term is a plain Term (Var in rules, Const in ground)
    ;; For multi-dependency: dep_term is nested DepPair, e.g. (DepPair dep0 dep1)
    (datatype Term
        (Var String)
        (Const String)
        (Desc String)
        (Zoe)
        (Num i64)
        (SkolemFn String Term)
        (DepPair Term Term)
    )

    ;; Argument list (Cons/Nil encoding)
    (datatype TermList
        (Nil)
        (Cons Term TermList)
    )

    ;; Logical Formulae
    (datatype Formula
        (Pred String TermList)
        (And Formula Formula)
        (Or Formula Formula)
        (Not Formula)
        (Exists String Formula)
        (ForAll String Formula)
        (Implies Formula Formula)
        (Past Formula)
        (Present Formula)
        (Future Formula)
    )

    ;; Ground-truth relation: "this formula is known true"
    (relation IsTrue (Formula))
    ;; Domain tracking: "this term is a known entity"
    (relation InDomain (Term))

    ;; ── Structural rewrites ──────────────────────────
    ;; Commutativity
    (rewrite (And a b) (And b a))
    (rewrite (Or a b) (Or b a))

    ;; Associativity
    (rewrite (And (And a b) c) (And a (And b c)))
    (rewrite (Or (Or a b) c) (Or a (Or b c)))

    ;; Double negation elimination
    (rewrite (Not (Not a)) a)

    ;; De Morgan's laws
    (rewrite (Not (And a b)) (Or (Not a) (Not b)))
    (rewrite (Not (Or a b)) (And (Not a) (Not b)))

    ;; Material conditional (bidirectional)
    (rewrite (Implies a b) (Or (Not a) b))
    (rewrite (Or (Not a) b) (Implies a b))

    ;; ── Inference rules ──────────────────────────────
    ;; Conjunction elimination
    (rule ((IsTrue (And a b))) ((IsTrue a) (IsTrue b)))

    ;; Disjunctive syllogism
    (rule ((IsTrue (Or a b)) (IsTrue (Not a))) ((IsTrue b)))
    (rule ((IsTrue (Or a b)) (IsTrue (Not b))) ((IsTrue a)))

    ;; Modus ponens via implication
    (rule ((IsTrue (Implies a b)) (IsTrue a)) ((IsTrue b)))

    ;; Modus tollens
    (rule ((IsTrue (Implies a b)) (IsTrue (Not b))) ((IsTrue (Not a))))

    ;; ∀-distribution over ∧
    (rule ((IsTrue (ForAll v (And A B))))
          ((IsTrue (And (ForAll v A) (ForAll v B)))))

    ;; ── Conjunction introduction (guarded) ─────────────
    ;; Helper: extract InDomain entities from predicate argument positions.
    ;; Only fires for terms already in InDomain (named entities, Skolem constants),
    ;; so (Zoe) and other non-entity terms are naturally excluded.
    (relation PredHasEntity (Formula Term))

    ;; Position x1
    (rule ((IsTrue (Pred r (Cons t rest))) (InDomain t))
          ((PredHasEntity (Pred r (Cons t rest)) t)))

    ;; Position x2
    (rule ((IsTrue (Pred r (Cons a1 (Cons t rest)))) (InDomain t))
          ((PredHasEntity (Pred r (Cons a1 (Cons t rest))) t)))

    ;; Position x3
    (rule ((IsTrue (Pred r (Cons a1 (Cons a2 (Cons t rest))))) (InDomain t))
          ((PredHasEntity (Pred r (Cons a1 (Cons a2 (Cons t rest)))) t)))

    ;; Introduction: derive And(A,B) when both A,B are atomic Pred forms
    ;; sharing at least one InDomain entity (any argument position).
    (rule ((IsTrue (Pred r1 args1)) (IsTrue (Pred r2 args2))
           (PredHasEntity (Pred r1 args1) t) (PredHasEntity (Pred r2 args2) t))
          ((IsTrue (And (Pred r1 args1) (Pred r2 args2)))))

    ;; ── Temporal conjunction elimination ─────────────
    ;; Past(A ∧ B) → Past(A) ∧ Past(B)
    (rule ((IsTrue (Past (And a b)))) ((IsTrue (Past a)) (IsTrue (Past b))))
    ;; Present(A ∧ B) → Present(A) ∧ Present(B)
    (rule ((IsTrue (Present (And a b)))) ((IsTrue (Present a)) (IsTrue (Present b))))
    ;; Future(A ∧ B) → Future(A) ∧ Future(B)
    (rule ((IsTrue (Future (And a b)))) ((IsTrue (Future a)) (IsTrue (Future b))))

    ;; ── Temporal entity extraction (for conjunction introduction under tense) ──
    ;; Past predicates
    (rule ((IsTrue (Past (Pred r (Cons t rest)))) (InDomain t))
          ((PredHasEntity (Past (Pred r (Cons t rest))) t)))
    (rule ((IsTrue (Past (Pred r (Cons a1 (Cons t rest))))) (InDomain t))
          ((PredHasEntity (Past (Pred r (Cons a1 (Cons t rest)))) t)))
    (rule ((IsTrue (Past (Pred r (Cons a1 (Cons a2 (Cons t rest)))))) (InDomain t))
          ((PredHasEntity (Past (Pred r (Cons a1 (Cons a2 (Cons t rest))))) t)))
    ;; Present predicates
    (rule ((IsTrue (Present (Pred r (Cons t rest)))) (InDomain t))
          ((PredHasEntity (Present (Pred r (Cons t rest))) t)))
    (rule ((IsTrue (Present (Pred r (Cons a1 (Cons t rest))))) (InDomain t))
          ((PredHasEntity (Present (Pred r (Cons a1 (Cons t rest)))) t)))
    (rule ((IsTrue (Present (Pred r (Cons a1 (Cons a2 (Cons t rest)))))) (InDomain t))
          ((PredHasEntity (Present (Pred r (Cons a1 (Cons a2 (Cons t rest))))) t)))
    ;; Future predicates
    (rule ((IsTrue (Future (Pred r (Cons t rest)))) (InDomain t))
          ((PredHasEntity (Future (Pred r (Cons t rest))) t)))
    (rule ((IsTrue (Future (Pred r (Cons a1 (Cons t rest))))) (InDomain t))
          ((PredHasEntity (Future (Pred r (Cons a1 (Cons t rest)))) t)))
    (rule ((IsTrue (Future (Pred r (Cons a1 (Cons a2 (Cons t rest)))))) (InDomain t))
          ((PredHasEntity (Future (Pred r (Cons a1 (Cons a2 (Cons t rest))))) t)))

    ;; Temporal conjunction introduction (same tense)
    (rule ((IsTrue (Past (Pred r1 args1))) (IsTrue (Past (Pred r2 args2)))
           (PredHasEntity (Past (Pred r1 args1)) t) (PredHasEntity (Past (Pred r2 args2)) t))
          ((IsTrue (Past (And (Pred r1 args1) (Pred r2 args2))))))
    (rule ((IsTrue (Present (Pred r1 args1))) (IsTrue (Present (Pred r2 args2)))
           (PredHasEntity (Present (Pred r1 args1)) t) (PredHasEntity (Present (Pred r2 args2)) t))
          ((IsTrue (Present (And (Pred r1 args1) (Pred r2 args2))))))
    (rule ((IsTrue (Future (Pred r1 args1))) (IsTrue (Future (Pred r2 args2)))
           (PredHasEntity (Future (Pred r1 args1)) t) (PredHasEntity (Future (Pred r2 args2)) t))
          ((IsTrue (Future (And (Pred r1 args1) (Pred r2 args2))))))
"#;

/// Create a fresh EGraph with the schema loaded.
fn make_fresh_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, SCHEMA)
        .expect("Failed to load FOL schema and rules");
    egraph
}

/// Build an egglog SkolemFn s-expression from a base name and dependency terms.
/// Single dep: `(SkolemFn "sk_N" dep0)` — backward compatible.
/// Multi dep: `(SkolemFn "sk_N" (DepPair dep0 (DepPair dep1 dep2)))` — right-nested pairs.
fn build_skolem_fn_sexp(base_name: &str, pattern_var_names: &[String]) -> String {
    let dep_term = match pattern_var_names.len() {
        0 => "(Zoe)".to_string(),
        1 => pattern_var_names[0].clone(),
        _ => {
            // Right-nested DepPair encoding: [a, b, c] → (DepPair a (DepPair b c))
            let mut acc = pattern_var_names.last().unwrap().clone();
            for dep in pattern_var_names[..pattern_var_names.len() - 1].iter().rev() {
                acc = format!("(DepPair {} {})", dep, acc);
            }
            acc
        }
    };
    format!("(SkolemFn \"{}\" {})", base_name, dep_term)
}

/// Build a ground SkolemFn s-expression with a Const entity argument.
/// Generate cartesian product of s-expression strings with given arity.
fn cartesian_product(entities: &[String], dep_count: usize) -> Vec<Vec<String>> {
    if dep_count == 0 {
        return vec![vec![]];
    }
    let mut result: Vec<Vec<String>> = vec![vec![]];
    for _ in 0..dep_count {
        let mut next = Vec::new();
        for combo in &result {
            for entity in entities {
                let mut extended = combo.clone();
                extended.push(entity.clone());
                next.push(extended);
            }
        }
        result = next;
    }
    result
}

// ─── WIT Export Implementation ────────────────────────────────────

struct ReasoningComponent;

impl Guest for ReasoningComponent {
    type KnowledgeBase = KnowledgeBase;
}

/// Process a logic buffer into the egglog e-graph without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
fn process_assertion(inner: &mut KnowledgeBaseInner, logic: &LogicBuffer) -> Result<(), String> {
    for &root_id in &logic.roots {
        // Phase 1: Collect existential variables for Skolemization.
        let mut skolem_subs = HashMap::new();
        let mut enclosing_universals = Vec::new();
        collect_exists_for_skolem(
            logic,
            root_id,
            &mut skolem_subs,
            &mut enclosing_universals,
            &mut inner.skolem_counter,
        );

        // Log Skolem substitutions (suppressed during rebuild)
        if !inner.rebuilding && !skolem_subs.is_empty() {
            let mapping: Vec<String> = skolem_subs
                .iter()
                .map(|(v, sk)| {
                    if sk.starts_with(SKDEP_PREFIX) {
                        format!("{} ↦ {}(∀-dependent)", v, &sk[SKDEP_PREFIX.len()..])
                    } else {
                        format!("{} ↦ {}", v, sk)
                    }
                })
                .collect();
            println!(
                "[Skolem] {} variable(s) → {}",
                skolem_subs.len(),
                mapping.join(", ")
            );
        }

        // Phase 2: Dispatch based on formula structure
        let is_forall = matches!(
            &logic.nodes[root_id as usize],
            LogicNode::ForAllNode(_)
        );

        if is_forall {
            // ═══ NATIVE RULE PATH ═══
            for sk in skolem_subs.values() {
                if !sk.starts_with(SKDEP_PREFIX) {
                    inner.note_entity(sk);
                }
            }
            collect_and_note_constants(logic, root_id, inner);
            compile_forall_to_rule(logic, root_id, &skolem_subs, inner)?;
        } else {
            // ═══ GROUND FORMULA PATH ═══
            for sk in skolem_subs.values() {
                if !sk.starts_with(SKDEP_PREFIX) {
                    inner.note_entity(sk);
                }
            }
            collect_and_note_constants(logic, root_id, inner);

            let raw_subs: HashMap<String, String> = skolem_subs
                .iter()
                .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
                .map(|(k, v)| (k.clone(), format!("(Const \"{}\")", v)))
                .collect();
            let sexp = reconstruct_sexp_with_subs(logic, root_id, &raw_subs);
            // Record as user-asserted fact for provenance tracking
            inner.asserted_sexps.insert(sexp.clone());
            let command = format!("(IsTrue {})", sexp);
            inner
                .egraph
                .parse_and_run_program(None, &command)
                .map_err(|e| format!("Failed to assert fact: {}", e))?;
        }

        // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
        generate_count_extra_witnesses(logic, root_id, &skolem_subs, inner);

        // Run rules to fixpoint
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
    }

    Ok(())
}

/// Internal methods that return `Result<_, String>` for use by both the WIT boundary and tests.
impl KnowledgeBase {
    /// Assert FOL facts from a logic buffer into the egglog e-graph.
    /// Stores the buffer in the fact registry and returns a unique fact ID.
    fn assert_fact_inner(&self, logic: LogicBuffer, label: String) -> Result<u64, String> {
        let mut inner = self.inner.borrow_mut();
        let id = inner.fresh_fact_id();
        inner.fact_registry.push(FactRecord {
            id,
            buffer: logic.clone(),
            label,
            retracted: false,
        });
        process_assertion(&mut inner, &logic)?;
        Ok(id)
    }

    /// Retract a previously asserted fact by its ID. Triggers a full KB rebuild
    /// from remaining (non-retracted) facts.
    fn retract_fact_inner(&self, id: u64) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();
        let record = inner.fact_registry.iter_mut().find(|r| r.id == id);
        match record {
            None => Err(format!("Fact #{} not found", id)),
            Some(r) if r.retracted => Ok(()), // idempotent
            Some(r) => {
                r.retracted = true;
                Self::rebuild_inner(&mut inner)
            }
        }
    }

    /// Rebuild the egraph from all non-retracted facts.
    /// Preserves fact_registry and fact_counter; resets all derived state.
    fn rebuild_inner(inner: &mut KnowledgeBaseInner) -> Result<(), String> {
        // Reset egraph and derived state
        inner.egraph = make_fresh_egraph();
        inner.skolem_counter = 0;
        inner.known_entities.clear();
        inner.known_descriptions.clear();
        inner.known_rules.clear();
        inner.skolem_fn_registry.clear();
        inner.asserted_sexps.clear();
        inner.universal_rules.clear();

        // Collect non-retracted buffers (clone to avoid borrow conflict)
        let buffers: Vec<LogicBuffer> = inner
            .fact_registry
            .iter()
            .filter(|r| !r.retracted)
            .map(|r| r.buffer.clone())
            .collect();

        // Replay with diagnostic output suppressed
        inner.rebuilding = true;
        for buf in &buffers {
            process_assertion(inner, buf)?;
        }
        inner.rebuilding = false;
        Ok(())
    }

    /// List all active (non-retracted) facts in the KB.
    fn list_facts_inner(&self) -> Result<Vec<FactSummary>, String> {
        let inner = self.inner.borrow();
        Ok(inner
            .fact_registry
            .iter()
            .filter(|r| !r.retracted)
            .map(|r| FactSummary {
                id: r.id,
                label: r.label.clone(),
                root_count: r.buffer.roots.len() as u32,
            })
            .collect())
    }

    /// Check whether all root formulas in the logic buffer are entailed by the KB.
    /// Runs egglog saturation (up to 100 iterations) before checking.
    fn query_entailment_inner(&self, logic: LogicBuffer) -> Result<bool, String> {
        let mut inner = self.inner.borrow_mut();
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        for &root_id in &logic.roots {
            let subs = HashMap::new();
            if !check_formula_holds(&logic, root_id, &subs, &mut inner, None)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Find all satisfying binding sets for existential variables in the query formula.
    /// Returns one `Vec<WitnessBinding>` per satisfying assignment.
    fn query_find_inner(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        let mut inner = self.inner.borrow_mut();
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        let mut result_sets: Option<Vec<Vec<(String, String)>>> = None;
        for &root_id in &logic.roots {
            let subs = HashMap::new();
            let witnesses = find_witnesses(&logic, root_id, &subs, &mut inner, None)?;
            match result_sets {
                None => result_sets = Some(witnesses),
                Some(ref _prev) => {
                    if witnesses.is_empty() {
                        return Ok(vec![]);
                    }
                    result_sets = Some(witnesses);
                }
            }
        }
        let binding_sets = result_sets.unwrap_or_default();
        Ok(binding_sets
            .into_iter()
            .map(|bindings| {
                bindings
                    .into_iter()
                    .map(|(var, sexp)| WitnessBinding {
                        variable: var,
                        term: parse_sexp_to_term(&sexp),
                    })
                    .collect()
            })
            .collect())
    }

    fn query_entailment_with_proof_inner(
        &self,
        logic: LogicBuffer,
    ) -> Result<(bool, ProofTrace), String> {
        let mut inner = self.inner.borrow_mut();
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        let mut steps: Vec<ProofStep> = Vec::new();
        let mut root_children: Vec<u32> = Vec::new();
        let mut all_hold = true;
        for &root_id in &logic.roots {
            let subs = HashMap::new();
            let (holds, step_idx) =
                check_formula_holds_traced(&logic, root_id, &subs, &mut inner, &mut steps, None)?;
            root_children.push(step_idx);
            if !holds {
                all_hold = false;
            }
        }
        let root = if root_children.len() == 1 {
            root_children[0]
        } else {
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: all_hold,
                children: root_children,
            });
            idx
        };
        Ok((all_hold, ProofTrace { steps, root }))
    }
}

impl GuestKnowledgeBase for KnowledgeBase {
    fn new() -> Self {
        KnowledgeBase {
            inner: RefCell::new(KnowledgeBaseInner::new()),
        }
    }

    fn assert_fact(&self, logic: LogicBuffer, label: String) -> Result<u64, NibliError> {
        self.assert_fact_inner(logic, label)
            .map_err(NibliError::Reasoning)
    }

    fn query_entailment(&self, logic: LogicBuffer) -> Result<bool, NibliError> {
        self.query_entailment_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    fn query_find(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, NibliError> {
        self.query_find_inner(logic).map_err(NibliError::Reasoning)
    }

    fn query_entailment_with_proof(
        &self,
        logic: LogicBuffer,
    ) -> Result<(bool, ProofTrace), NibliError> {
        self.query_entailment_with_proof_inner(logic)
            .map_err(NibliError::Reasoning)
    }

    fn reset(&self) -> Result<(), NibliError> {
        self.inner.borrow_mut().reset();
        Ok(())
    }

    fn retract_fact(&self, id: u64) -> Result<(), NibliError> {
        self.retract_fact_inner(id)
            .map_err(NibliError::Reasoning)
    }

    fn list_facts(&self) -> Result<Vec<FactSummary>, NibliError> {
        self.list_facts_inner().map_err(NibliError::Reasoning)
    }
}

// ─── Numeric Comparison Helpers ──────────────────────────────────

/// Extract an i64 numeric value from a LogicalTerm.
/// Handles direct Number literals and Variables substituted to "(Num N)" form.
fn extract_num_value(term: &LogicalTerm, subs: &HashMap<String, String>) -> Option<i64> {
    match term {
        LogicalTerm::Number(n) => Some(*n as i64),
        LogicalTerm::Variable(v) => {
            let s = subs.get(v.as_str())?;
            s.strip_prefix("(Num ")?.strip_suffix(')')?.parse::<i64>().ok()
        }
        _ => None,
    }
}

/// Evaluate zmadu/mleca/dunli when first two args are Num.
/// Returns None for non-numeric args (fall through to standard egglog check).
fn try_numeric_comparison(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Option<bool> {
    let a = extract_num_value(args.get(0)?, subs)?;
    let b = extract_num_value(args.get(1)?, subs)?;
    match rel {
        "zmadu" => Some(a > b),
        "mleca" => Some(a < b),
        "dunli" => Some(a == b),
        _ => None,
    }
}

/// Evaluate arithmetic predicates (pilji/sumji/dilcu) when all three args are Num.
/// Place structure: x1 = op(x2, x3).
fn try_arithmetic_evaluation(
    rel: &str,
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Option<bool> {
    let x1 = extract_num_value(args.get(0)?, subs)?;
    let x2 = extract_num_value(args.get(1)?, subs)?;
    let x3 = extract_num_value(args.get(2)?, subs)?;
    match rel {
        "pilji" => Some(x1 == x2 * x3),
        "sumji" => Some(x1 == x2 + x3),
        "dilcu" => {
            if x3 == 0 {
                return Some(false);
            }
            Some(x1 == x2 / x3)
        }
        _ => None,
    }
}

// ─── Compute Dispatch Helpers ────────────────────────────────────

/// Parse an egglog s-expression substitution back to a LogicalTerm.
/// Parse an egglog s-expression string back into a [`LogicalTerm`] for witness extraction.
/// Recognizes `(Const "...")`, `(Desc "...")`, `(Num ...)`, `(Zoe)` patterns.
fn parse_sexp_to_term(sexp: &str) -> LogicalTerm {
    if let Some(name) = sexp
        .strip_prefix("(Const \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Constant(name.to_string())
    } else if let Some(n) = sexp
        .strip_prefix("(Num ")
        .and_then(|s| s.strip_suffix(')'))
    {
        LogicalTerm::Number(n.parse::<f64>().unwrap_or(0.0))
    } else if let Some(name) = sexp
        .strip_prefix("(Desc \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Description(name.to_string())
    } else if sexp == "(Zoe)" {
        LogicalTerm::Unspecified
    } else if let Some(name) = sexp
        .strip_prefix("(Var \"")
        .and_then(|s| s.strip_suffix("\")"))
    {
        LogicalTerm::Variable(name.to_string())
    } else {
        LogicalTerm::Variable(sexp.to_string())
    }
}

/// Resolve variable substitutions in args back to concrete LogicalTerm values
/// for passing to the compute backend.
fn resolve_args_for_dispatch(
    args: &[LogicalTerm],
    subs: &HashMap<String, String>,
) -> Vec<LogicalTerm> {
    args.iter()
        .map(|a| match a {
            LogicalTerm::Variable(v) => {
                if let Some(s) = subs.get(v.as_str()) {
                    parse_sexp_to_term(s)
                } else {
                    a.clone()
                }
            }
            _ => a.clone(),
        })
        .collect()
}

/// Dispatch a compute predicate to the WIT compute-backend import.
/// On native (non-wasm32) targets, returns Err (backend unavailable).
#[cfg(target_arch = "wasm32")]
fn dispatch_to_backend(rel: &str, args: &[LogicalTerm]) -> Result<bool, String> {
    crate::bindings::lojban::nesy::compute_backend::evaluate(rel, args)
        .map_err(|e| format!("{}", e))
}

#[cfg(not(target_arch = "wasm32"))]
fn dispatch_to_backend(_rel: &str, _args: &[LogicalTerm]) -> Result<bool, String> {
    Err("Compute backend unavailable in native mode".to_string())
}

/// Build an egglog s-expression for a ground predicate from resolved args.
/// Returns None if any argument is still a Variable (not fully ground).
/// Output: `(Pred "rel" (Cons (Num 8) (Cons (Num 2) (Cons (Num 3) (Nil)))))`
/// Build an egglog s-expression for a ground predicate: `(Pred "rel" (Const "a") ...)`.
/// Returns `None` if any argument is a non-ground variable (cannot be fully resolved).
fn build_ground_predicate_sexp(rel: &str, resolved_args: &[LogicalTerm]) -> Option<String> {
    for arg in resolved_args {
        if matches!(arg, LogicalTerm::Variable(_)) {
            return None;
        }
    }
    let mut args_str = String::from("(Nil)");
    for arg in resolved_args.iter().rev() {
        let term_str = match arg {
            LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
            LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
            LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
            LogicalTerm::Unspecified => "(Zoe)".to_string(),
            LogicalTerm::Variable(_) => unreachable!(),
        };
        args_str = format!("(Cons {} {})", term_str, args_str);
    }
    Some(format!("(Pred \"{}\" {})", rel, args_str))
}

// ─── Query Decomposition ─────────────────────────────────────────

/// Wrap an s-expression with a temporal operator if a tense context is active.
fn wrap_with_tense(tense: Option<&str>, sexp: &str) -> String {
    match tense {
        Some(t) => format!("({} {})", t, sexp),
        None => sexp.to_string(),
    }
}

/// Recursively check whether a formula (identified by `node_id`) is entailed by the KB.
///
/// Handles all FOL node types: conjunction, disjunction, negation, quantifiers,
/// tense/deontic wrappers, count quantifiers, compute nodes, and predicate leaves.
/// Variable substitutions are threaded through `subs` for universal quantifier instantiation.
/// The `tense` parameter propagates a temporal context (Past/Present/Future) through the
/// formula tree — tense nodes set it, leaf predicates wrap their s-expression with it.
fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
            && check_formula_holds(buffer, *r, subs, inner, tense)?),
        LogicNode::OrNode((l, r)) => {
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let command = format!("(check (IsTrue {}))", wrapped);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => return Ok(true),
                Err(_) => {}
            }
            Ok(check_formula_holds(buffer, *l, subs, inner, tense)?
                || check_formula_holds(buffer, *r, subs, inner, tense)?)
        }
        LogicNode::NotNode(inner_node) => Ok(!check_formula_holds(buffer, *inner_node, subs, inner, tense)?),
        // Temporal nodes: set tense context for inner formula
        LogicNode::PastNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Past")),
        LogicNode::PresentNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Present")),
        LogicNode::FutureNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, Some("Future")),
        // Deontic nodes: remain transparent, pass through current tense
        LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner, tense),
        LogicNode::ExistsNode((v, body)) => {
            // 1. Check if any known domain member (Const or Desc) satisfies the body
            let members = inner.all_domain_members();
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if check_formula_holds(buffer, *body, &new_subs, inner, tense)? {
                    return Ok(true);
                }
            }
            // 2. Try SkolemFn witnesses from the registry
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                // SkolemFn deps can be any domain member
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                let combos = cartesian_product(&dep_sexps, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp);
                    if check_formula_holds(buffer, *body, &new_subs, inner, tense)? {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }
        LogicNode::ForAllNode((v, body)) => {
            let members = inner.all_domain_members();
            if members.is_empty() {
                return Ok(true);
            }
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if !check_formula_holds(buffer, *body, &new_subs, inner, tense)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LogicNode::CountNode((v, count, body)) => {
            let members = inner.all_domain_members();
            let mut satisfying = 0u32;
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if check_formula_holds(buffer, *body, &new_subs, inner, tense)? {
                    satisfying += 1;
                }
            }
            Ok(satisfying == *count)
        }
        LogicNode::Predicate((rel, args)) => {
            // Try numeric comparison short-circuit for zmadu/mleca/dunli (timeless)
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                return Ok(result);
            }
            // Standard egglog check with tense wrapping
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let command = format!("(check (IsTrue {}))", wrapped);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => Ok(true),
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("Check failed") {
                        Ok(false)
                    } else {
                        Err(format!("Reasoning error: {}", msg))
                    }
                }
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // 1. Try WIT dispatch to external compute backend (wasm32 only)
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    // Ingest ground fact into KB for future reasoning
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        let cmd = format!("(IsTrue {})", sexp);
                        inner.egraph.parse_and_run_program(None, &cmd).ok();
                    }
                }
                return Ok(result);
            }
            // 2. Try built-in arithmetic evaluation
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    // Ingest ground fact into KB for future reasoning
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        let cmd = format!("(IsTrue {})", sexp);
                        inner.egraph.parse_and_run_program(None, &cmd).ok();
                    }
                }
                return Ok(result);
            }
            // 3. Fall back to egglog check (already in KB, no ingestion needed)
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => Ok(true),
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("Check failed") {
                        Ok(false)
                    } else {
                        Err(format!("Reasoning error: {}", msg))
                    }
                }
            }
        }
    }
}

// ─── Witness Extraction ──────────────────────────────────────────

/// Find all satisfying binding sets for existential variables in a formula.
/// Returns Vec<Vec<(variable_name, sexp_value)>> — each inner Vec is one
/// complete assignment. Empty outer Vec means no witnesses found.
fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<Vec<Vec<(String, String)>>, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            let mut results = Vec::new();

            // 1. Try all known domain members (Const + Desc) as witnesses
            let members = inner.all_domain_members();
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                let sub_results = find_witnesses(buffer, *body, &new_subs, inner, tense)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), sexp.clone()));
                    results.push(bindings);
                }
            }

            // 2. Try SkolemFn witnesses from the registry
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                let combos = cartesian_product(&dep_sexps, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    let sub_results = find_witnesses(buffer, *body, &new_subs, inner, tense)?;
                    for mut bindings in sub_results {
                        bindings.push((v.clone(), witness_sexp.clone()));
                        results.push(bindings);
                    }
                }
            }

            Ok(results)
        }
        // Temporal nodes: set tense context
        LogicNode::PastNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Past")),
        LogicNode::PresentNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Present")),
        LogicNode::FutureNode(inner_node) => find_witnesses(buffer, *inner_node, subs, inner, Some("Future")),
        LogicNode::AndNode((l, r)) => {
            // Cross-product: for each left binding set, check right with merged subs
            let left_results = find_witnesses(buffer, *l, subs, inner, tense)?;
            let mut results = Vec::new();
            for left_bindings in left_results {
                let mut merged_subs = subs.clone();
                for (k, v) in &left_bindings {
                    merged_subs.insert(k.clone(), v.clone());
                }
                let right_results = find_witnesses(buffer, *r, &merged_subs, inner, tense)?;
                for right_bindings in right_results {
                    let mut combined = left_bindings.clone();
                    combined.extend(right_bindings);
                    results.push(combined);
                }
            }
            Ok(results)
        }
        LogicNode::OrNode((l, r)) => {
            // Union: collect from both sides
            let mut results = find_witnesses(buffer, *l, subs, inner, tense)?;
            results.extend(find_witnesses(buffer, *r, subs, inner, tense)?);
            Ok(results)
        }
        // For all other node types, delegate to boolean check.
        // If the formula holds, return one empty binding set; otherwise empty.
        _ => {
            if check_formula_holds(buffer, node_id, subs, inner, tense)? {
                Ok(vec![vec![]])
            } else {
                Ok(vec![])
            }
        }
    }
}

// ─── Proof Trace Generation ──────────────────────────────────────

// ─── Backward-Chaining Provenance ────────────────────────────────

/// Maximum backward-chaining depth to prevent infinite recursion on cyclic rules.
const MAX_BACKWARD_CHAIN_DEPTH: usize = 10;

/// Try to explain a derived fact by backward-chaining through universal rules.
/// Returns the proof step index if a derivation is found.
fn try_backward_chain_traced(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
) -> Option<u32> {
    // Snapshot rules to avoid borrow conflict with mutable egglog access
    let rules: Vec<UniversalRuleRecord> = inner.universal_rules.clone();

    for rule in &rules {
        for conclusion_template in &rule.conclusion_templates {
            if let Some(bindings) = sexp_match(conclusion_template, sexp, &rule.pattern_var_names)
            {
                // Verify all conditions hold in egglog with the bound variables
                let mut all_conditions_hold = true;
                let mut condition_sexps = Vec::new();

                for cond_template in &rule.condition_templates {
                    let cond_sexp = sexp_substitute(cond_template, &bindings);
                    let check_cmd = format!("(check (IsTrue {}))", cond_sexp);
                    match inner.egraph.parse_and_run_program(None, &check_cmd) {
                        Ok(_) => condition_sexps.push(cond_sexp),
                        Err(_) => {
                            all_conditions_hold = false;
                            break;
                        }
                    }
                }

                if !all_conditions_hold {
                    continue;
                }

                // For bare rules (no conditions), just record the derivation
                if rule.condition_templates.is_empty() {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
                        holds: true,
                        children: vec![],
                    });
                    return Some(idx);
                }

                // Recursively trace each condition
                let mut child_indices = Vec::new();
                for cond_sexp in &condition_sexps {
                    let child_idx =
                        trace_predicate_provenance(cond_sexp, inner, steps, depth + 1);
                    child_indices.push(child_idx);
                }

                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::Derived((rule.label.clone(), sexp.to_string())),
                    holds: true,
                    children: child_indices,
                });
                return Some(idx);
            }
        }
    }

    None
}

/// Trace the provenance of a predicate fact known to be in egglog.
/// Returns the proof step index.
fn trace_predicate_provenance(
    sexp: &str,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
) -> u32 {
    // 1. Was this fact directly asserted?
    if inner.asserted_sexps.contains(sexp) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::Asserted(sexp.to_string()),
            holds: true,
            children: vec![],
        });
        return idx;
    }

    // 2. Try backward-chaining through universal rules
    if depth < MAX_BACKWARD_CHAIN_DEPTH {
        if let Some(idx) = try_backward_chain_traced(sexp, inner, steps, depth) {
            return idx;
        }
    }

    // 3. Fallback: in egglog but can't trace derivation
    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateCheck(("egglog".to_string(), sexp.to_string())),
        holds: true,
        children: vec![],
    });
    idx
}

/// Like `check_formula_holds` but builds a proof trace as it recurses.
/// Returns (result, step_index) where step_index is the index of this
/// step in the `steps` Vec.
fn check_formula_holds_traced(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    tense: Option<&str>,
) -> Result<(bool, u32), String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps, tense)?;
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps, tense)?;
            let result = l_result && r_result;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Conjunction,
                holds: result,
                children: vec![l_idx, r_idx],
            });
            Ok((result, idx))
        }
        LogicNode::OrNode((l, r)) => {
            // Try egglog direct check first (with tense wrapping)
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let command = format!("(check (IsTrue {}))", wrapped);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::DisjunctionEgraph(wrapped),
                        holds: true,
                        children: vec![],
                    });
                    return Ok((true, idx));
                }
                Err(_) => {}
            }
            // Fallback: try left then right
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps, tense)?;
            if l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("left".to_string()),
                    holds: true,
                    children: vec![l_idx],
                });
                return Ok((true, idx));
            }
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps, tense)?;
            if r_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("right".to_string()),
                    holds: true,
                    children: vec![r_idx],
                });
                return Ok((true, idx));
            }
            // Neither holds
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::DisjunctionIntro("neither".to_string()),
                holds: false,
                children: vec![l_idx, r_idx],
            });
            Ok((false, idx))
        }
        LogicNode::NotNode(inner_node) => {
            let (inner_result, inner_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense)?;
            let result = !inner_result;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Negation,
                holds: result,
                children: vec![inner_idx],
            });
            Ok((result, idx))
        }
        // Temporal nodes: set tense context for inner formula
        LogicNode::PastNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Past"))?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("past".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PresentNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Present"))?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("present".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::FutureNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, Some("Future"))?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("future".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        // Deontic nodes: remain transparent, pass through current tense
        LogicNode::ObligatoryNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("obligatory".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PermittedNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps, tense)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("permitted".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::ExistsNode((v, body)) => {
            // 1. Try all known domain members (Const + Desc)
            let members = inner.all_domain_members();
            for (sexp, term) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                let (holds, body_idx) =
                    check_formula_holds_traced(buffer, *body, &new_subs, inner, steps, tense)?;
                if holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ExistsWitness((v.clone(), term.clone())),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
                }
            }
            // 2. Try SkolemFn witnesses
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let dep_sexps: Vec<String> = members.iter().map(|(s, _)| s.clone()).collect();
                let combos = cartesian_product(&dep_sexps, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_skolem_fn_sexp(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    let (holds, body_idx) =
                        check_formula_holds_traced(buffer, *body, &new_subs, inner, steps, tense)?;
                    if holds {
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::ExistsWitness((
                                v.clone(),
                                parse_sexp_to_term(&witness_sexp),
                            )),
                            holds: true,
                            children: vec![body_idx],
                        });
                        return Ok((true, idx));
                    }
                }
            }
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ExistsFailed,
                holds: false,
                children: vec![],
            });
            Ok((false, idx))
        }
        LogicNode::ForAllNode((v, body)) => {
            let members = inner.all_domain_members();
            if members.is_empty() {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ForallVacuous,
                    holds: true,
                    children: vec![],
                });
                return Ok((true, idx));
            }
            let mut child_indices = Vec::new();
            let mut entity_terms = Vec::new();
            for (sexp, term) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                let (holds, body_idx) =
                    check_formula_holds_traced(buffer, *body, &new_subs, inner, steps, tense)?;
                if !holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ForallCounterexample(term.clone()),
                        holds: false,
                        children: vec![body_idx],
                    });
                    return Ok((false, idx));
                }
                child_indices.push(body_idx);
                entity_terms.push(term.clone());
            }
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ForallVerified(entity_terms),
                holds: true,
                children: child_indices,
            });
            Ok((true, idx))
        }
        LogicNode::CountNode((v, count, body)) => {
            let members = inner.all_domain_members();
            let mut satisfying = 0u32;
            for (sexp, _) in &members {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), sexp.clone());
                if check_formula_holds(buffer, *body, &new_subs, inner, tense)? {
                    satisfying += 1;
                }
            }
            let result = satisfying == *count;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::CountResult((*count, satisfying)),
                holds: result,
                children: vec![],
            });
            Ok((result, idx))
        }
        LogicNode::Predicate((rel, args)) => {
            // Try numeric comparison short-circuit (timeless)
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                let detail = format!(
                    "{}({}) = {}",
                    rel,
                    args.iter()
                        .map(|a| match a {
                            LogicalTerm::Number(n) => format!("{}", *n as i64),
                            LogicalTerm::Variable(v) => subs
                                .get(v.as_str())
                                .cloned()
                                .unwrap_or_else(|| v.clone()),
                            _ => "?".to_string(),
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    result
                );
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::PredicateCheck(("numeric".to_string(), detail)),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // Standard egglog check with tense wrapping
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let wrapped = wrap_with_tense(tense, &sexp);
            let command = format!("(check (IsTrue {}))", wrapped);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => {
                    // Trace provenance: asserted → derived → fallback
                    let idx = trace_predicate_provenance(&wrapped, inner, steps, 0);
                    Ok((true, idx))
                }
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("Check failed") {
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::PredicateCheck(("egglog".to_string(), wrapped)),
                            holds: false,
                            children: vec![],
                        });
                        Ok((false, idx))
                    } else {
                        Err(format!("Reasoning error: {}", msg))
                    }
                }
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // 1. Try WIT dispatch
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(rel, &resolved) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        let cmd = format!("(IsTrue {})", sexp);
                        inner.egraph.parse_and_run_program(None, &cmd).ok();
                    }
                }
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ComputeCheck(("backend".to_string(), rel.clone())),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // 2. Try built-in arithmetic
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                if result {
                    if let Some(sexp) = build_ground_predicate_sexp(rel, &resolved) {
                        let cmd = format!("(IsTrue {})", sexp);
                        inner.egraph.parse_and_run_program(None, &cmd).ok();
                    }
                }
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::ComputeCheck(("arithmetic".to_string(), rel.clone())),
                    holds: result,
                    children: vec![],
                });
                return Ok((result, idx));
            }
            // 3. Egglog fallback
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ComputeCheck(("egglog".to_string(), rel.clone())),
                        holds: true,
                        children: vec![],
                    });
                    Ok((true, idx))
                }
                Err(e) => {
                    let msg = e.to_string();
                    if msg.contains("Check failed") {
                        let idx = steps.len() as u32;
                        steps.push(ProofStep {
                            rule: ProofRule::ComputeCheck(("egglog".to_string(), rel.clone())),
                            holds: false,
                            children: vec![],
                        });
                        Ok((false, idx))
                    } else {
                        Err(format!("Reasoning error: {}", msg))
                    }
                }
            }
        }
    }
}

// ─── Skolemization Helpers ────────────────────────────────────────

fn collect_exists_for_skolem(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    enclosing_universals: &mut Vec<String>,
    counter: &mut usize,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            if !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    let sk = format!("sk_{}", *counter);
                    *counter += 1;
                    subs.insert(v.clone(), sk);
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
        }
        LogicNode::ForAllNode((v, body)) => {
            enclosing_universals.push(v.clone());
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
            enclosing_universals.pop();
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_exists_for_skolem(buffer, *l, subs, enclosing_universals, counter);
            collect_exists_for_skolem(buffer, *r, subs, enclosing_universals, counter);
        }
        LogicNode::NotNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals, counter);
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count > 0 && !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    let sk = format!("sk_{}", *counter);
                    *counter += 1;
                    subs.insert(v.clone(), sk);
                } else {
                    let base = format!("sk_{}", *counter);
                    *counter += 1;
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals, counter);
        }
        LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals, counter);
        }
    }
}

// ─── Native Rule Compilation ─────────────────────────────────────

/// Decompose a material conditional body into (conditions, action).
/// Decompose a formula into (conditions, consequent) for material conditional rules.
/// Recognizes `Not(And(conditions)) → consequent` and `Or(Not(conditions), consequent)` patterns.
fn decompose_implication(buffer: &LogicBuffer, body_id: u32) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::OrNode((left, right)) => {
                match &buffer.nodes[*left as usize] {
                    LogicNode::NotNode(inner) => {
                        conditions.push(*inner);
                        current = *right;
                    }
                    _ => break,
                }
            }
            _ => break,
        }
    }

    if conditions.is_empty() {
        None
    } else {
        Some((conditions, current))
    }
}

/// Flatten nested And nodes into individual atom node IDs.
fn flatten_conjuncts(buffer: &LogicBuffer, node_id: u32) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_conjuncts(buffer, *l);
            result.extend(flatten_conjuncts(buffer, *r));
            result
        }
        _ => vec![node_id],
    }
}

/// Flatten consequent And-nodes and strip Skolemized Exists wrappers.
fn flatten_consequent(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
) -> Vec<u32> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) if skolem_subs.contains_key(v.as_str()) => {
            flatten_consequent(buffer, *body, skolem_subs)
        }
        LogicNode::AndNode((l, r)) => {
            let mut result = flatten_consequent(buffer, *l, skolem_subs);
            result.extend(flatten_consequent(buffer, *r, skolem_subs));
            result
        }
        _ => vec![node_id],
    }
}

/// Note all Const and Desc terms found in the formula as known domain members.
fn collect_and_note_constants(buffer: &LogicBuffer, node_id: u32, inner: &mut KnowledgeBaseInner) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) | LogicNode::ComputeNode((_, args)) => {
            for arg in args {
                match arg {
                    LogicalTerm::Constant(c) => inner.note_entity(c),
                    LogicalTerm::Description(d) => inner.note_description(d),
                    _ => {}
                }
            }
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_and_note_constants(buffer, *l, inner);
            collect_and_note_constants(buffer, *r, inner);
        }
        LogicNode::NotNode(inner_node)
        | LogicNode::ExistsNode((_, inner_node))
        | LogicNode::ForAllNode((_, inner_node)) => {
            collect_and_note_constants(buffer, *inner_node, inner);
        }
        LogicNode::CountNode((_, _, body)) => {
            collect_and_note_constants(buffer, *body, inner);
        }
        LogicNode::PastNode(inner_node)
        | LogicNode::PresentNode(inner_node)
        | LogicNode::FutureNode(inner_node)
        | LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => {
            collect_and_note_constants(buffer, *inner_node, inner);
        }
    }
}

/// Reconstruct an egglog s-expression with bare pattern variables for rule compilation.
/// Reconstruct an egglog s-expression from a logic buffer node, applying variable
/// substitutions and Skolem replacements. Used for building egglog rule bodies.
fn reconstruct_rule_sexp(
    buffer: &LogicBuffer,
    node_id: u32,
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
    dependent_skolems: &HashMap<String, (String, Vec<String>)>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(pvar) = pattern_vars.get(v.as_str()) {
                            pvar.clone()
                        } else if let Some(sk) = ground_skolems.get(v.as_str()) {
                            format!("(Const \"{}\")", sk)
                        } else if let Some((base, pvars)) = dependent_skolems.get(v.as_str()) {
                            build_skolem_fn_sexp(base, pvars)
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::ExistsNode((v, body)) => {
            if ground_skolems.contains_key(v.as_str())
                || pattern_vars.contains_key(v.as_str())
                || dependent_skolems.contains_key(v.as_str())
            {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            if pattern_vars.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
                )
            }
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems, dependent_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems, dependent_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::NotNode(inner) => {
            format!(
                "(Not {})",
                reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems)
            )
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else if ground_skolems.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems)
            } else {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems, dependent_skolems);
                format!("(Exists \"{}\" {})", v, body_sexp)
            }
        }
        LogicNode::PastNode(inner) => {
            format!("(Past {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::PresentNode(inner) => {
            format!("(Present {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::FutureNode(inner) => {
            format!("(Future {})", reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems))
        }
        LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems)
        }
    }
}

/// Extract the predicate name from a bare s-expression like `(Pred "gerku" ...)`.
fn extract_pred_name(sexp: &str) -> Option<&str> {
    let rest = sexp.strip_prefix("(Pred \"")?;
    let end = rest.find('"')?;
    Some(&rest[..end])
}

/// Build a human-readable rule label from condition/conclusion templates.
fn build_rule_label(conditions: &[String], conclusions: &[String]) -> String {
    let cond_names: Vec<&str> = conditions
        .iter()
        .filter_map(|s| extract_pred_name(s))
        .collect();
    let concl_names: Vec<&str> = conclusions
        .iter()
        .filter_map(|s| extract_pred_name(s))
        .collect();
    if cond_names.is_empty() {
        format!("∀ → {}", concl_names.join(" ∧ "))
    } else {
        format!("{} → {}", cond_names.join(" ∧ "), concl_names.join(" ∧ "))
    }
}

/// Compile a ForAll node into a native egglog rule.
fn compile_forall_to_rule(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Result<(), String> {
    // 1. Collect universal variables from nested ForAll nodes
    let mut universals: Vec<String> = Vec::new();
    let mut current = node_id;
    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::ForAllNode((v, body)) => {
                universals.push(v.clone());
                current = *body;
            }
            LogicNode::PastNode(inner_node)
            | LogicNode::PresentNode(inner_node)
            | LogicNode::FutureNode(inner_node)
            | LogicNode::ObligatoryNode(inner_node)
            | LogicNode::PermittedNode(inner_node) => {
                current = *inner_node;
            }
            _ => break,
        }
    }
    let inner_body_id = current;

    // 2. Build pattern variable map: "_v0" -> "x__v0"
    let pattern_vars: HashMap<String, String> = universals
        .iter()
        .enumerate()
        .map(|(i, v)| (v.clone(), format!("x__v{}", i)))
        .collect();

    let ground_skolems: HashMap<String, String> = skolem_subs
        .iter()
        .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

    let pattern_var_names: Vec<String> = universals
        .iter()
        .map(|v| pattern_vars[v].clone())
        .collect();
    let dependent_skolems: HashMap<String, (String, Vec<String>)> = skolem_subs
        .iter()
        .filter_map(|(k, v)| {
            v.strip_prefix(SKDEP_PREFIX).map(|base| {
                (k.clone(), (base.to_string(), pattern_var_names.clone()))
            })
        })
        .collect();

    // Register dependent Skolems for query-side witness enumeration
    if !dependent_skolems.is_empty() {
        for (_, (base, pvars)) in &dependent_skolems {
            if !inner.skolem_fn_registry.iter().any(|e| e.base_name == *base) {
                inner.skolem_fn_registry.push(SkolemFnEntry {
                    base_name: base.clone(),
                    dep_count: pvars.len(),
                });
            }
        }
    }

    // 3. Decompose inner body
    match decompose_implication(buffer, inner_body_id) {
        Some((condition_ids, consequent_id)) => {
            let mut all_conditions = Vec::new();
            for cid in &condition_ids {
                all_conditions.extend(flatten_conjuncts(buffer, *cid));
            }

            let bare_condition_sexps: Vec<String> = all_conditions
                .iter()
                .map(|&cid| {
                    reconstruct_rule_sexp(buffer, cid, &pattern_vars, &ground_skolems, &dependent_skolems)
                })
                .collect();
            let conditions_sexp: Vec<String> = bare_condition_sexps
                .iter()
                .map(|s| format!("(IsTrue {})", s))
                .collect();

            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);
            let bare_conclusion_sexps: Vec<String> = consequent_atoms
                .iter()
                .map(|&aid| {
                    reconstruct_rule_sexp(buffer, aid, &pattern_vars, &ground_skolems, &dependent_skolems)
                })
                .collect();
            let actions_sexp: Vec<String> = bare_conclusion_sexps
                .iter()
                .map(|s| format!("(IsTrue {})", s))
                .collect();

            let rule = format!(
                "(rule ({}) ({}))",
                conditions_sexp.join(" "),
                actions_sexp.join(" ")
            );

            if !inner.known_rules.insert(rule.clone()) {
                if !inner.rebuilding {
                    println!(
                        "[Rule] ∀{} already present, skipping",
                        universals.join(",")
                    );
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled ∀{} to native egglog rule",
                        universals.join(",")
                    );
                }
                inner
                    .egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile universal to rule: {}", e))?;

                // Record rule structure for backward-chaining provenance
                let label = build_rule_label(&bare_condition_sexps, &bare_conclusion_sexps);
                inner.universal_rules.push(UniversalRuleRecord {
                    label,
                    condition_templates: bare_condition_sexps.clone(),
                    conclusion_templates: bare_conclusion_sexps.clone(),
                    pattern_var_names: pattern_var_names.clone(),
                });

                // ── xorlo presupposition: assert restrictor domain is non-empty ──
                // In Lojban, `ro lo P cu Q` presupposes at least one P exists.
                // Create a presupposition Skolem for each restrictor predicate,
                // substituting universal variables with a fresh constant.
                let xp_name = inner.fresh_skolem();
                inner.note_entity(&xp_name);
                let mut xp_subs: HashMap<String, String> = HashMap::new();
                for v in &universals {
                    xp_subs.insert(v.clone(), format!("(Const \"{}\")", xp_name));
                }
                // Merge ground skolems from outer scope
                for (k, v) in &ground_skolems {
                    xp_subs.entry(k.clone()).or_insert_with(|| format!("(Const \"{}\")", v));
                }
                for &cid in &all_conditions {
                    let presup = reconstruct_sexp_with_subs(buffer, cid, &xp_subs);
                    // Record xorlo presupposition as asserted for provenance
                    inner.asserted_sexps.insert(presup.clone());
                    let cmd = format!("(IsTrue {})", presup);
                    inner.egraph.parse_and_run_program(None, &cmd).ok();
                }
                inner.egraph.parse_and_run_program(None, "(run 100)").ok();

                // ── Temporal lifting: compile Past/Present/Future variants ──
                compile_temporal_lifted_rules(inner, &bare_condition_sexps, &bare_conclusion_sexps, &pattern_var_names)?;
            }
        }
        None => {
            let body_sexp =
                reconstruct_rule_sexp(buffer, inner_body_id, &pattern_vars, &ground_skolems, &dependent_skolems);

            let domain_conditions: Vec<String> = universals
                .iter()
                .map(|v| format!("(InDomain {})", pattern_vars[v]))
                .collect();

            let rule = format!(
                "(rule ({}) ((IsTrue {})))",
                domain_conditions.join(" "),
                body_sexp
            );

            if !inner.known_rules.insert(rule.clone()) {
                if !inner.rebuilding {
                    println!(
                        "[Rule] bare ∀{} already present, skipping",
                        universals.join(",")
                    );
                }
            } else {
                if !inner.rebuilding {
                    println!(
                        "[Rule] Compiled bare ∀{} with InDomain trigger",
                        universals.join(",")
                    );
                }
                inner
                    .egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile bare universal to rule: {}", e))?;

                // Record bare rule structure for backward-chaining provenance
                let label = build_rule_label(&[], &[body_sexp.clone()]);
                inner.universal_rules.push(UniversalRuleRecord {
                    label,
                    condition_templates: vec![],
                    conclusion_templates: vec![body_sexp.clone()],
                    pattern_var_names: pattern_var_names.clone(),
                });

                // ── Temporal lifting: compile Past/Present/Future variants ──
                compile_temporal_lifted_rules(inner, &[], &[body_sexp], &pattern_var_names)?;
            }
        }
    }

    Ok(())
}

/// Compile Past/Present/Future variants of a universal rule.
/// For each tense T, wraps all conditions and conclusions with T(...).
fn compile_temporal_lifted_rules(
    inner: &mut KnowledgeBaseInner,
    bare_condition_sexps: &[String],
    bare_conclusion_sexps: &[String],
    pattern_var_names: &[String],
) -> Result<(), String> {
    for tense in &["Past", "Present", "Future"] {
        let tensed_conditions: Vec<String> = bare_condition_sexps
            .iter()
            .map(|s| format!("(IsTrue ({} {}))", tense, s))
            .collect();
        let tensed_actions: Vec<String> = bare_conclusion_sexps
            .iter()
            .map(|s| format!("(IsTrue ({} {}))", tense, s))
            .collect();

        // For bare rules (no conditions), use InDomain triggers
        let rule = if tensed_conditions.is_empty() {
            // Bare rules need InDomain as triggers
            let domain_conditions: Vec<String> = pattern_var_names
                .iter()
                .map(|pv| format!("(InDomain {})", pv))
                .collect();
            format!(
                "(rule ({}) ({}))",
                domain_conditions.join(" "),
                tensed_actions.join(" ")
            )
        } else {
            format!(
                "(rule ({}) ({}))",
                tensed_conditions.join(" "),
                tensed_actions.join(" ")
            )
        };

        if inner.known_rules.insert(rule.clone()) {
            inner
                .egraph
                .parse_and_run_program(None, &rule)
                .map_err(|e| format!("Failed to compile {}-lifted rule: {}", tense, e))?;

            // Record tense-lifted rule for backward-chaining provenance
            let tensed_cond_templates: Vec<String> = bare_condition_sexps
                .iter()
                .map(|s| format!("({} {})", tense, s))
                .collect();
            let tensed_concl_templates: Vec<String> = bare_conclusion_sexps
                .iter()
                .map(|s| format!("({} {})", tense, s))
                .collect();
            let label = build_rule_label(&tensed_cond_templates, &tensed_concl_templates);
            inner.universal_rules.push(UniversalRuleRecord {
                label,
                condition_templates: tensed_cond_templates,
                conclusion_templates: tensed_concl_templates,
                pattern_var_names: pattern_var_names.to_vec(),
            });
        }
    }
    Ok(())
}

// ─── S-Expression Pattern Matching (for backward-chaining provenance) ────

/// Tokenize an s-expression string into atoms, parens, and quoted strings.
fn sexp_tokenize(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&ch) = chars.peek() {
        match ch {
            '(' => {
                tokens.push("(".to_string());
                chars.next();
            }
            ')' => {
                tokens.push(")".to_string());
                chars.next();
            }
            '"' => {
                chars.next(); // consume opening quote
                let mut quoted = String::from("\"");
                while let Some(&c) = chars.peek() {
                    chars.next();
                    if c == '"' {
                        break;
                    }
                    quoted.push(c);
                }
                quoted.push('"');
                tokens.push(quoted);
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c == '(' || c == ')' || c == '"' || c.is_whitespace() {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                tokens.push(atom);
            }
        }
    }
    tokens
}

/// Extract one complete s-expression starting at position `start` in a token stream.
/// Returns `(end_position, reconstructed_sexp_string)`.
fn extract_sexp_at(tokens: &[String], start: usize) -> Option<(usize, String)> {
    if start >= tokens.len() {
        return None;
    }
    if tokens[start] == "(" {
        let mut depth = 1usize;
        let mut end = start + 1;
        while end < tokens.len() && depth > 0 {
            if tokens[end] == "(" {
                depth += 1;
            } else if tokens[end] == ")" {
                depth -= 1;
            }
            end += 1;
        }
        if depth != 0 {
            return None;
        }
        // Reconstruct the s-expression with proper spacing
        let mut out = String::new();
        for i in start..end {
            if i > start && tokens[i] != ")" && tokens[i - 1] != "(" {
                out.push(' ');
            }
            out.push_str(&tokens[i]);
        }
        Some((end, out))
    } else {
        Some((start + 1, tokens[start].clone()))
    }
}

/// Match one s-expression element starting at `(pi, ci)`.
/// Returns `(new_pi, new_ci)` — the positions right after the matched element.
/// Does NOT tail-recurse beyond the single matched element.
fn sexp_match_one(
    pat: &[String],
    pi: usize,
    conc: &[String],
    ci: usize,
    var_names: &[String],
    bindings: &mut HashMap<String, String>,
) -> Option<(usize, usize)> {
    if pi >= pat.len() || ci >= conc.len() {
        return None;
    }

    let pt = &pat[pi];

    // If pattern token is a variable name, match a complete sub-expression
    if var_names.contains(pt) {
        let (sub_end, sub_sexp) = extract_sexp_at(conc, ci)?;
        if let Some(existing) = bindings.get(pt.as_str()) {
            if *existing != sub_sexp {
                return None;
            }
        } else {
            bindings.insert(pt.clone(), sub_sexp);
        }
        return Some((pi + 1, sub_end));
    }

    // Both are "(" — match parenthesized sub-expressions element by element
    if pt == "(" && conc[ci] == "(" {
        let mut pj = pi + 1;
        let mut cj = ci + 1;
        loop {
            if pj >= pat.len() || cj >= conc.len() {
                return None;
            }
            if pat[pj] == ")" && conc[cj] == ")" {
                return Some((pj + 1, cj + 1));
            }
            if pat[pj] == ")" || conc[cj] == ")" {
                return None;
            }
            let (new_pj, new_cj) =
                sexp_match_one(pat, pj, conc, cj, var_names, bindings)?;
            pj = new_pj;
            cj = new_cj;
        }
    }

    // Literal match
    if pt == &conc[ci] {
        Some((pi + 1, ci + 1))
    } else {
        None
    }
}

/// Match a template s-expression against a concrete s-expression.
/// Pattern variables in `var_names` (e.g., "x__v0") match complete sub-expressions.
/// Returns bindings mapping variable names to their matched sub-expressions.
fn sexp_match(
    pattern: &str,
    concrete: &str,
    var_names: &[String],
) -> Option<HashMap<String, String>> {
    let pat_tokens = sexp_tokenize(pattern);
    let conc_tokens = sexp_tokenize(concrete);
    let mut bindings = HashMap::new();
    let (pe, ce) = sexp_match_one(&pat_tokens, 0, &conc_tokens, 0, var_names, &mut bindings)?;
    if pe == pat_tokens.len() && ce == conc_tokens.len() {
        Some(bindings)
    } else {
        None
    }
}

/// Substitute pattern variable names in a template with their bound values.
fn sexp_substitute(template: &str, bindings: &HashMap<String, String>) -> String {
    let tokens = sexp_tokenize(template);
    let mut result_tokens: Vec<String> = Vec::new();
    for token in &tokens {
        if let Some(replacement) = bindings.get(token.as_str()) {
            result_tokens.extend(sexp_tokenize(replacement));
        } else {
            result_tokens.push(token.clone());
        }
    }
    // Reconstruct s-expression string with proper spacing
    let mut out = String::new();
    for (i, token) in result_tokens.iter().enumerate() {
        if i > 0 && token != ")" && result_tokens[i - 1] != "(" {
            out.push(' ');
        }
        out.push_str(token);
    }
    out
}

// ─── S-Expression Reconstruction ─────────────────────────────────

fn reconstruct_sexp_with_subs(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) | LogicNode::ComputeNode((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(raw_sexp) = subs.get(v.as_str()) {
                            raw_sexp.clone()
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", *n as i64),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::ExistsNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                reconstruct_sexp_with_subs(buffer, *body, subs)
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                reconstruct_sexp_with_subs(buffer, *body, subs)
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                )
            }
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_sexp_with_subs(buffer, *l, subs),
                reconstruct_sexp_with_subs(buffer, *r, subs)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_sexp_with_subs(buffer, *l, subs),
                reconstruct_sexp_with_subs(buffer, *r, subs)
            )
        }
        LogicNode::NotNode(inner) => {
            format!("(Not {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else {
                if subs.contains_key(v.as_str()) {
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                } else {
                    let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                    format!("(Exists \"{}\" {})", v, body_sexp)
                }
            }
        }
        LogicNode::PastNode(inner) => {
            format!("(Past {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::PresentNode(inner) => {
            format!("(Present {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::FutureNode(inner) => {
            format!("(Future {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
        LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => reconstruct_sexp_with_subs(buffer, *inner, subs),
    }
}

/// Generate extra Skolem witnesses for Count(x, n, body) where n > 1.
fn generate_count_extra_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::CountNode((v, count, body)) => {
            if *count > 1 {
                for _ in 1..*count {
                    let extra_sk = inner.fresh_skolem();
                    inner.note_entity(&extra_sk);

                    let mut extra_subs: HashMap<String, String> = skolem_subs
                        .iter()
                        .filter(|(_, sv)| !sv.starts_with(SKDEP_PREFIX))
                        .map(|(k, sv)| (k.clone(), format!("(Const \"{}\")", sv)))
                        .collect();
                    extra_subs.insert(v.clone(), format!("(Const \"{}\")", extra_sk));

                    let sexp = reconstruct_sexp_with_subs(buffer, *body, &extra_subs);
                    let command = format!("(IsTrue {})", sexp);
                    if let Err(e) = inner.egraph.parse_and_run_program(None, &command) {
                        eprintln!(
                            "[reasoning] Failed to assert extra Count witness {}: {}",
                            extra_sk, e
                        );
                    }
                }
            }
            generate_count_extra_witnesses(buffer, *body, skolem_subs, inner);
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            generate_count_extra_witnesses(buffer, *l, skolem_subs, inner);
            generate_count_extra_witnesses(buffer, *r, skolem_subs, inner);
        }
        LogicNode::NotNode(inner_node)
        | LogicNode::ExistsNode((_, inner_node))
        | LogicNode::ForAllNode((_, inner_node)) => {
            generate_count_extra_witnesses(buffer, *inner_node, skolem_subs, inner);
        }
        LogicNode::PastNode(inner_node)
        | LogicNode::PresentNode(inner_node)
        | LogicNode::FutureNode(inner_node)
        | LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => {
            generate_count_extra_witnesses(buffer, *inner_node, skolem_subs, inner);
        }
        LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
    }
}

bindings::export!(ReasoningComponent with_types_in bindings);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bindings::lojban::nesy::logic_types::{
        LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofTrace,
    };

    /// Helper: build a Predicate node with the given relation and args.
    fn pred(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::Predicate((rel.to_string(), args)));
        id
    }

    /// Helper: build a NotNode wrapping the given node.
    fn not(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::NotNode(inner));
        id
    }

    /// Helper: build an OrNode.
    fn or(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::OrNode((left, right)));
        id
    }

    /// Helper: build a ForAllNode.
    fn forall(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ForAllNode((var.to_string(), body)));
        id
    }

    /// Helper: build an ExistsNode.
    fn exists(nodes: &mut Vec<LogicNode>, var: &str, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ExistsNode((var.to_string(), body)));
        id
    }

    /// Helper: build an AndNode.
    fn and(nodes: &mut Vec<LogicNode>, left: u32, right: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::AndNode((left, right)));
        id
    }

    fn new_kb() -> KnowledgeBase {
        KnowledgeBase {
            inner: RefCell::new(KnowledgeBaseInner::new()),
        }
    }

    fn assert_buf(kb: &KnowledgeBase, buf: LogicBuffer) {
        kb.assert_fact_inner(buf, String::new()).unwrap();
    }

    fn query(kb: &KnowledgeBase, buf: LogicBuffer) -> bool {
        kb.query_entailment_inner(buf).unwrap()
    }

    /// Build "la .X. P" -> Pred("P", [Const("X"), Zoe])
    fn make_assertion(entity: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            predicate,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Build "ro lo P cu Q" -> ForAll("_v0", Or(Not(Pred("P", [Var("_v0"), Zoe])), Pred("Q", [Var("_v0"), Zoe])))
    fn make_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body = pred(
            &mut nodes,
            consequent,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, body);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    fn make_query(entity: &str, predicate: &str) -> LogicBuffer {
        make_assertion(entity, predicate)
    }

    #[test]
    fn test_native_rule_simple_universal() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_entity_after_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_selective_application() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
        assert!(!query(&kb, make_query("bob", "danlu")));
    }

    // ─── Existential introduction (xorlo presupposition) ─────────

    #[test]
    fn test_xorlo_presupposition_basic() {
        // ro lo gerku cu danlu → presupposition: ∃x. gerku(x)
        // Query ∃x. gerku(x) should find the presupposition Skolem
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        // Query: ∃x. gerku(x)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_consequent() {
        // ro lo gerku cu danlu → presupposition creates sk entity → rule fires
        // Query ∃x. danlu(x) should find the derived fact
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_conjunction() {
        // THE BUG FIX: ro lo gerku cu danlu, then ? lo gerku cu danlu
        // (∃x. gerku(x) ∧ danlu(x)) should be TRUE
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p1, p2);
        let root = exists(&mut nodes, "x", conj);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_with_real_entity() {
        // Real entity + presupposition Skolem both satisfy the query
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Both alis and the presupposition Skolem are in the KB
        assert!(query(&kb, make_query("alis", "danlu")));

        // Witness search should find both alis and the presupposition Skolem
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });
        assert!(results.len() >= 2); // alis + presupposition Skolem
    }

    #[test]
    fn test_xorlo_presupposition_transitive() {
        // ro lo gerku cu danlu, ro lo danlu cu xanlu
        // Each universal creates its own presupposition Skolem
        // Query ∃x. xanlu(x) should find witnesses via chain
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "xanlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_xorlo_presupposition_no_false_positives() {
        // ro lo gerku cu danlu should NOT make mlatu(x) exist
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_native_rule_transitive_chain() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "xanlu")));
    }

    #[test]
    fn test_native_rule_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));
        assert!(query(&kb, make_query("bob", "danlu")));
    }

    #[test]
    fn test_native_rule_negated_universal() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body_pred = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let neg_body = not(&mut nodes, body_pred);
        let neg_restrict = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg_restrict, neg_body);
        let root = forall(&mut nodes, "_v0", disj);
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_duplicate_rule_no_panic() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "danlu")));
    }

    // ─── Dependent Skolem (Phase B) Tests ────────────────────────────

    fn make_dependent_skolem_universal(restrictor: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let body = pred(
            &mut nodes,
            consequent,
            vec![
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let ex = exists(&mut nodes, "_v1", body);
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, ex);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    fn make_exists_query(entity: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            predicate,
            vec![
                LogicalTerm::Constant(entity.to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "_v1", body);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_dependent_skolem_native_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
    }

    #[test]
    fn test_dependent_skolem_entity_after_rule() {
        let kb = new_kb();
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
    }

    #[test]
    fn test_dependent_skolem_query_existential() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
        assert!(!query(&kb, make_exists_query("bob", "zdani")));
    }

    #[test]
    fn test_skolem_fn_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("bob", "prenu"));
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        assert!(query(&kb, make_exists_query("alis", "zdani")));
        assert!(query(&kb, make_exists_query("bob", "zdani")));
    }

    #[test]
    fn test_skolem_fn_registry_populated() {
        let kb = new_kb();
        assert_buf(&kb, make_dependent_skolem_universal("prenu", "zdani"));
        let inner = kb.inner.borrow();
        assert!(!inner.skolem_fn_registry.is_empty(), "SkolemFn registry should have entries");
        assert_eq!(inner.skolem_fn_registry[0].base_name, "sk_0");
        assert_eq!(inner.skolem_fn_registry[0].dep_count, 1);
    }

    // ─── Multi-Dependency SkolemFn Tests ─────────────────────────

    /// Build: ∀_v0. ∀_v1. (¬(prenu(_v0, zo'e) ∧ mlatu(_v1, zo'e)) ∨ ∃_v2. zdani(_v0, _v1, _v2))
    /// Meaning: for all persons x and cats y, there exists a z such that zdani(x, y, z).
    fn make_multi_dep_skolem_universal() -> LogicBuffer {
        let mut nodes = Vec::new();
        let p = pred(
            &mut nodes,
            "prenu",
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        let q = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Variable("_v1".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p, q);
        let body = pred(
            &mut nodes,
            "zdani",
            vec![
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Variable("_v1".to_string()),
                LogicalTerm::Variable("_v2".to_string()),
            ],
        );
        let ex = exists(&mut nodes, "_v2", body);
        let neg = not(&mut nodes, conj);
        let disj = or(&mut nodes, neg, ex);
        let inner_forall = forall(&mut nodes, "_v1", disj);
        let root = forall(&mut nodes, "_v0", inner_forall);
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Query: ∃_v2. zdani(entity_a, entity_b, _v2)
    fn make_multi_dep_exists_query(entity_a: &str, entity_b: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "zdani",
            vec![
                LogicalTerm::Constant(entity_a.to_string()),
                LogicalTerm::Constant(entity_b.to_string()),
                LogicalTerm::Variable("_v2".to_string()),
            ],
        );
        let root = exists(&mut nodes, "_v2", body);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_multi_dep_skolem_two_universals() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert_buf(&kb, make_multi_dep_skolem_universal());
        // ∃z. zdani(alis, felix, z) should be TRUE via SkolemFn with 2 deps
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    }

    #[test]
    fn test_multi_dep_skolem_registry() {
        let kb = new_kb();
        assert_buf(&kb, make_multi_dep_skolem_universal());
        let inner = kb.inner.borrow();
        assert!(!inner.skolem_fn_registry.is_empty());
        assert_eq!(inner.skolem_fn_registry[0].dep_count, 2);
    }

    #[test]
    fn test_multi_dep_skolem_different_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("bob", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert_buf(&kb, make_assertion("garfield", "mlatu"));
        assert_buf(&kb, make_multi_dep_skolem_universal());
        // All combinations of person × cat should have zdani witnesses
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
        assert!(query(&kb, make_multi_dep_exists_query("alis", "garfield")));
        assert!(query(&kb, make_multi_dep_exists_query("bob", "felix")));
        assert!(query(&kb, make_multi_dep_exists_query("bob", "garfield")));
        // Non-prenu or non-mlatu entities should NOT have zdani witnesses
        assert!(!query(&kb, make_multi_dep_exists_query("felix", "alis")));
    }

    #[test]
    fn test_multi_dep_skolem_rule_before_facts() {
        let kb = new_kb();
        // Rule first, then facts
        assert_buf(&kb, make_multi_dep_skolem_universal());
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_assertion("felix", "mlatu"));
        assert!(query(&kb, make_multi_dep_exists_query("alis", "felix")));
    }

    // ─── Numeric Comparison Tests ────────────────────────────────

    /// Build a comparison predicate: Pred(rel, [Num(a), Num(b), Zoe, ...])
    fn make_numeric_pred(nodes: &mut Vec<LogicNode>, relation: &str, a: f64, b: f64) -> u32 {
        let mut args = vec![
            LogicalTerm::Number(a),
            LogicalTerm::Number(b),
            LogicalTerm::Unspecified,
        ];
        // zmadu and mleca have arity 4; dunli has arity 3
        if relation == "zmadu" || relation == "mleca" {
            args.push(LogicalTerm::Unspecified);
        }
        pred(nodes, relation, args)
    }

    fn make_numeric_query(relation: &str, a: f64, b: f64) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = make_numeric_pred(&mut nodes, relation, a, b);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_zmadu_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 2.0, 1.0)));
    }

    #[test]
    fn test_zmadu_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 1.0, 2.0)));
    }

    #[test]
    fn test_zmadu_numeric_equal_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 2.0, 2.0)));
    }

    #[test]
    fn test_mleca_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("mleca", 1.0, 2.0)));
    }

    #[test]
    fn test_mleca_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("mleca", 2.0, 1.0)));
    }

    #[test]
    fn test_dunli_numeric_true() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
    }

    #[test]
    fn test_dunli_numeric_false() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
    }

    #[test]
    fn test_zmadu_negated() {
        let kb = new_kb();
        // NOT (1 > 2) should be TRUE
        let mut nodes = Vec::new();
        let cmp = make_numeric_pred(&mut nodes, "zmadu", 1.0, 2.0);
        let root = not(&mut nodes, cmp);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_zmadu_non_numeric_fallback() {
        let kb = new_kb();
        // Non-numeric zmadu: assert then query via standard egglog path
        let mut a_nodes = Vec::new();
        let a_root = pred(
            &mut a_nodes,
            "zmadu",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Unspecified,
                LogicalTerm::Unspecified,
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![a_root] });

        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "zmadu",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Unspecified,
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_zmadu_large_numbers() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 1_000_000.0, 999_999.0)));
    }

    #[test]
    fn test_zmadu_negative_numbers() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", -1.0, -2.0)));
        assert!(!query(&kb, make_numeric_query("zmadu", -2.0, -1.0)));
    }

    // ─── ComputeNode Tests ───────────────────────────────────────

    /// Helper: build a ComputeNode with the given relation and args.
    fn compute(nodes: &mut Vec<LogicNode>, rel: &str, args: Vec<LogicalTerm>) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ComputeNode((rel.to_string(), args)));
        id
    }

    /// Helper: build a ComputeNode query buffer for arithmetic predicates.
    fn make_compute_query(rel: &str, x1: f64, x2: f64, x3: f64) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = compute(
            &mut nodes,
            rel,
            vec![
                LogicalTerm::Number(x1),
                LogicalTerm::Number(x2),
                LogicalTerm::Number(x3),
            ],
        );
        LogicBuffer {
            nodes,
            roots: vec![root],
        }
    }

    #[test]
    fn test_compute_pilji_true() {
        let kb = new_kb();
        // 6 = 2 * 3
        assert!(query(&kb, make_compute_query("pilji", 6.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_pilji_false() {
        let kb = new_kb();
        // 7 != 2 * 3
        assert!(!query(&kb, make_compute_query("pilji", 7.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_sumji_true() {
        let kb = new_kb();
        // 5 = 2 + 3
        assert!(query(&kb, make_compute_query("sumji", 5.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_sumji_false() {
        let kb = new_kb();
        // 4 != 2 + 3
        assert!(!query(&kb, make_compute_query("sumji", 4.0, 2.0, 3.0)));
    }

    #[test]
    fn test_compute_dilcu_true() {
        let kb = new_kb();
        // 3 = 6 / 2
        assert!(query(&kb, make_compute_query("dilcu", 3.0, 6.0, 2.0)));
    }

    #[test]
    fn test_compute_dilcu_division_by_zero() {
        let kb = new_kb();
        // x / 0 is always false
        assert!(!query(&kb, make_compute_query("dilcu", 0.0, 5.0, 0.0)));
    }

    #[test]
    fn test_compute_negated() {
        let kb = new_kb();
        // NOT(7 = 2 * 3) → TRUE (because 7 != 6)
        let mut nodes = Vec::new();
        let inner = compute(
            &mut nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let root = not(&mut nodes, inner);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_compute_node_egglog_fallback() {
        // ComputeNode with non-arithmetic predicate falls back to egglog
        let kb = new_kb();

        // Assert: klama(alis, zarci) as a regular fact
        let mut a_nodes = Vec::new();
        let a_root = pred(
            &mut a_nodes,
            "klama",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("zarci".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![a_root] });

        // Query as ComputeNode — unknown to arithmetic, should fall through to egglog
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "klama",
            vec![
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Constant("zarci".to_string()),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    // ── Material conditional / modus ponens tests ──

    /// Helper: build "ganai la .X. P gi la .X. Q" as Or(Not(Pred(P, [X])), Pred(Q, [X]))
    /// This is the logic IR that sentence connective `ganai...gi` produces.
    fn make_material_conditional(entity: &str, antecedent: &str, consequent: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let ante = pred(
            &mut nodes,
            antecedent,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        let cons = pred(
            &mut nodes,
            consequent,
            vec![LogicalTerm::Constant(entity.to_string()), LogicalTerm::Unspecified],
        );
        let neg_ante = not(&mut nodes, ante);
        let root = or(&mut nodes, neg_ante, cons);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_material_conditional_modus_ponens() {
        // ganai la .sol. barda gi la .sol. tsali
        // + la .sol. barda
        // → la .sol. tsali should be TRUE via modus ponens
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "barda"));
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert!(query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_modus_ponens_reversed_order() {
        // Assert the conditional FIRST, then the antecedent
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert_buf(&kb, make_assertion("sol", "barda"));
        assert!(query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_modus_tollens() {
        // ganai la .sol. barda gi la .sol. tsali
        // + la .sol. na tsali (Not tsali)
        // → la .sol. na barda (Not barda) via modus tollens
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));

        // Assert Not(tsali(sol))
        let mut neg_nodes = Vec::new();
        let inner = pred(
            &mut neg_nodes,
            "tsali",
            vec![LogicalTerm::Constant("sol".to_string()), LogicalTerm::Unspecified],
        );
        let root = not(&mut neg_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: neg_nodes, roots: vec![root] });

        // Query: barda(sol) should be FALSE (modus tollens derives Not(barda(sol)))
        assert!(!query(&kb, make_query("sol", "barda")));
    }

    #[test]
    fn test_material_conditional_antecedent_not_satisfied() {
        // ganai la .sol. barda gi la .sol. tsali
        // (no barda assertion)
        // → la .sol. tsali should be FALSE (antecedent not satisfied)
        let kb = new_kb();
        assert_buf(&kb, make_material_conditional("sol", "barda", "tsali"));
        assert!(!query(&kb, make_query("sol", "tsali")));
    }

    #[test]
    fn test_material_conditional_chain() {
        // ganai A gi B, ganai B gi C, assert A → derive C
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "tarci"));
        assert_buf(&kb, make_material_conditional("sol", "tarci", "gusni"));
        assert_buf(&kb, make_material_conditional("sol", "gusni", "melbi"));
        assert!(query(&kb, make_query("sol", "melbi")));
    }

    // ── Deontic predicate tests ──

    /// Helper: build a 3-place deontic assertion: Pred(rel, [Const(entity), Const(action), Zoe])
    fn make_deontic_assertion(entity: &str, relation: &str, action: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            relation,
            vec![
                LogicalTerm::Constant(entity.to_string()),
                LogicalTerm::Constant(action.to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_deontic_bilga_assert_query() {
        // bilga(alis, klama, Zoe) — Alice is obligated to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "bilga", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "bilga", "klama")));
        assert!(!query(&kb, make_deontic_assertion("bob", "bilga", "klama")));
    }

    #[test]
    fn test_deontic_curmi_assert_query() {
        // curmi(alis, klama, Zoe) — Alice is permitted to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "curmi", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "curmi", "klama")));
        assert!(!query(&kb, make_deontic_assertion("alis", "curmi", "tavla")));
    }

    #[test]
    fn test_deontic_nitcu_assert_query() {
        // nitcu(alis, klama, Zoe) — Alice needs to go
        let kb = new_kb();
        assert_buf(&kb, make_deontic_assertion("alis", "nitcu", "klama"));
        assert!(query(&kb, make_deontic_assertion("alis", "nitcu", "klama")));
        assert!(!query(&kb, make_deontic_assertion("alis", "nitcu", "tavla")));
    }

    #[test]
    fn test_deontic_universal_obligation() {
        // ∀x. prenu(x) → bilga(x, Zoe, Zoe) — all people are obligated
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "prenu"));
        assert_buf(&kb, make_universal("prenu", "bilga"));
        assert!(query(&kb, make_query("alis", "bilga")));
        assert!(!query(&kb, make_query("bob", "bilga")));
    }

    #[test]
    fn test_deontic_conditional_chain() {
        // ganai bilga(sol) gi nitcu(sol) — if obligated then needed
        // + bilga(sol) → nitcu(sol) via modus ponens
        let kb = new_kb();
        assert_buf(&kb, make_assertion("sol", "bilga"));
        assert_buf(&kb, make_material_conditional("sol", "bilga", "nitcu"));
        assert!(query(&kb, make_query("sol", "nitcu")));
    }

    // ── Deontic attitudinal tests ──

    /// Helper: build an ObligatoryNode wrapping the given node.
    fn obligatory(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::ObligatoryNode(inner));
        id
    }

    /// Helper: build a PermittedNode wrapping the given node.
    fn permitted(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PermittedNode(inner));
        id
    }

    #[test]
    fn test_obligatory_assert_query() {
        // Assert Obligatory(klama(alis, zo'e)) then query exact → TRUE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = obligatory(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = obligatory(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_permitted_assert_query() {
        // Assert Permitted(klama(alis, zo'e)) then query exact → TRUE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = permitted(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = permitted(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_obligatory_transparent() {
        // Assert Obligatory(klama(alis, zo'e)) then query without wrapper → TRUE (transparent)
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = obligatory(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        // Query without obligatory wrapper → still TRUE (pass-through)
        assert!(query(&kb, make_query("alis", "klama")));
    }

    // ── Compute result ingestion tests ──

    #[test]
    fn test_compute_result_ingested_into_kb() {
        let kb = new_kb();

        // Query pilji(6, 2, 3) via ComputeNode → TRUE (built-in arithmetic)
        // This should auto-ingest the fact into egglog
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Now query the SAME fact as a plain Predicate (not ComputeNode)
        // It should be found directly in egglog because of auto-ingestion
        let mut p_nodes = Vec::new();
        let p_root = pred(
            &mut p_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: p_nodes, roots: vec![p_root] }));
    }

    #[test]
    fn test_compute_false_not_ingested() {
        let kb = new_kb();

        // Query pilji(7, 2, 3) via ComputeNode → FALSE (7 != 2*3)
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Verify the false fact was NOT ingested as a plain Predicate
        let mut p_nodes = Vec::new();
        let p_root = pred(
            &mut p_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(7.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: p_nodes, roots: vec![p_root] }));
    }

    #[test]
    fn test_ingested_result_available_for_reasoning() {
        let kb = new_kb();

        // Step 1: Query sumji(5, 2, 3) via ComputeNode → TRUE, auto-ingests
        let mut q_nodes = Vec::new();
        let q_root = compute(
            &mut q_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(5.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));

        // Step 2: Assert another fact
        assert_buf(&kb, make_assertion("ok", "derived"));

        // Step 3: Query conjunction: And(sumji(5,2,3), derived("ok", Zoe))
        // Both facts should be in KB: sumji from compute ingestion, derived from assertion
        let mut q2_nodes = Vec::new();
        let left = pred(
            &mut q2_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(5.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let right = pred(
            &mut q2_nodes,
            "derived",
            vec![
                LogicalTerm::Constant("ok".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = and(&mut q2_nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes: q2_nodes, roots: vec![root] }));

        // Step 4: Conjunctive query with a non-ingested compute fact fails
        let mut q3_nodes = Vec::new();
        let l2 = pred(
            &mut q3_nodes,
            "sumji",
            vec![
                LogicalTerm::Number(99.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        let r2 = pred(
            &mut q3_nodes,
            "derived",
            vec![
                LogicalTerm::Constant("ok".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root2 = and(&mut q3_nodes, l2, r2);
        assert!(!query(&kb, LogicBuffer { nodes: q3_nodes, roots: vec![root2] }));
    }

    // ─── Witness extraction tests ────────────────────────────────

    fn query_find(kb: &KnowledgeBase, buf: LogicBuffer) -> Vec<Vec<WitnessBinding>> {
        kb.query_find_inner(buf).unwrap()
    }

    #[test]
    fn test_find_witnesses_single() {
        // Assert klama(mi), query ∃x.klama(x) → x = mi
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
    }

    #[test]
    fn test_find_witnesses_multiple() {
        // Assert klama(mi) + klama(do), query ∃x.klama(x) → x = mi, x = do
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("do", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 2);
        let mut found: Vec<String> = results
            .iter()
            .map(|bs| {
                assert_eq!(bs.len(), 1);
                assert_eq!(bs[0].variable, "x");
                match &bs[0].term {
                    LogicalTerm::Constant(c) => c.clone(),
                    _ => panic!("expected Constant"),
                }
            })
            .collect();
        found.sort();
        assert_eq!(found, vec!["do", "mi"]);
    }

    #[test]
    fn test_find_witnesses_conjunction() {
        // Assert klama(mi), prami(mi), klama(do)
        // Query ∃x.(klama(x) ∧ prami(x)) → only x = mi satisfies both
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("mi", "prami"));
        assert_buf(&kb, make_assertion("do", "klama"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "prami",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let conj = and(&mut nodes, p1, p2);
        let root = exists(&mut nodes, "x", conj);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "mi"));
    }

    #[test]
    fn test_find_witnesses_no_match() {
        // No facts, query ∃x.klama(x) → empty
        let kb = new_kb();

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.is_empty());
    }

    #[test]
    fn test_find_witnesses_via_universal_rule() {
        // Assert gerku(alis), ∀x.(gerku(x)→danlu(x))
        // Query ∃x.danlu(x) → should find alis (+ presupposition Skolem)
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "danlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        // At least alis + presupposition Skolem
        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    #[test]
    fn test_find_witnesses_two_variables() {
        // Assert nelci(bob, alis), query ∃x.∃y.nelci(x, y)
        // Should find x=bob, y=alis
        let kb = new_kb();

        let mut anodes = Vec::new();
        let aidx = pred(
            &mut anodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes: anodes, roots: vec![aidx] });

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Variable("y".to_string()),
            ],
        );
        let inner = exists(&mut nodes, "y", body);
        let root = exists(&mut nodes, "x", inner);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 2);
        let vars: std::collections::HashMap<&str, &LogicalTerm> = results[0]
            .iter()
            .map(|b| (b.variable.as_str(), &b.term))
            .collect();
        assert!(matches!(vars["x"], LogicalTerm::Constant(c) if c == "bob"));
        assert!(matches!(vars["y"], LogicalTerm::Constant(c) if c == "alis"));
    }

    #[test]
    fn test_find_witnesses_transitive_chain() {
        // Assert gerku(alis), ∀x.(gerku→danlu), ∀x.(danlu→xanlu)
        // Query ∃x.xanlu(x) → should find alis (+ presupposition Skolems)
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "xanlu",
            vec![LogicalTerm::Variable("x".to_string()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    // ─── Proof trace tests ───────────────────────────────────────

    fn query_with_proof(kb: &KnowledgeBase, buf: LogicBuffer) -> (bool, ProofTrace) {
        kb.query_entailment_with_proof_inner(buf).unwrap()
    }

    #[test]
    fn test_proof_trace_simple_predicate() {
        // Assert klama(mi), query it → single asserted step, result true
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

        assert!(result);
        assert!(!trace.steps.is_empty());
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_false_predicate() {
        // Query non-existent fact → predicate-check with result false
        let kb = new_kb();
        let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

        assert!(!result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(!root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::PredicateCheck(_)));
    }

    #[test]
    fn test_proof_trace_conjunction() {
        // Assert klama(mi), prami(mi), query conjunction → conjunction root with two children
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        assert_buf(&kb, make_assertion("mi", "prami"));

        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let p2 = pred(
            &mut nodes,
            "prami",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let root = and(&mut nodes, p1, p2);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Conjunction));
        assert_eq!(root_step.children.len(), 2);
        // Both children should be asserted with result true
        for &child in &root_step.children {
            let child_step = &trace.steps[child as usize];
            assert!(child_step.holds);
            assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
        }
    }

    #[test]
    fn test_proof_trace_negation() {
        // Query negation of non-existent fact → negation root with result true
        let kb = new_kb();
        let mut nodes = Vec::new();
        let inner = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Constant("mi".into()), LogicalTerm::Unspecified],
        );
        let root = not(&mut nodes, inner);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Negation));
        assert_eq!(root_step.children.len(), 1);
        // Inner should be predicate-check with result false
        let inner_step = &trace.steps[root_step.children[0] as usize];
        assert!(!inner_step.holds);
    }

    #[test]
    fn test_proof_trace_exists_witness() {
        // Assert klama(alis), query ∃x.klama(x) → exists-witness with x = alis
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "klama"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ExistsWitness(_)));
        if let ProofRule::ExistsWitness((var, term)) = &root_step.rule {
            assert_eq!(var, "x");
            assert!(matches!(term, LogicalTerm::Constant(c) if c == "alis"));
        }
    }

    #[test]
    fn test_proof_trace_exists_failed() {
        // Query ∃x.klama(x) with no facts → exists-failed
        let kb = new_kb();

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "klama",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = exists(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(!result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(!root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ExistsFailed));
    }

    #[test]
    fn test_proof_trace_forall() {
        // Assert gerku(alis), gerku(bob), query ∀x.gerku(x)→gerku(x) [trivially true]
        // Actually: assert gerku for both entities, query ∀x.(gerku(x)→gerku(x))
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));

        // Query: ∀x. gerku(x) — should be ForAll verified for both entities
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = forall(&mut nodes, "x", body);
        let (result, trace) =
            query_with_proof(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::ForallVerified(_)));
        if let ProofRule::ForallVerified(entities) = &root_step.rule {
            assert_eq!(entities.len(), 2);
        }
        // Each child should be a predicate-check with result true
        for &child in &root_step.children {
            let child_step = &trace.steps[child as usize];
            assert!(child_step.holds);
        }
    }

    // ─── Derivation Provenance Tests ──────────────────────────────────

    #[test]
    fn test_proof_trace_asserted_fact() {
        // Directly asserted fact should show Asserted, not PredicateCheck
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
        if let ProofRule::Asserted(sexp) = &root_step.rule {
            assert!(sexp.contains("gerku"));
            assert!(sexp.contains("alis"));
        }
    }

    #[test]
    fn test_proof_trace_single_hop_derived() {
        // gerku(alis) + rule gerku→danlu → danlu(alis) should show Derived with Asserted child
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "danlu"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
        if let ProofRule::Derived((label, sexp)) = &root_step.rule {
            assert!(sexp.contains("danlu"));
            assert!(label.contains("gerku"));
            assert!(label.contains("danlu"));
        }
        assert_eq!(root_step.children.len(), 1);
        // The child should be Asserted (gerku(alis))
        let child_step = &trace.steps[root_step.children[0] as usize];
        assert!(child_step.holds);
        assert!(matches!(&child_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_multi_hop_derived() {
        // Chain: gerku(alis) → danlu(alis) → xanlu(alis) via two rules
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert_buf(&kb, make_universal("danlu", "xanlu"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "xanlu"));
        assert!(result);

        // Root: Derived(danlu → xanlu)
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Derived(_)));
        if let ProofRule::Derived((label, _)) = &root_step.rule {
            assert!(label.contains("xanlu"));
        }
        assert_eq!(root_step.children.len(), 1);

        // Child: Derived(gerku → danlu)
        let mid_step = &trace.steps[root_step.children[0] as usize];
        assert!(mid_step.holds);
        assert!(matches!(&mid_step.rule, ProofRule::Derived(_)));
        assert_eq!(mid_step.children.len(), 1);

        // Grandchild: Asserted(gerku(alis))
        let leaf_step = &trace.steps[mid_step.children[0] as usize];
        assert!(leaf_step.holds);
        assert!(matches!(&leaf_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_derived_depth_limit() {
        // Self-referencing rule: gerku → gerku. Asserted fact should be found first,
        // preventing infinite backward-chaining.
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "gerku"));
        let (result, trace) = query_with_proof(&kb, make_query("alis", "gerku"));
        assert!(result);
        // Should not panic or infinite-loop. Asserted is checked first.
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_proof_trace_xorlo_presup_is_asserted() {
        // Universal "ro lo gerku cu danlu" creates xorlo presupposition Skolem.
        // That fact should show as Asserted, not trigger backward-chaining.
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu"));
        // xorlo presupposition creates sk_0 as a gerku
        let (result, trace) = query_with_proof(&kb, make_query("sk_0", "gerku"));
        assert!(result);
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::Asserted(_)));
    }

    #[test]
    fn test_sexp_pattern_matching() {
        // Test the s-expression pattern matcher directly
        let var_names = vec!["x__v0".to_string()];

        // Simple predicate match
        let pattern = r#"(Pred "gerku" (Cons x__v0 (Cons (Zoe) (Nil))))"#;
        let concrete = r#"(Pred "gerku" (Cons (Const "alis") (Cons (Zoe) (Nil))))"#;
        let bindings = sexp_match(pattern, concrete, &var_names).unwrap();
        assert_eq!(bindings.get("x__v0").unwrap(), r#"(Const "alis")"#);

        // Non-matching predicate name
        let wrong = r#"(Pred "mlatu" (Cons (Const "alis") (Cons (Zoe) (Nil))))"#;
        assert!(sexp_match(pattern, wrong, &var_names).is_none());

        // Substitution
        let template = r#"(Pred "danlu" (Cons x__v0 (Cons (Zoe) (Nil))))"#;
        let result = sexp_substitute(template, &bindings);
        assert!(result.contains(r#"Const "alis""#));
        assert!(result.contains("danlu"));
    }

    // ─── Conjunction Introduction (Guarded) Tests ────────────────────

    /// Helper: check whether an IsTrue(And(...)) exists in the e-graph.
    fn egraph_has_conjunction(kb: &KnowledgeBase, pred1: &str, entity1: &str, pred2: &str, entity2: &str) -> bool {
        let mut inner = kb.inner.borrow_mut();
        let cmd = format!(
            "(check (IsTrue (And (Pred \"{}\" (Cons (Const \"{}\") (Cons (Zoe) (Nil)))) (Pred \"{}\" (Cons (Const \"{}\") (Cons (Zoe) (Nil)))))))",
            pred1, entity1, pred2, entity2
        );
        inner.egraph.parse_and_run_program(None, &cmd).is_ok()
    }

    #[test]
    fn test_conjunction_introduction_basic() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "barda"));

        // Both share entity "alis" in x1 → conjunction should exist
        assert!(
            egraph_has_conjunction(&kb, "gerku", "alis", "barda", "alis"),
            "And(gerku(alis), barda(alis)) should be derived"
        );
        // Commutativity: reversed order should also hold
        assert!(
            egraph_has_conjunction(&kb, "barda", "alis", "gerku", "alis"),
            "And(barda(alis), gerku(alis)) should be derived (commutativity)"
        );
    }

    #[test]
    fn test_conjunction_introduction_no_shared_entity() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));

        // No shared entity → conjunction should NOT exist
        assert!(
            !egraph_has_conjunction(&kb, "gerku", "alis", "mlatu", "bob"),
            "And(gerku(alis), mlatu(bob)) should NOT be derived (no shared entity)"
        );
    }

    #[test]
    fn test_conjunction_introduction_with_derived() {
        let kb = new_kb();
        assert_buf(&kb, make_universal("gerku", "danlu")); // All dogs are animals
        assert_buf(&kb, make_assertion("alis", "gerku"));   // Alice is a dog
        assert_buf(&kb, make_assertion("alis", "barda"));   // Alice is big

        // Rule derives danlu(alis). Conjunction introduction should combine derived + asserted.
        assert!(
            egraph_has_conjunction(&kb, "danlu", "alis", "barda", "alis"),
            "And(danlu(alis), barda(alis)) should be derived via rule + conjunction intro"
        );
        // Also: gerku(alis) ∧ danlu(alis) (asserted + derived)
        assert!(
            egraph_has_conjunction(&kb, "gerku", "alis", "danlu", "alis"),
            "And(gerku(alis), danlu(alis)) should be derived"
        );
    }

    #[test]
    fn test_conjunction_introduction_cross_position() {
        // nelci(bob, alis) and gerku(alis) share "alis" across x2 and x1
        let kb = new_kb();

        // gerku(alis, _)
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // nelci(bob, alis, _)
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Check: And(gerku(alis,_), nelci(bob,alis,_)) should exist
        let mut inner = kb.inner.borrow_mut();
        let cmd = "(check (IsTrue (And (Pred \"gerku\" (Cons (Const \"alis\") (Cons (Zoe) (Nil)))) (Pred \"nelci\" (Cons (Const \"bob\") (Cons (Const \"alis\") (Cons (Zoe) (Nil))))))))";
        assert!(
            inner.egraph.parse_and_run_program(None, cmd).is_ok(),
            "Cross-position entity sharing should trigger conjunction introduction"
        );
    }

    // ─── SE-conversion + universal rule + targeted witness tests ────

    /// Build a 2-arg universal rule with different argument structures:
    /// ∀x. restrictor(x, _) → consequent(fixed_entity, x, _)
    /// This simulates "ro lo gerku cu se nelci la .bob." where SE swaps x1↔x2,
    /// producing: ∀x. gerku(x) → nelci(bob, x)
    fn make_universal_2arg(
        restrictor: &str,
        consequent: &str,
        fixed_entity: &str,
    ) -> LogicBuffer {
        let mut nodes = Vec::new();
        // restrictor(x, _)
        let restrict = pred(
            &mut nodes,
            restrictor,
            vec![LogicalTerm::Variable("_v0".to_string()), LogicalTerm::Unspecified],
        );
        // consequent(fixed_entity, x, _)
        let body = pred(
            &mut nodes,
            consequent,
            vec![
                LogicalTerm::Constant(fixed_entity.to_string()),
                LogicalTerm::Variable("_v0".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let neg = not(&mut nodes, restrict);
        let disj = or(&mut nodes, neg, body);
        let root = forall(&mut nodes, "_v0", disj);
        LogicBuffer { nodes, roots: vec![root] }
    }

    #[test]
    fn test_se_conversion_universal_rule() {
        // Simulates the REPL demo:
        //   la .alis. gerku          → gerku(alis)
        //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
        //   ? la .bob. nelci la .alis.        → nelci(bob, alis) = TRUE
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: nelci(bob, alis) — should be TRUE via universal rule
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_se_conversion_universal_multiple_entities() {
        // Two dogs: both should be liked by bob via universal rule
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("rex", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // nelci(bob, alis) = TRUE
        let mut n1 = Vec::new();
        let r1 = pred(
            &mut n1,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("alis".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: n1, roots: vec![r1] }));

        // nelci(bob, rex) = TRUE
        let mut n2 = Vec::new();
        let r2 = pred(
            &mut n2,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("rex".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: n2, roots: vec![r2] }));

        // nelci(bob, carol) = FALSE (carol is not a dog)
        let mut n3 = Vec::new();
        let r3 = pred(
            &mut n3,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Constant("carol".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        assert!(!query(&kb, LogicBuffer { nodes: n3, roots: vec![r3] }));
    }

    #[test]
    fn test_targeted_witness_search_with_fixed_entity() {
        // Simulates the REPL demo:
        //   la .alis. gerku          → gerku(alis)
        //   ro lo gerku cu se nelci la .bob.  → ∀x. gerku(x) → nelci(bob, x)
        //   ?? ma se nelci la .bob.           → ∃x. nelci(bob, x) → includes alis
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: ∃x. nelci(bob, x) — should find alis (+ presupposition Skolem)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 1);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
    }

    #[test]
    fn test_targeted_witness_search_multiple_matches() {
        // Two dogs → both should appear as witnesses for "who does bob like?"
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("rex", "gerku"));
        assert_buf(&kb, make_universal_2arg("gerku", "nelci", "bob"));

        // Query: ∃x. nelci(bob, x) — should find alis AND rex (+ presupposition Skolem)
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        let results = query_find(&kb, LogicBuffer { nodes, roots: vec![root] });

        assert!(results.len() >= 2);
        let found: Vec<String> = results.iter().filter_map(|bs| {
            match &bs[0].term { LogicalTerm::Constant(c) => Some(c.clone()), _ => None }
        }).collect();
        assert!(found.contains(&"alis".to_string()), "alis should be a witness");
        assert!(found.contains(&"rex".to_string()), "rex should be a witness");
    }

    #[test]
    fn test_conjunction_introduction_multiple_entities() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "barda"));
        assert_buf(&kb, make_assertion("bob", "mlatu"));
        assert_buf(&kb, make_assertion("bob", "cmalu"));

        // alis predicates should conjoin with each other
        assert!(egraph_has_conjunction(&kb, "gerku", "alis", "barda", "alis"));
        // bob predicates should conjoin with each other
        assert!(egraph_has_conjunction(&kb, "mlatu", "bob", "cmalu", "bob"));
        // cross-entity should NOT conjoin
        assert!(!egraph_has_conjunction(&kb, "gerku", "alis", "mlatu", "bob"));
    }

    // ─── KB Reset Tests ──────────────────────────────────────────

    #[test]
    fn test_kb_reset_clears_facts() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert!(query(&kb, make_query("alis", "gerku")));

        // Reset the knowledge base
        kb.inner.borrow_mut().reset();

        // After reset, previously asserted fact should no longer hold
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_kb_reset_clears_rules() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(query(&kb, make_query("alis", "danlu")));

        kb.inner.borrow_mut().reset();

        // After reset, re-assert the fact but not the rule
        assert_buf(&kb, make_assertion("alis", "gerku"));
        // Rule should not exist anymore
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_kb_reset_resets_skolem_counter() {
        let kb = new_kb();
        // Assert a universal to trigger Skolem generation
        assert_buf(&kb, make_universal("gerku", "danlu"));
        let counter_before = kb.inner.borrow().skolem_counter;
        assert!(counter_before > 0);

        kb.inner.borrow_mut().reset();
        assert_eq!(kb.inner.borrow().skolem_counter, 0);
    }

    // ─── Empty buffer / edge case tests ──────────────────────────

    #[test]
    fn test_query_with_no_facts() {
        let kb = new_kb();
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_assert_and_query_same_fact_twice() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("alis", "gerku"));
        // Should still hold and not cause issues
        assert!(query(&kb, make_query("alis", "gerku")));
    }

    // ─── Disjunction query tests ─────────────────────────────────

    #[test]
    fn test_disjunction_left_true() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_disjunction_right_true() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "mlatu"));

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_disjunction_both_false() {
        let kb = new_kb();

        let mut nodes = Vec::new();
        let left = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let right = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = or(&mut nodes, left, right);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Double negation tests ───────────────────────────────────

    #[test]
    fn test_double_negation_elimination() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Query Not(Not(gerku(alis))) → should be TRUE
        let mut nodes = Vec::new();
        let inner = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let neg1 = not(&mut nodes, inner);
        let root = not(&mut nodes, neg1);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Tense wrapper tests ─────────────────────────────────────

    fn past(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PastNode(inner));
        id
    }

    fn present(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::PresentNode(inner));
        id
    }

    fn future(nodes: &mut Vec<LogicNode>, inner: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::FutureNode(inner));
        id
    }

    #[test]
    fn test_past_tense_wrapper_assert_query() {
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        // Query same tense wrapper → TRUE
        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_tense_not_transparent() {
        // Assert Past(klama(alis)), query klama(alis) without tense → FALSE
        // (tense is NOT transparent — tensed assertion ≠ timeless query)
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        assert!(!query(&kb, make_query("alis", "klama")));
    }

    #[test]
    fn test_tense_discrimination_past_vs_future() {
        // Assert Past(klama(alis)), query Future(klama(alis)) → FALSE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = past(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = future(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_tense_discrimination_present_vs_past() {
        // Assert Present(klama(alis)), query Past(klama(alis)) → FALSE
        let kb = new_kb();
        let mut a_nodes = Vec::new();
        let inner = pred(
            &mut a_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let root = present(&mut a_nodes, inner);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![root] });

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_untensed_assert_tensed_query() {
        // Assert klama(alis) (bare/timeless), query Past(klama(alis)) → FALSE
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "klama"));

        let mut q_nodes = Vec::new();
        let q_inner = pred(
            &mut q_nodes,
            "klama",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let q_root = past(&mut q_nodes, q_inner);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_temporal_rule_lifting() {
        // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
        // Assert: Past(gerku(alis))
        // Query: Past(danlu(alis)) → TRUE (temporal lifting)
        let kb = new_kb();

        // Compile the universal rule: ForAll(x, Or(Not(gerku(x)), danlu(x)))
        let mut r_nodes = Vec::new();
        let gerku = pred(
            &mut r_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let danlu = pred(
            &mut r_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let neg_gerku = not(&mut r_nodes, gerku);
        let impl_body = or(&mut r_nodes, neg_gerku, danlu);
        let forall = {
            let id = r_nodes.len() as u32;
            r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
            id
        };
        assert_buf(&kb, LogicBuffer { nodes: r_nodes, roots: vec![forall] });

        // Assert Past(gerku(alis))
        let mut a_nodes = Vec::new();
        let gerku_alis = pred(
            &mut a_nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_gerku = past(&mut a_nodes, gerku_alis);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![past_gerku] });

        // Query Past(danlu(alis)) → TRUE (lifted rule fires on Past premises)
        let mut q_nodes = Vec::new();
        let danlu_alis = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_danlu = past(&mut q_nodes, danlu_alis);
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![past_danlu] }));
    }

    #[test]
    fn test_temporal_rule_no_cross_tense() {
        // Assert: ∀x. gerku(x) → danlu(x) (timeless rule)
        // Assert: Past(gerku(alis))
        // Query: Future(danlu(alis)) → FALSE (no cross-tense derivation)
        let kb = new_kb();

        // Universal rule
        let mut r_nodes = Vec::new();
        let gerku = pred(
            &mut r_nodes,
            "gerku",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let danlu = pred(
            &mut r_nodes,
            "danlu",
            vec![LogicalTerm::Variable("_v0".into()), LogicalTerm::Unspecified],
        );
        let neg_gerku = not(&mut r_nodes, gerku);
        let impl_body = or(&mut r_nodes, neg_gerku, danlu);
        let forall = {
            let id = r_nodes.len() as u32;
            r_nodes.push(LogicNode::ForAllNode(("_v0".into(), impl_body)));
            id
        };
        assert_buf(&kb, LogicBuffer { nodes: r_nodes, roots: vec![forall] });

        // Assert Past(gerku(alis))
        let mut a_nodes = Vec::new();
        let gerku_alis = pred(
            &mut a_nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let past_gerku = past(&mut a_nodes, gerku_alis);
        assert_buf(&kb, LogicBuffer { nodes: a_nodes, roots: vec![past_gerku] });

        // Query Future(danlu(alis)) → FALSE (Past ≠ Future)
        let mut q_nodes = Vec::new();
        let danlu_alis = pred(
            &mut q_nodes,
            "danlu",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let future_danlu = future(&mut q_nodes, danlu_alis);
        assert!(!query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![future_danlu] }));
    }

    // ─── Multiple roots test ─────────────────────────────────────

    #[test]
    fn test_assert_multiple_roots() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let r1 = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Constant("alis".into()), LogicalTerm::Unspecified],
        );
        let r2 = pred(
            &mut nodes,
            "mlatu",
            vec![LogicalTerm::Constant("bob".into()), LogicalTerm::Unspecified],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![r1, r2] });

        assert!(query(&kb, make_query("alis", "gerku")));
        assert!(query(&kb, make_query("bob", "mlatu")));
    }

    // ─── Count quantifier test ───────────────────────────────────

    fn count(nodes: &mut Vec<LogicNode>, var: &str, cnt: u32, body: u32) -> u32 {
        let id = nodes.len() as u32;
        nodes.push(LogicNode::CountNode((var.to_string(), cnt, body)));
        id
    }

    #[test]
    fn test_count_exact_match() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));
        assert_buf(&kb, make_assertion("bob", "gerku"));

        // Count(x, 2, gerku(x, _)) → exactly 2 dogs
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = count(&mut nodes, "x", 2, body);
        assert!(query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    #[test]
    fn test_count_mismatch() {
        let kb = new_kb();
        assert_buf(&kb, make_assertion("alis", "gerku"));

        // Count(x, 2, gerku(x, _)) → only 1 dog, not 2
        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "gerku",
            vec![LogicalTerm::Variable("x".into()), LogicalTerm::Unspecified],
        );
        let root = count(&mut nodes, "x", 2, body);
        assert!(!query(&kb, LogicBuffer { nodes, roots: vec![root] }));
    }

    // ─── Compute builtin arithmetic tests ────────────────────────

    #[test]
    fn test_compute_pilji_correct() {
        let kb = new_kb();
        let buf = make_compute_query("pilji", 6.0, 2.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_pilji_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("pilji", 7.0, 2.0, 3.0);
        assert!(!query(&kb, buf));
    }

    #[test]
    fn test_compute_sumji_correct() {
        let kb = new_kb();
        let buf = make_compute_query("sumji", 5.0, 2.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_sumji_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("sumji", 6.0, 2.0, 3.0);
        assert!(!query(&kb, buf));
    }

    #[test]
    fn test_compute_dilcu_correct() {
        let kb = new_kb();
        let buf = make_compute_query("dilcu", 2.0, 6.0, 3.0);
        assert!(query(&kb, buf));
    }

    #[test]
    fn test_compute_dilcu_incorrect() {
        let kb = new_kb();
        let buf = make_compute_query("dilcu", 3.0, 6.0, 3.0);
        assert!(!query(&kb, buf));
    }

    // ─── Numerical comparison predicate tests ────────────────────

    #[test]
    fn test_zmadu_greater_than() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("zmadu", 5.0, 3.0)));
    }

    #[test]
    fn test_zmadu_not_greater() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("zmadu", 3.0, 5.0)));
    }

    #[test]
    fn test_mleca_less_than() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("mleca", 3.0, 5.0)));
    }

    #[test]
    fn test_dunli_equal() {
        let kb = new_kb();
        assert!(query(&kb, make_numeric_query("dunli", 5.0, 5.0)));
    }

    #[test]
    fn test_dunli_not_equal() {
        let kb = new_kb();
        assert!(!query(&kb, make_numeric_query("dunli", 5.0, 3.0)));
    }

    // ─── Assert fact with various term types ──────────────────────

    #[test]
    fn test_assert_fact_with_number_terms() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Query the same fact back
        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "pilji",
            vec![
                LogicalTerm::Number(6.0),
                LogicalTerm::Number(2.0),
                LogicalTerm::Number(3.0),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    #[test]
    fn test_assert_fact_with_description_terms() {
        let kb = new_kb();
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Description("lo_gerku".to_string()),
            ],
        );
        assert_buf(&kb, LogicBuffer { nodes, roots: vec![root] });

        // Query back
        let mut q_nodes = Vec::new();
        let q_root = pred(
            &mut q_nodes,
            "nelci",
            vec![
                LogicalTerm::Constant("bob".to_string()),
                LogicalTerm::Description("lo_gerku".to_string()),
            ],
        );
        assert!(query(&kb, LogicBuffer { nodes: q_nodes, roots: vec![q_root] }));
    }

    // ─── Fact Registry / Retraction Tests ────────────────────────────

    #[test]
    fn test_retract_basic() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), "la alis gerku".into()).unwrap();
        assert!(query(&kb, make_query("alis", "gerku")));
        kb.retract_fact_inner(id).unwrap();
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_retract_preserves_other_facts() {
        let kb = new_kb();
        let id1 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let _id2 = kb.assert_fact_inner(make_assertion("bob", "mlatu"), String::new()).unwrap();
        kb.retract_fact_inner(id1).unwrap();
        assert!(!query(&kb, make_query("alis", "gerku")));
        assert!(query(&kb, make_query("bob", "mlatu")));
    }

    #[test]
    fn test_retract_derived_facts_gone() {
        let kb = new_kb();
        let base_id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let _rule_id = kb.assert_fact_inner(make_universal("gerku", "danlu"), String::new()).unwrap();
        // "alis danlu" should be derivable via the rule
        assert!(query(&kb, make_query("alis", "danlu")));
        kb.retract_fact_inner(base_id).unwrap();
        // After retracting the base fact, "alis danlu" should no longer hold
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_retract_rule_preserves_base_facts() {
        let kb = new_kb();
        let _base_id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        let rule_id = kb.assert_fact_inner(make_universal("gerku", "danlu"), String::new()).unwrap();
        assert!(query(&kb, make_query("alis", "danlu")));
        kb.retract_fact_inner(rule_id).unwrap();
        // Base fact preserved
        assert!(query(&kb, make_query("alis", "gerku")));
        // Derived fact gone (rule retracted)
        assert!(!query(&kb, make_query("alis", "danlu")));
    }

    #[test]
    fn test_retract_and_reassert_new_id() {
        let kb = new_kb();
        let id1 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.retract_fact_inner(id1).unwrap();
        let id2 = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        assert!(id2 > id1);
        assert!(query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_retract_nonexistent_errors() {
        let kb = new_kb();
        assert!(kb.retract_fact_inner(999).is_err());
    }

    #[test]
    fn test_retract_idempotent() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.retract_fact_inner(id).unwrap();
        kb.retract_fact_inner(id).unwrap(); // second retract is no-op
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    #[test]
    fn test_list_facts_empty() {
        let kb = new_kb();
        let facts = kb.list_facts_inner().unwrap();
        assert!(facts.is_empty());
    }

    #[test]
    fn test_list_facts_after_assert() {
        let kb = new_kb();
        kb.assert_fact_inner(make_assertion("alis", "gerku"), "la alis gerku".into()).unwrap();
        let facts = kb.list_facts_inner().unwrap();
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].label, "la alis gerku");
        assert_eq!(facts[0].root_count, 1);
    }

    #[test]
    fn test_list_facts_excludes_retracted() {
        let kb = new_kb();
        let id = kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.assert_fact_inner(make_assertion("bob", "mlatu"), "bob mlatu".into()).unwrap();
        kb.retract_fact_inner(id).unwrap();
        let facts = kb.list_facts_inner().unwrap();
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].id, 1); // bob's fact
        assert_eq!(facts[0].label, "bob mlatu");
    }

    #[test]
    fn test_reset_clears_registry() {
        let kb = new_kb();
        kb.assert_fact_inner(make_assertion("alis", "gerku"), String::new()).unwrap();
        kb.inner.borrow_mut().reset();
        let facts = kb.list_facts_inner().unwrap();
        assert!(facts.is_empty());
        assert!(!query(&kb, make_query("alis", "gerku")));
    }

    // ─── C5: Description term opacity tests ──────────────────────

    /// Helper: make an assertion with a Description term in x1.
    fn make_desc_assertion(desc_name: &str, predicate: &str) -> LogicBuffer {
        let mut nodes = Vec::new();
        let root = pred(
            &mut nodes,
            predicate,
            vec![
                LogicalTerm::Description(desc_name.to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        LogicBuffer { nodes, roots: vec![root] }
    }

    /// Helper: make a query with a Description term in x1.
    fn make_desc_query(desc_name: &str, predicate: &str) -> LogicBuffer {
        make_desc_assertion(desc_name, predicate)
    }

    #[test]
    fn test_desc_gets_indomain() {
        // Assert a fact with Description term → Desc should be in InDomain
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        let inner = kb.inner.borrow();
        assert!(
            inner.known_descriptions.contains("gerku"),
            "expected 'gerku' in known_descriptions"
        );
    }

    #[test]
    fn test_desc_conjunction_introduction() {
        // Two facts about same Desc term → conjunction should be derivable
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "danlu"));
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

        // Query And(danlu(Desc "gerku"), sutra(Desc "gerku"))
        let mut nodes = Vec::new();
        let p1 = pred(
            &mut nodes,
            "danlu",
            vec![
                LogicalTerm::Description("gerku".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let p2 = pred(
            &mut nodes,
            "sutra",
            vec![
                LogicalTerm::Description("gerku".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = and(&mut nodes, p1, p2);
        assert!(
            query(&kb, LogicBuffer { nodes, roots: vec![root] }),
            "conjunction of two Desc-term facts should hold via conjunction introduction"
        );
    }

    #[test]
    fn test_desc_does_not_trigger_rule_without_restrictor() {
        // Assert sutra(Desc "gerku") (but NOT gerku(Desc "gerku"))
        // Assert rule: ro lo gerku cu danlu (∀x. gerku(x) → danlu(x))
        // Query danlu(Desc "gerku") → should FAIL (the restrictor isn't satisfied)
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(
            !query(&kb, make_desc_query("gerku", "danlu")),
            "universal rule should NOT fire without restrictor being satisfied for Desc term"
        );
    }

    #[test]
    fn test_desc_triggers_rule_when_restrictor_satisfied() {
        // Assert gerku(Desc "gerku") AND sutra(Desc "gerku")
        // Assert rule: ro lo gerku cu danlu
        // Query danlu(Desc "gerku") → should SUCCEED
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "gerku"));
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));
        assert_buf(&kb, make_universal("gerku", "danlu"));
        assert!(
            query(&kb, make_desc_query("gerku", "danlu")),
            "universal rule should fire when restrictor IS satisfied for Desc term"
        );
    }

    #[test]
    fn test_desc_exists_witness() {
        // Assert sutra(Desc "gerku") → ∃x. sutra(x) should find Desc "gerku" as witness
        let kb = new_kb();
        assert_buf(&kb, make_desc_assertion("gerku", "sutra"));

        let mut nodes = Vec::new();
        let body = pred(
            &mut nodes,
            "sutra",
            vec![
                LogicalTerm::Variable("x".to_string()),
                LogicalTerm::Unspecified,
            ],
        );
        let root = exists(&mut nodes, "x", body);
        assert!(
            query(&kb, LogicBuffer { nodes, roots: vec![root] }),
            "existential query should find Desc term as witness"
        );
    }
}
