#[allow(warnings)]
mod bindings;

use crate::bindings::exports::lojban::nesy::reasoning::{Guest, GuestKnowledgeBase};
use crate::bindings::lojban::nesy::error_types::NibliError;
use crate::bindings::lojban::nesy::logic_types::{
    LogicBuffer, LogicNode, LogicalTerm, ProofRule, ProofStep, ProofTrace, WitnessBinding,
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

/// All mutable KB state behind a single RefCell.
struct KnowledgeBaseInner {
    egraph: EGraph,
    skolem_counter: usize,
    known_entities: HashSet<String>,
    known_rules: HashSet<String>,
    skolem_fn_registry: Vec<SkolemFnEntry>,
}

impl KnowledgeBaseInner {
    fn new() -> Self {
        Self {
            egraph: make_fresh_egraph(),
            skolem_counter: 0,
            known_entities: HashSet::new(),
            known_rules: HashSet::new(),
            skolem_fn_registry: Vec::new(),
        }
    }

    fn reset(&mut self) {
        self.egraph = make_fresh_egraph();
        self.skolem_counter = 0;
        self.known_entities.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
    }

    fn fresh_skolem(&mut self) -> String {
        let sk = format!("sk_{}", self.skolem_counter);
        self.skolem_counter += 1;
        sk
    }

    fn get_known_entities(&self) -> Vec<String> {
        self.known_entities.iter().cloned().collect()
    }

    fn note_entity(&mut self, name: &str) {
        let is_new = self.known_entities.insert(name.to_string());
        if is_new {
            let cmd = format!("(InDomain (Const \"{}\"))", name);
            self.egraph.parse_and_run_program(None, &cmd).ok();
        }
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
    ;; where dep_term is a Term (either Var in rules, or Const in ground facts)
    (datatype Term
        (Var String)
        (Const String)
        (Desc String)
        (Zoe)
        (Num i64)
        (SkolemFn String Term)
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
"#;

/// Create a fresh EGraph with the schema loaded.
fn make_fresh_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, SCHEMA)
        .expect("Failed to load FOL schema and rules");
    egraph
}

/// Build an egglog SkolemFn s-expression from a base name and pattern variable names.
fn build_skolem_fn_sexp(base_name: &str, pattern_var_names: &[String]) -> String {
    assert_eq!(
        pattern_var_names.len(),
        1,
        "SkolemFn currently supports dep_count=1, got {}",
        pattern_var_names.len()
    );
    format!("(SkolemFn \"{}\" {})", base_name, pattern_var_names[0])
}

/// Build a ground SkolemFn s-expression with a Const entity argument.
fn build_ground_skolem_fn(base_name: &str, entities: &[String]) -> String {
    assert_eq!(
        entities.len(),
        1,
        "SkolemFn currently supports dep_count=1, got {}",
        entities.len()
    );
    format!("(SkolemFn \"{}\" (Const \"{}\"))", base_name, entities[0])
}

/// Generate cartesian product of entities with given arity.
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

/// Internal methods that return Result<_, String> for use by both WIT boundary and tests.
impl KnowledgeBase {
    fn assert_fact_inner(&self, logic: LogicBuffer) -> Result<(), String> {
        let mut inner = self.inner.borrow_mut();

        for &root_id in &logic.roots {
            // Phase 1: Collect existential variables for Skolemization.
            let mut skolem_subs = HashMap::new();
            let mut enclosing_universals = Vec::new();
            collect_exists_for_skolem(
                &logic,
                root_id,
                &mut skolem_subs,
                &mut enclosing_universals,
                &mut inner.skolem_counter,
            );

            // Log Skolem substitutions
            if !skolem_subs.is_empty() {
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
                collect_and_note_constants(&logic, root_id, &mut inner);
                compile_forall_to_rule(&logic, root_id, &skolem_subs, &mut inner)?;
            } else {
                // ═══ GROUND FORMULA PATH ═══
                for sk in skolem_subs.values() {
                    if !sk.starts_with(SKDEP_PREFIX) {
                        inner.note_entity(sk);
                    }
                }
                collect_and_note_constants(&logic, root_id, &mut inner);

                let raw_subs: HashMap<String, String> = skolem_subs
                    .iter()
                    .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
                    .map(|(k, v)| (k.clone(), format!("(Const \"{}\")", v)))
                    .collect();
                let sexp = reconstruct_sexp_with_subs(&logic, root_id, &raw_subs);
                let command = format!("(IsTrue {})", sexp);
                inner
                    .egraph
                    .parse_and_run_program(None, &command)
                    .map_err(|e| format!("Failed to assert fact: {}", e))?;
            }

            // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
            generate_count_extra_witnesses(&logic, root_id, &skolem_subs, &mut inner);

            // Run rules to fixpoint
            inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        }

        Ok(())
    }

    fn query_entailment_inner(&self, logic: LogicBuffer) -> Result<bool, String> {
        let mut inner = self.inner.borrow_mut();
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        for &root_id in &logic.roots {
            let subs = HashMap::new();
            if !check_formula_holds(&logic, root_id, &subs, &mut inner)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn query_find_inner(&self, logic: LogicBuffer) -> Result<Vec<Vec<WitnessBinding>>, String> {
        let mut inner = self.inner.borrow_mut();
        inner.egraph.parse_and_run_program(None, "(run 100)").ok();
        let mut result_sets: Option<Vec<Vec<(String, String)>>> = None;
        for &root_id in &logic.roots {
            let subs = HashMap::new();
            let witnesses = find_witnesses(&logic, root_id, &subs, &mut inner)?;
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
                check_formula_holds_traced(&logic, root_id, &subs, &mut inner, &mut steps)?;
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

    fn assert_fact(&self, logic: LogicBuffer) -> Result<(), NibliError> {
        self.assert_fact_inner(logic).map_err(NibliError::Reasoning)
    }

    fn query_entailment(&self, logic: LogicBuffer) -> Result<bool, NibliError> {
        self.query_entailment_inner(logic).map_err(NibliError::Reasoning)
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

fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, inner)?
            && check_formula_holds(buffer, *r, subs, inner)?),
        LogicNode::OrNode((l, r)) => {
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => return Ok(true),
                Err(_) => {}
            }
            Ok(check_formula_holds(buffer, *l, subs, inner)?
                || check_formula_holds(buffer, *r, subs, inner)?)
        }
        LogicNode::NotNode(inner_node) => Ok(!check_formula_holds(buffer, *inner_node, subs, inner)?),
        LogicNode::PastNode(inner_node)
        | LogicNode::PresentNode(inner_node)
        | LogicNode::FutureNode(inner_node)
        | LogicNode::ObligatoryNode(inner_node)
        | LogicNode::PermittedNode(inner_node) => check_formula_holds(buffer, *inner_node, subs, inner),
        LogicNode::ExistsNode((v, body)) => {
            // 1. Check if any known entity satisfies the body
            let entities = inner.get_known_entities();
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                if check_formula_holds(buffer, *body, &new_subs, inner)? {
                    return Ok(true);
                }
            }
            // 2. Try SkolemFn witnesses from the registry
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let combos = cartesian_product(&entities, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_ground_skolem_fn(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp);
                    if check_formula_holds(buffer, *body, &new_subs, inner)? {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }
        LogicNode::ForAllNode((v, body)) => {
            let entities = inner.get_known_entities();
            if entities.is_empty() {
                return Ok(true);
            }
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                if !check_formula_holds(buffer, *body, &new_subs, inner)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LogicNode::CountNode((v, count, body)) => {
            let entities = inner.get_known_entities();
            let mut satisfying = 0u32;
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                if check_formula_holds(buffer, *body, &new_subs, inner)? {
                    satisfying += 1;
                }
            }
            Ok(satisfying == *count)
        }
        LogicNode::Predicate((rel, args)) => {
            // Try numeric comparison short-circuit for zmadu/mleca/dunli
            if let Some(result) = try_numeric_comparison(rel, args, subs) {
                return Ok(result);
            }
            // Standard egglog check
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
) -> Result<Vec<Vec<(String, String)>>, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            let mut results = Vec::new();

            // 1. Try each known entity as a witness
            let entities = inner.get_known_entities();
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                let sub_results = find_witnesses(buffer, *body, &new_subs, inner)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), format!("(Const \"{}\")", entity)));
                    results.push(bindings);
                }
            }

            // 2. Try SkolemFn witnesses from the registry
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let combos = cartesian_product(&entities, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_ground_skolem_fn(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    let sub_results = find_witnesses(buffer, *body, &new_subs, inner)?;
                    for mut bindings in sub_results {
                        bindings.push((v.clone(), witness_sexp.clone()));
                        results.push(bindings);
                    }
                }
            }

            Ok(results)
        }
        LogicNode::AndNode((l, r)) => {
            // Cross-product: for each left binding set, check right with merged subs
            let left_results = find_witnesses(buffer, *l, subs, inner)?;
            let mut results = Vec::new();
            for left_bindings in left_results {
                let mut merged_subs = subs.clone();
                for (k, v) in &left_bindings {
                    merged_subs.insert(k.clone(), v.clone());
                }
                let right_results = find_witnesses(buffer, *r, &merged_subs, inner)?;
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
            let mut results = find_witnesses(buffer, *l, subs, inner)?;
            results.extend(find_witnesses(buffer, *r, subs, inner)?);
            Ok(results)
        }
        // For all other node types, delegate to boolean check.
        // If the formula holds, return one empty binding set; otherwise empty.
        _ => {
            if check_formula_holds(buffer, node_id, subs, inner)? {
                Ok(vec![vec![]])
            } else {
                Ok(vec![])
            }
        }
    }
}

// ─── Proof Trace Generation ──────────────────────────────────────

/// Like `check_formula_holds` but builds a proof trace as it recurses.
/// Returns (result, step_index) where step_index is the index of this
/// step in the `steps` Vec.
fn check_formula_holds_traced(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
) -> Result<(bool, u32), String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps)?;
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps)?;
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
            // Try egglog direct check first
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::DisjunctionEgraph(sexp),
                        holds: true,
                        children: vec![],
                    });
                    return Ok((true, idx));
                }
                Err(_) => {}
            }
            // Fallback: try left then right
            let (l_result, l_idx) = check_formula_holds_traced(buffer, *l, subs, inner, steps)?;
            if l_result {
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::DisjunctionIntro("left".to_string()),
                    holds: true,
                    children: vec![l_idx],
                });
                return Ok((true, idx));
            }
            let (r_result, r_idx) = check_formula_holds_traced(buffer, *r, subs, inner, steps)?;
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
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
            let result = !inner_result;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::Negation,
                holds: result,
                children: vec![inner_idx],
            });
            Ok((result, idx))
        }
        LogicNode::PastNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
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
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
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
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("future".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::ObligatoryNode(inner_node) => {
            let (result, child_idx) =
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
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
                check_formula_holds_traced(buffer, *inner_node, subs, inner, steps)?;
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::ModalPassthrough("permitted".to_string()),
                holds: result,
                children: vec![child_idx],
            });
            Ok((result, idx))
        }
        LogicNode::ExistsNode((v, body)) => {
            // 1. Try known entities
            let entities = inner.get_known_entities();
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                let (holds, body_idx) =
                    check_formula_holds_traced(buffer, *body, &new_subs, inner, steps)?;
                if holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ExistsWitness((
                            v.clone(),
                            LogicalTerm::Constant(entity.clone()),
                        )),
                        holds: true,
                        children: vec![body_idx],
                    });
                    return Ok((true, idx));
                }
            }
            // 2. Try SkolemFn witnesses
            let entries: Vec<SkolemFnEntry> = inner.skolem_fn_registry.clone();
            for entry in &entries {
                let combos = cartesian_product(&entities, entry.dep_count);
                for combo in &combos {
                    let witness_sexp = build_ground_skolem_fn(&entry.base_name, combo);
                    let mut new_subs = subs.clone();
                    new_subs.insert(v.clone(), witness_sexp.clone());
                    let (holds, body_idx) =
                        check_formula_holds_traced(buffer, *body, &new_subs, inner, steps)?;
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
            let entities = inner.get_known_entities();
            if entities.is_empty() {
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
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                let (holds, body_idx) =
                    check_formula_holds_traced(buffer, *body, &new_subs, inner, steps)?;
                if !holds {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::ForallCounterexample(LogicalTerm::Constant(
                            entity.clone(),
                        )),
                        holds: false,
                        children: vec![body_idx],
                    });
                    return Ok((false, idx));
                }
                child_indices.push(body_idx);
                entity_terms.push(LogicalTerm::Constant(entity.clone()));
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
            let entities = inner.get_known_entities();
            let mut satisfying = 0u32;
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), format!("(Const \"{}\")", entity));
                if check_formula_holds(buffer, *body, &new_subs, inner)? {
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
            // Try numeric comparison short-circuit
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
            // Standard egglog check
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match inner.egraph.parse_and_run_program(None, &command) {
                Ok(_) => {
                    let idx = steps.len() as u32;
                    steps.push(ProofStep {
                        rule: ProofRule::PredicateCheck(("egglog".to_string(), sexp)),
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
                            rule: ProofRule::PredicateCheck(("egglog".to_string(), sexp)),
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

/// Note all Const terms found in the formula as known entities.
fn collect_and_note_constants(buffer: &LogicBuffer, node_id: u32, inner: &mut KnowledgeBaseInner) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) | LogicNode::ComputeNode((_, args)) => {
            for arg in args {
                if let LogicalTerm::Constant(c) = arg {
                    inner.note_entity(c);
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
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems, dependent_skolems)
        }
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

            let conditions_sexp: Vec<String> = all_conditions
                .iter()
                .map(|&cid| {
                    let sexp =
                        reconstruct_rule_sexp(buffer, cid, &pattern_vars, &ground_skolems, &dependent_skolems);
                    format!("(IsTrue {})", sexp)
                })
                .collect();

            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);
            let actions_sexp: Vec<String> = consequent_atoms
                .iter()
                .map(|&aid| {
                    let sexp =
                        reconstruct_rule_sexp(buffer, aid, &pattern_vars, &ground_skolems, &dependent_skolems);
                    format!("(IsTrue {})", sexp)
                })
                .collect();

            let rule = format!(
                "(rule ({}) ({}))",
                conditions_sexp.join(" "),
                actions_sexp.join(" ")
            );

            if !inner.known_rules.insert(rule.clone()) {
                println!(
                    "[Rule] ∀{} already present, skipping",
                    universals.join(",")
                );
            } else {
                println!(
                    "[Rule] Compiled ∀{} to native egglog rule",
                    universals.join(",")
                );
                inner
                    .egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile universal to rule: {}", e))?;
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
                println!(
                    "[Rule] bare ∀{} already present, skipping",
                    universals.join(",")
                );
            } else {
                println!(
                    "[Rule] Compiled bare ∀{} with InDomain trigger",
                    universals.join(",")
                );
                inner
                    .egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile bare universal to rule: {}", e))?;
            }
        }
    }

    Ok(())
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
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
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
        kb.assert_fact_inner(buf).unwrap();
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
        // Query ∃x.danlu(x) → x = alis (derived via rule)
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

        assert_eq!(results.len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "alis"));
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
        // Query ∃x.xanlu(x) → x = alis (derived via 2-hop chain)
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

        assert_eq!(results.len(), 1);
        assert_eq!(results[0][0].variable, "x");
        assert!(matches!(&results[0][0].term, LogicalTerm::Constant(c) if c == "alis"));
    }

    // ─── Proof trace tests ───────────────────────────────────────

    fn query_with_proof(kb: &KnowledgeBase, buf: LogicBuffer) -> (bool, ProofTrace) {
        kb.query_entailment_with_proof_inner(buf).unwrap()
    }

    #[test]
    fn test_proof_trace_simple_predicate() {
        // Assert klama(mi), query it → single predicate-check step, result true
        let kb = new_kb();
        assert_buf(&kb, make_assertion("mi", "klama"));
        let (result, trace) = query_with_proof(&kb, make_query("mi", "klama"));

        assert!(result);
        assert!(!trace.steps.is_empty());
        let root_step = &trace.steps[trace.root as usize];
        assert!(root_step.holds);
        assert!(matches!(&root_step.rule, ProofRule::PredicateCheck(_)));
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
        // Both children should be predicate-check with result true
        for &child in &root_step.children {
            let child_step = &trace.steps[child as usize];
            assert!(child_step.holds);
            assert!(matches!(&child_step.rule, ProofRule::PredicateCheck(_)));
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
}
