#[allow(warnings)]
mod bindings;

use crate::bindings::exports::lojban::nesy::reasoning::Guest;
use crate::bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};
use egglog::EGraph;
use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

// ─── Global Persistent State ──────────────────────────────────────

static EGRAPH: OnceLock<Mutex<EGraph>> = OnceLock::new();
static SKOLEM_COUNTER: OnceLock<Mutex<usize>> = OnceLock::new();
static KNOWN_ENTITIES: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
static UNIVERSAL_TEMPLATES: OnceLock<Mutex<Vec<UniversalTemplate>>> = OnceLock::new();

/// A stored universal formula for Herbrand instantiation.
/// When new entities appear, we instantiate the template for each.
struct UniversalTemplate {
    var_name: String,
    /// The body s-expression with (Var "var_name") as placeholder.
    /// Dependent Skolem variables appear as (Var "__skdep__sk_N").
    body_sexp: String,
    /// Dependent Skolem placeholders: (placeholder_var_name, base_skolem_name).
    /// For ∃ nested under ∀, each gets a unique constant per entity:
    /// e.g., base "sk_1" + entity "alice" → "sk_1_alice".
    dependent_skolems: Vec<(String, String)>,
}

/// Prefix used for dependent Skolem placeholder variables.
/// A dependent Skolem is an ∃ variable nested under a ∀.
/// These remain as (Var "...") in the template sexp and get replaced
/// with entity-specific constants during Herbrand instantiation.
const SKDEP_PREFIX: &str = "__skdep__";

/// The egglog schema and inference rules, shared between init and reset.
/// NOTE: Num added to Term datatype (bug 0.5 fix).
const SCHEMA: &str = r#"
    ;; ═══════════════════════════════════════════════════
    ;; Lojban NeSy Engine — FOL Schema & Rules
    ;; Phase 6b: Skolemization + Herbrand instantiation
    ;; ═══════════════════════════════════════════════════

    ;; Atomic Terms
    (datatype Term
        (Var String)
        (Const String)
        (Desc String)
        (Zoe)
        (Num i64)
    )

    ;; Variadic Argument List (Linked List)
    (datatype TermList
        (Nil)
        (Cons Term TermList)
    )

    ;; Well-Formed Formulas
    (datatype Formula
        (Pred String TermList)
        (And Formula Formula)
        (Or Formula Formula)
        (Not Formula)
        (Implies Formula Formula)
        (Exists String Formula)
        (ForAll String Formula)
    )

    ;; The Knowledge Base
    (relation IsTrue (Formula))

    ;; ───────────────────────────────────────────────────
    ;; STRUCTURAL REWRITES
    ;; ───────────────────────────────────────────────────

    ;; Commutativity
    (rewrite (And A B) (And B A))
    (rewrite (Or A B) (Or B A))

    ;; Associativity
    (rewrite (And (And A B) C) (And A (And B C)))
    (rewrite (Or (Or A B) C) (Or A (Or B C)))

    ;; Double negation elimination
    (rewrite (Not (Not A)) A)

    ;; De Morgan's Laws
    (rewrite (Not (And A B)) (Or (Not A) (Not B)))
    (rewrite (Not (Or A B)) (And (Not A) (Not B)))

    ;; Material conditional elimination
    (rewrite (Implies A B) (Or (Not A) B))

    ;; ───────────────────────────────────────────────────
    ;; INFERENCE RULES
    ;; ───────────────────────────────────────────────────

    ;; Conjunction Elimination
    (rule ((IsTrue (And A B)))
          ((IsTrue A) (IsTrue B)))

    ;; Disjunctive Syllogism: A ∨ B, ¬A ⊢ B
    (rule ((IsTrue (Or A B)) (IsTrue (Not A)))
          ((IsTrue B)))

    ;; Modus Ponens (disjunctive form): ¬A ∨ B, A ⊢ B
    ;; Critical for universal instantiation: ∀x.(¬R(x) ∨ P(x)) + R(e) ⊢ P(e)
    ;; Cannot rely on double negation to bridge because egglog rewrites
    ;; are directional — Not(Not(A)) is never created from A alone.
    (rule ((IsTrue (Or (Not A) B)) (IsTrue A))
          ((IsTrue B)))

    ;; Modus Ponens
    (rule ((IsTrue (Implies A B)) (IsTrue A))
          ((IsTrue B)))

    ;; Modus Tollens
    (rule ((IsTrue (Implies A B)) (IsTrue (Not B)))
          ((IsTrue (Not A))))

    ;; ───────────────────────────────────────────────────
    ;; QUANTIFIER RULES (residual)
    ;; ───────────────────────────────────────────────────

    ;; ∀-distribution over ∧
    (rule ((IsTrue (ForAll v (And A B))))
          ((IsTrue (And (ForAll v A) (ForAll v B)))))
"#;

/// Create a fresh EGraph with the schema loaded.
fn make_fresh_egraph() -> EGraph {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, SCHEMA)
        .expect("Failed to load FOL schema and rules");
    egraph
}

fn fresh_skolem() -> String {
    let counter = SKOLEM_COUNTER.get_or_init(|| Mutex::new(0));
    let mut c = counter.lock().unwrap();
    let sk = format!("sk_{}", *c);
    *c += 1;
    sk
}

/// Register an entity and instantiate all stored universals for it.
/// Returns true if the entity was NEW (not previously known).
fn register_entity(name: &str, egraph: &mut EGraph) -> bool {
    let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
    let is_new = entities.lock().unwrap().insert(name.to_string());

    if is_new {
        // Instantiate all stored universals for the new entity
        let templates = UNIVERSAL_TEMPLATES.get_or_init(|| Mutex::new(Vec::new()));
        let templates_guard = templates.lock().unwrap();
        for tmpl in templates_guard.iter() {
            let instantiated = instantiate_for_entity(
                &tmpl.body_sexp,
                &tmpl.var_name,
                name,
                &tmpl.dependent_skolems,
            );
            // Register entity-specific Skolem constants (without triggering
            // further universal instantiation — avoids infinite expansion).
            for (_, base_name) in &tmpl.dependent_skolems {
                let unique_sk = format!("{}_{}", base_name, name);
                entities.lock().unwrap().insert(unique_sk);
            }
            let command = format!("(IsTrue {})", instantiated);
            if let Err(e) = egraph.parse_and_run_program(None, &command) {
                eprintln!(
                    "[reasoning] Failed to instantiate universal for {}: {}",
                    name, e
                );
            }
        }
    }

    is_new
}

fn get_known_entities() -> Vec<String> {
    let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
    entities.lock().unwrap().iter().cloned().collect()
}

fn get_egraph() -> &'static Mutex<EGraph> {
    EGRAPH.get_or_init(|| Mutex::new(make_fresh_egraph()))
}

/// Register an entity WITHOUT triggering universal template instantiation.
/// Used for Skolem-generated witnesses to avoid infinite expansion:
/// if we instantiated universals for Skolem witnesses, those could create
/// more Skolem witnesses → infinite loop.
fn register_entity_no_instantiate(name: &str) {
    let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
    entities.lock().unwrap().insert(name.to_string());
}

/// Instantiate a universal template body for a specific entity.
/// Replaces the ∀ variable AND generates per-entity Skolem constants
/// for any dependent Skolems (∃ under ∀).
fn instantiate_for_entity(
    body_sexp: &str,
    var_name: &str,
    entity: &str,
    dependent_skolems: &[(String, String)],
) -> String {
    let mut result = body_sexp.replace(
        &format!("(Var \"{}\")", var_name),
        &format!("(Const \"{}\")", entity),
    );
    for (placeholder, base_name) in dependent_skolems {
        let unique_sk = format!("{}_{}", base_name, entity);
        result = result.replace(
            &format!("(Var \"{}\")", placeholder),
            &format!("(Const \"{}\")", unique_sk),
        );
    }
    result
}

// ─── WIT Export Implementation ────────────────────────────────────

struct ReasoningComponent;

impl Guest for ReasoningComponent {
    /// Assert facts with Skolemization (∃) and Herbrand instantiation (∀).
    fn assert_fact(logic: LogicBuffer) -> Result<(), String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        for &root_id in &logic.roots {
            // Phase 1: Collect existential variables for Skolemization.
            // Tracks enclosing universals to detect ∃-under-∀ (dependent Skolems).
            let mut skolem_subs = HashMap::new();
            let mut enclosing_universals = Vec::new();
            collect_exists_for_skolem(&logic, root_id, &mut skolem_subs, &mut enclosing_universals);

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

            // Register ONLY independent Skolem constants as entities.
            // Dependent Skolems get registered per-entity during Herbrand instantiation.
            for sk in skolem_subs.values() {
                if !sk.starts_with(SKDEP_PREFIX) {
                    register_entity(sk, &mut egraph);
                }
            }

            // Register named constants as entities
            collect_and_register_constants(&logic, root_id, &mut egraph);

            // Phase 2: Check for ForAll nodes and handle Herbrand instantiation
            let forall_entries = collect_forall_nodes(&logic, root_id, &skolem_subs);

            if !forall_entries.is_empty() {
                for (var_name, body_sexp, dependent_skolems) in &forall_entries {
                    println!(
                        "[Universal] ∀{} registered for Herbrand instantiation",
                        var_name
                    );
                    if !dependent_skolems.is_empty() {
                        let deps: Vec<&str> = dependent_skolems
                            .iter()
                            .map(|(_, base)| base.as_str())
                            .collect();
                        println!(
                            "[Skolem] {} dependent witness(es): {} (unique per entity)",
                            dependent_skolems.len(),
                            deps.join(", ")
                        );
                    }

                    // Store template for future entity registration
                    let templates = UNIVERSAL_TEMPLATES.get_or_init(|| Mutex::new(Vec::new()));
                    templates.lock().unwrap().push(UniversalTemplate {
                        var_name: var_name.clone(),
                        body_sexp: body_sexp.clone(),
                        dependent_skolems: dependent_skolems.clone(),
                    });

                    // Instantiate for all currently known entities
                    let entities = get_known_entities();
                    for entity in &entities {
                        let instantiated =
                            instantiate_for_entity(body_sexp, var_name, entity, dependent_skolems);
                        // Register entity-specific Skolem constants
                        for (_, base_name) in dependent_skolems {
                            let unique_sk = format!("{}_{}", base_name, entity);
                            register_entity_no_instantiate(&unique_sk);
                        }
                        let command = format!("(IsTrue {})", instantiated);
                        if let Err(e) = egraph.parse_and_run_program(None, &command) {
                            eprintln!(
                                "[reasoning] Failed to instantiate ∀{} for {}: {}",
                                var_name, entity, e
                            );
                        }
                    }
                }
            } else {
                // No universals — just assert the ground formula
                let sexp = reconstruct_sexp_with_subs(&logic, root_id, &skolem_subs);
                let command = format!("(IsTrue {})", sexp);
                egraph
                    .parse_and_run_program(None, &command)
                    .map_err(|e| format!("Failed to assert fact: {}", e))?;
            }

            // Run rules to fixpoint
            egraph.parse_and_run_program(None, "(run 100)").ok();
        }

        Ok(())
    }

    fn query_entailment(logic: LogicBuffer) -> Result<bool, String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        // Run rules to fixpoint before querying
        egraph.parse_and_run_program(None, "(run 100)").ok();

        for &root_id in &logic.roots {
            let subs = HashMap::new();
            if !check_formula_holds(&logic, root_id, &subs, &mut egraph)? {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Clear the knowledge base, Skolem counter, entity registry,
    /// and universal templates. Returns to a fresh-boot state.
    fn reset_state() -> Result<(), String> {
        // 1. Replace e-graph with a fresh one (schema reloaded)
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();
        *egraph = make_fresh_egraph();

        // 2. Reset Skolem counter to 0
        let counter = SKOLEM_COUNTER.get_or_init(|| Mutex::new(0));
        *counter.lock().unwrap() = 0;

        // 3. Clear known entities
        let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
        entities.lock().unwrap().clear();

        // 4. Clear universal templates
        let templates = UNIVERSAL_TEMPLATES.get_or_init(|| Mutex::new(Vec::new()));
        templates.lock().unwrap().clear();

        Ok(())
    }
}

// ─── Query Decomposition ─────────────────────────────────────────

fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    egraph: &mut EGraph,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => Ok(check_formula_holds(buffer, *l, subs, egraph)?
            && check_formula_holds(buffer, *r, subs, egraph)?),
        LogicNode::OrNode((l, r)) => {
            // First: check if the compound (Or A B) itself is in the e-graph.
            // This catches cases like `mi klama ja bajra` where (IsTrue (Or ...))
            // was asserted but neither disjunct is individually derivable.
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match egraph.parse_and_run_program(None, &command) {
                Ok(_) => return Ok(true),
                Err(_) => {}
            }
            // Fallback: check if either disjunct holds individually.
            Ok(check_formula_holds(buffer, *l, subs, egraph)?
                || check_formula_holds(buffer, *r, subs, egraph)?)
        }
        LogicNode::NotNode(inner) => Ok(!check_formula_holds(buffer, *inner, subs, egraph)?),
        // Tense wrappers are transparent for reasoning
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => check_formula_holds(buffer, *inner, subs, egraph),
        LogicNode::ExistsNode((v, body)) => {
            // Check if any known entity satisfies the body
            let entities = get_known_entities();
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), entity.clone());
                if check_formula_holds(buffer, *body, &new_subs, egraph)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        LogicNode::ForAllNode((v, body)) => {
            // Check if ALL known entities satisfy the body
            let entities = get_known_entities();
            if entities.is_empty() {
                // Vacuously true over empty domain
                return Ok(true);
            }
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), entity.clone());
                if !check_formula_holds(buffer, *body, &new_subs, egraph)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LogicNode::Predicate(_) => {
            // Atomic: delegate to egglog
            let sexp = reconstruct_sexp_with_subs(buffer, node_id, subs);
            let command = format!("(check (IsTrue {}))", sexp);
            match egraph.parse_and_run_program(None, &command) {
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

// ─── Skolemization Helpers ────────────────────────────────────────

fn collect_exists_for_skolem(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
    enclosing_universals: &mut Vec<String>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            if !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    // Independent ∃ (not under any ∀): ground Skolem constant
                    subs.insert(v.clone(), fresh_skolem());
                } else {
                    // Dependent ∃ (under ∀): placeholder for per-entity Skolemization.
                    // The witness depends on the enclosing universal variables,
                    // so each entity gets its own Skolem constant at instantiation time.
                    let base = fresh_skolem();
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals);
        }
        LogicNode::ForAllNode((v, body)) => {
            enclosing_universals.push(v.clone());
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals);
            enclosing_universals.pop();
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_exists_for_skolem(buffer, *l, subs, enclosing_universals);
            collect_exists_for_skolem(buffer, *r, subs, enclosing_universals);
        }
        LogicNode::NotNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals);
        }
        LogicNode::Predicate(_) => {}
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs, enclosing_universals);
        }
    }
}

/// Extract ForAll nodes: returns (var_name, body_sexp, dependent_skolems) tuples.
/// The body_sexp has the ForAll wrapper stripped and existentials Skolemized.
/// Independent Skolems (∃ not under ∀) become (Const "sk_N").
/// Dependent Skolems (∃ under ∀) become (Var "__skdep__sk_N") placeholders.
fn collect_forall_nodes(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
) -> Vec<(String, String, Vec<(String, String)>)> {
    let mut entries = Vec::new();
    collect_forall_nodes_rec(buffer, node_id, skolem_subs, &mut entries);
    entries
}

fn collect_forall_nodes_rec(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    entries: &mut Vec<(String, String, Vec<(String, String)>)>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ForAllNode((v, body)) => {
            let body_sexp = reconstruct_sexp_with_subs(buffer, *body, skolem_subs);
            // Collect dependent Skolems that appear in this body.
            let dependent_skolems: Vec<(String, String)> = skolem_subs
                .values()
                .filter_map(|val| {
                    val.strip_prefix(SKDEP_PREFIX).and_then(|base| {
                        if body_sexp.contains(&format!("(Var \"{}\")", val)) {
                            Some((val.clone(), base.to_string()))
                        } else {
                            None
                        }
                    })
                })
                .collect();
            entries.push((v.clone(), body_sexp, dependent_skolems));
            // Don't recurse into body — the template is the complete body
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_forall_nodes_rec(buffer, *l, skolem_subs, entries);
            collect_forall_nodes_rec(buffer, *r, skolem_subs, entries);
        }
        LogicNode::NotNode(inner) | LogicNode::ExistsNode((_, inner)) => {
            collect_forall_nodes_rec(buffer, *inner, skolem_subs, entries);
        }
        // Tense wrappers: recurse through to find any ForAll nodes inside
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_forall_nodes_rec(buffer, *inner, skolem_subs, entries);
        }
        _ => {}
    }
}

/// Register all Const terms found in the formula as known entities.
fn collect_and_register_constants(buffer: &LogicBuffer, node_id: u32, egraph: &mut EGraph) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) => {
            for arg in args {
                if let LogicalTerm::Constant(c) = arg {
                    register_entity(c, egraph);
                }
            }
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_and_register_constants(buffer, *l, egraph);
            collect_and_register_constants(buffer, *r, egraph);
        }
        LogicNode::NotNode(inner)
        | LogicNode::ExistsNode((_, inner))
        | LogicNode::ForAllNode((_, inner)) => {
            collect_and_register_constants(buffer, *inner, egraph);
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_and_register_constants(buffer, *inner, egraph);
        }
    }
}

// ─── S-Expression Reconstruction ─────────────────────────────────

/// Reconstruct an egglog-compatible s-expression from a LogicBuffer node.
///
/// Tense wrappers (Past/Present/Future) are transparent: they recurse
/// directly into the inner formula. The egglog schema has no temporal
/// types, so tense is stripped for assertion/query. Tense information
/// is preserved in the LogicBuffer itself and visible via :debug output
/// (handled by the orchestrator's separate reconstruct_sexp).
fn reconstruct_sexp_with_subs(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(replacement) = subs.get(v.as_str()) {
                            if replacement.starts_with(SKDEP_PREFIX) {
                                // Dependent Skolem: stays as a Var placeholder.
                                // Will be replaced with a per-entity Const during
                                // Herbrand instantiation.
                                format!("(Var \"{}\")", replacement)
                            } else {
                                format!("(Const \"{}\")", replacement)
                            }
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
                // Universal variable substituted — strip ForAll wrapper
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
        // Tense wrappers are transparent for egglog.
        // Strip the wrapper and recurse into the inner formula.
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => reconstruct_sexp_with_subs(buffer, *inner, subs),
    }
}

bindings::export!(ReasoningComponent with_types_in bindings);
