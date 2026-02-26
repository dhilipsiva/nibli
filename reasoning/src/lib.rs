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
static KNOWN_RULES: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

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
    ;; Phase 7: Native egglog rules for universals
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

    ;; Domain of known entities (for bare universal triggers)
    (relation InDomain (Term))

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

/// Record an entity name for query-side enumeration and InDomain tracking.
/// Unlike register_entity, this does NOT trigger template instantiation.
/// Used by the native-rule path where egglog handles universals directly.
fn note_entity(name: &str, egraph: &mut EGraph) {
    let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
    let is_new = entities.lock().unwrap().insert(name.to_string());
    if is_new {
        let cmd = format!("(InDomain (Const \"{}\"))", name);
        egraph.parse_and_run_program(None, &cmd).ok();
    }
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
    /// Assert facts with Skolemization (∃) and native egglog rules (∀).
    /// Phase A: Simple universals (no dependent Skolems) compile to native rules.
    /// Universals with dependent Skolems (∃ under ∀) fall back to Herbrand expansion.
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

            // Phase 2: Dispatch based on formula structure
            let is_forall = matches!(
                &logic.nodes[root_id as usize],
                LogicNode::ForAllNode(_)
            );

            if is_forall && !has_dependent_skolems(&logic, root_id, false) {
                // ═══ NATIVE RULE PATH ═══
                // Simple universal (no ∃ under ∀): compile to egglog rule.
                // egglog's hash-join engine handles matching natively — O(K) not O(E×T).

                // Note independent Skolem constants as entities
                for sk in skolem_subs.values() {
                    if !sk.starts_with(SKDEP_PREFIX) {
                        note_entity(sk, &mut egraph);
                    }
                }

                // Note named constants as entities
                collect_and_note_constants(&logic, root_id, &mut egraph);

                // Compile ForAll to native egglog rule
                compile_forall_to_rule(&logic, root_id, &skolem_subs, &mut egraph)?;
            } else if is_forall {
                // ═══ HERBRAND FALLBACK PATH ═══
                // Universal with dependent Skolems (∃ under ∀): use old approach.
                // Will be replaced by SkolemFn in Phase B.

                // Register independent Skolem constants as entities
                for sk in skolem_subs.values() {
                    if !sk.starts_with(SKDEP_PREFIX) {
                        register_entity(sk, &mut egraph);
                    }
                }

                // Register named constants as entities
                collect_and_register_constants(&logic, root_id, &mut egraph);

                let forall_entries = collect_forall_nodes(&logic, root_id, &skolem_subs);
                for (var_name, body_sexp, dependent_skolems) in &forall_entries {
                    println!(
                        "[Universal] ∀{} registered for Herbrand instantiation (dependent Skolems)",
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
                // ═══ GROUND FORMULA PATH ═══
                // No universals — just assert the ground formula.

                // Register independent Skolem constants
                for sk in skolem_subs.values() {
                    if !sk.starts_with(SKDEP_PREFIX) {
                        note_entity(sk, &mut egraph);
                    }
                }

                // Note named constants as entities
                collect_and_note_constants(&logic, root_id, &mut egraph);

                let sexp = reconstruct_sexp_with_subs(&logic, root_id, &skolem_subs);
                let command = format!("(IsTrue {})", sexp);
                egraph
                    .parse_and_run_program(None, &command)
                    .map_err(|e| format!("Failed to assert fact: {}", e))?;
            }

            // Phase 3: Generate extra witnesses for Count quantifiers (n > 1)
            generate_count_extra_witnesses(&logic, root_id, &skolem_subs, &mut egraph);

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

        // 5. Clear known rules
        let rules = KNOWN_RULES.get_or_init(|| Mutex::new(HashSet::new()));
        rules.lock().unwrap().clear();

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
        LogicNode::CountNode((v, count, body)) => {
            // Check that exactly `count` known entities satisfy the body
            let entities = get_known_entities();
            let mut satisfying = 0u32;
            for entity in &entities {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), entity.clone());
                if check_formula_holds(buffer, *body, &new_subs, egraph)? {
                    satisfying += 1;
                }
            }
            Ok(satisfying == *count)
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
        LogicNode::CountNode((v, count, body)) => {
            // Count(x, n > 0, body): the variable needs a Skolem witness (like Exists)
            if *count > 0 && !subs.contains_key(v.as_str()) {
                if enclosing_universals.is_empty() {
                    subs.insert(v.clone(), fresh_skolem());
                } else {
                    let base = fresh_skolem();
                    let placeholder = format!("{}{}", SKDEP_PREFIX, base);
                    subs.insert(v.clone(), placeholder);
                }
            }
            // Count(x, 0, body): no witness needed (it means ∀x.¬body)
            collect_exists_for_skolem(buffer, *body, subs, enclosing_universals);
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
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                // Count(x, 0, body) ≡ ∀x.¬body — treat as universal template
                let body_sexp = reconstruct_sexp_with_subs(buffer, *body, skolem_subs);
                let negated = format!("(Not {})", body_sexp);
                // Collect dependent Skolems in the negated body
                let dependent_skolems: Vec<(String, String)> = skolem_subs
                    .values()
                    .filter_map(|val| {
                        val.strip_prefix(SKDEP_PREFIX).and_then(|base| {
                            if negated.contains(&format!("(Var \"{}\")", val)) {
                                Some((val.clone(), base.to_string()))
                            } else {
                                None
                            }
                        })
                    })
                    .collect();
                entries.push((v.clone(), negated, dependent_skolems));
            } else {
                // Count(x, n>0, body): recurse into body for nested ForAlls
                collect_forall_nodes_rec(buffer, *body, skolem_subs, entries);
            }
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
        LogicNode::CountNode((_, _, body)) => {
            collect_and_register_constants(buffer, *body, egraph);
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_and_register_constants(buffer, *inner, egraph);
        }
    }
}

// ─── Native Rule Compilation ─────────────────────────────────────

/// Check if a ForAll node has any dependent existentials (∃ nested under ∀).
/// If true, the old Herbrand approach is used as fallback (Phase A).
fn has_dependent_skolems(buffer: &LogicBuffer, node_id: u32, under_forall: bool) -> bool {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ForAllNode((_, body)) => has_dependent_skolems(buffer, *body, true),
        LogicNode::ExistsNode((_, body)) => {
            if under_forall {
                return true;
            }
            has_dependent_skolems(buffer, *body, false)
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            has_dependent_skolems(buffer, *l, under_forall)
                || has_dependent_skolems(buffer, *r, under_forall)
        }
        LogicNode::NotNode(inner) => has_dependent_skolems(buffer, *inner, under_forall),
        LogicNode::CountNode((_, _, body)) => has_dependent_skolems(buffer, *body, under_forall),
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => has_dependent_skolems(buffer, *inner, under_forall),
        LogicNode::Predicate(_) => false,
    }
}

/// Decompose a material conditional body into (conditions, action).
/// The semantics layer produces universals as ForAll(v, Or(Not(restrictor), body)).
/// This walks the Or(Not(...), ...) chain collecting antecedents.
/// Returns None if the body is not in implication form.
fn decompose_implication(buffer: &LogicBuffer, body_id: u32) -> Option<(Vec<u32>, u32)> {
    let mut conditions = Vec::new();
    let mut current = body_id;

    loop {
        match &buffer.nodes[current as usize] {
            LogicNode::OrNode((left, right)) => {
                match &buffer.nodes[*left as usize] {
                    LogicNode::NotNode(inner) => {
                        // Or(Not(condition), rest) → add condition, continue with rest
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

/// Note all Const terms found in the formula as known entities (no template instantiation).
fn collect_and_note_constants(buffer: &LogicBuffer, node_id: u32, egraph: &mut EGraph) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) => {
            for arg in args {
                if let LogicalTerm::Constant(c) = arg {
                    note_entity(c, egraph);
                }
            }
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_and_note_constants(buffer, *l, egraph);
            collect_and_note_constants(buffer, *r, egraph);
        }
        LogicNode::NotNode(inner)
        | LogicNode::ExistsNode((_, inner))
        | LogicNode::ForAllNode((_, inner)) => {
            collect_and_note_constants(buffer, *inner, egraph);
        }
        LogicNode::CountNode((_, _, body)) => {
            collect_and_note_constants(buffer, *body, egraph);
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_and_note_constants(buffer, *inner, egraph);
        }
    }
}

/// Reconstruct an egglog s-expression with bare pattern variables for rule compilation.
/// Variables in `pattern_vars` are emitted as bare identifiers (egglog pattern variables).
/// Variables in `ground_skolems` are emitted as (Const "sk_N").
/// Other variables are emitted as (Var "name").
fn reconstruct_rule_sexp(
    buffer: &LogicBuffer,
    node_id: u32,
    pattern_vars: &HashMap<String, String>,
    ground_skolems: &HashMap<String, String>,
) -> String {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((rel, args)) => {
            let mut args_str = String::from("(Nil)");
            for arg in args.iter().rev() {
                let term_str = match arg {
                    LogicalTerm::Variable(v) => {
                        if let Some(pvar) = pattern_vars.get(v.as_str()) {
                            // Bare egglog pattern variable (no quotes, no Var constructor)
                            pvar.clone()
                        } else if let Some(sk) = ground_skolems.get(v.as_str()) {
                            format!("(Const \"{}\")", sk)
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
            // In rule context, Skolemized exists are stripped
            if ground_skolems.contains_key(v.as_str()) || pattern_vars.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems)
            } else {
                format!(
                    "(Exists \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems)
                )
            }
        }
        LogicNode::ForAllNode((v, body)) => {
            // In rule context, ForAll wrappers are stripped (pattern vars handle them)
            if pattern_vars.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems)
            } else {
                format!(
                    "(ForAll \"{}\" {})",
                    v,
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems)
                )
            }
        }
        LogicNode::AndNode((l, r)) => {
            format!(
                "(And {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems)
            )
        }
        LogicNode::OrNode((l, r)) => {
            format!(
                "(Or {} {})",
                reconstruct_rule_sexp(buffer, *l, pattern_vars, ground_skolems),
                reconstruct_rule_sexp(buffer, *r, pattern_vars, ground_skolems)
            )
        }
        LogicNode::NotNode(inner) => {
            format!(
                "(Not {})",
                reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems)
            )
        }
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else if ground_skolems.contains_key(v.as_str()) {
                reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems)
            } else {
                let body_sexp =
                    reconstruct_rule_sexp(buffer, *body, pattern_vars, ground_skolems);
                format!("(Exists \"{}\" {})", v, body_sexp)
            }
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            reconstruct_rule_sexp(buffer, *inner, pattern_vars, ground_skolems)
        }
    }
}

/// Compile a ForAll node into a native egglog rule.
/// The ForAll variable becomes a pattern variable in the rule.
/// The formula body (expected to be in material conditional form Or(Not(A), B))
/// is decomposed into rule conditions and actions.
fn compile_forall_to_rule(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    egraph: &mut EGraph,
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
            LogicNode::PastNode(inner)
            | LogicNode::PresentNode(inner)
            | LogicNode::FutureNode(inner) => {
                current = *inner;
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

    // Extract only ground Skolem subs (no dependent ones in Phase A)
    let ground_skolems: HashMap<String, String> = skolem_subs
        .iter()
        .filter(|(_, v)| !v.starts_with(SKDEP_PREFIX))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

    // 3. Decompose inner body
    match decompose_implication(buffer, inner_body_id) {
        Some((condition_ids, consequent_id)) => {
            // Implication form: conditions become rule patterns, consequent becomes action

            // 4. Flatten conditions into individual atoms
            let mut all_conditions = Vec::new();
            for cid in &condition_ids {
                all_conditions.extend(flatten_conjuncts(buffer, *cid));
            }

            // 5. Build condition s-expressions
            let conditions_sexp: Vec<String> = all_conditions
                .iter()
                .map(|&cid| {
                    let sexp =
                        reconstruct_rule_sexp(buffer, cid, &pattern_vars, &ground_skolems);
                    format!("(IsTrue {})", sexp)
                })
                .collect();

            // 6. Build action s-expressions
            let consequent_atoms = flatten_consequent(buffer, consequent_id, skolem_subs);
            let actions_sexp: Vec<String> = consequent_atoms
                .iter()
                .map(|&aid| {
                    let sexp =
                        reconstruct_rule_sexp(buffer, aid, &pattern_vars, &ground_skolems);
                    format!("(IsTrue {})", sexp)
                })
                .collect();

            // 7. Emit egglog rule
            let rule = format!(
                "(rule ({}) ({}))",
                conditions_sexp.join(" "),
                actions_sexp.join(" ")
            );

            // Deduplicate: egglog 2.0 panics on duplicate rules
            let known_rules = KNOWN_RULES.get_or_init(|| Mutex::new(HashSet::new()));
            if !known_rules.lock().unwrap().insert(rule.clone()) {
                println!(
                    "[Rule] ∀{} already present, skipping",
                    universals.join(",")
                );
            } else {
                println!(
                    "[Rule] Compiled ∀{} to native egglog rule",
                    universals.join(",")
                );
                egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile universal to rule: {}", e))?;
            }
        }
        None => {
            // Bare universal (no implication): use InDomain trigger
            let body_sexp =
                reconstruct_rule_sexp(buffer, inner_body_id, &pattern_vars, &ground_skolems);

            let domain_conditions: Vec<String> = universals
                .iter()
                .map(|v| format!("(InDomain {})", pattern_vars[v]))
                .collect();

            let rule = format!(
                "(rule ({}) ((IsTrue {})))",
                domain_conditions.join(" "),
                body_sexp
            );

            let known_rules = KNOWN_RULES.get_or_init(|| Mutex::new(HashSet::new()));
            if !known_rules.lock().unwrap().insert(rule.clone()) {
                println!(
                    "[Rule] bare ∀{} already present, skipping",
                    universals.join(",")
                );
            } else {
                println!(
                    "[Rule] Compiled bare ∀{} with InDomain trigger",
                    universals.join(",")
                );
                egraph
                    .parse_and_run_program(None, &rule)
                    .map_err(|e| format!("Failed to compile bare universal to rule: {}", e))?;
            }
        }
    }

    Ok(())
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
        LogicNode::CountNode((v, count, body)) => {
            if *count == 0 {
                // Count(x, 0, body) ≡ ∀x.¬body
                let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                format!("(ForAll \"{}\" (Not {}))", v, body_sexp)
            } else {
                // Count(x, n>0, body): primary Skolem already in subs. Emit as Exists.
                if subs.contains_key(v.as_str()) {
                    reconstruct_sexp_with_subs(buffer, *body, subs)
                } else {
                    let body_sexp = reconstruct_sexp_with_subs(buffer, *body, subs);
                    format!("(Exists \"{}\" {})", v, body_sexp)
                }
            }
        }
        // Tense wrappers are transparent for egglog.
        // Strip the wrapper and recurse into the inner formula.
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => reconstruct_sexp_with_subs(buffer, *inner, subs),
    }
}

/// Generate extra Skolem witnesses for Count(x, n, body) where n > 1.
/// The primary Skolem witness was already created in phase 1 (Skolemization).
/// This function creates n-1 additional witnesses and asserts the body for each.
fn generate_count_extra_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    egraph: &mut EGraph,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::CountNode((v, count, body)) => {
            if *count > 1 {
                // The primary witness is already in skolem_subs.
                // Generate (count - 1) additional witnesses.
                for _ in 1..*count {
                    let extra_sk = fresh_skolem();
                    note_entity(&extra_sk, egraph);

                    // Build substitutions with the extra witness replacing v
                    let mut extra_subs = skolem_subs.clone();
                    extra_subs.insert(v.clone(), extra_sk.clone());

                    let sexp = reconstruct_sexp_with_subs(buffer, *body, &extra_subs);
                    let command = format!("(IsTrue {})", sexp);
                    if let Err(e) = egraph.parse_and_run_program(None, &command) {
                        eprintln!(
                            "[reasoning] Failed to assert extra Count witness {}: {}",
                            extra_sk, e
                        );
                    }
                }
            }
            // Recurse into body for nested Count nodes
            generate_count_extra_witnesses(buffer, *body, skolem_subs, egraph);
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            generate_count_extra_witnesses(buffer, *l, skolem_subs, egraph);
            generate_count_extra_witnesses(buffer, *r, skolem_subs, egraph);
        }
        LogicNode::NotNode(inner)
        | LogicNode::ExistsNode((_, inner))
        | LogicNode::ForAllNode((_, inner)) => {
            generate_count_extra_witnesses(buffer, *inner, skolem_subs, egraph);
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            generate_count_extra_witnesses(buffer, *inner, skolem_subs, egraph);
        }
        LogicNode::Predicate(_) => {}
    }
}

bindings::export!(ReasoningComponent with_types_in bindings);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};

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

    fn reset() {
        ReasoningComponent::reset_state().unwrap();
    }

    fn assert_buf(buf: LogicBuffer) {
        ReasoningComponent::assert_fact(buf).unwrap();
    }

    fn query(buf: LogicBuffer) -> bool {
        ReasoningComponent::query_entailment(buf).unwrap()
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

    /// Build query "? la .X. P" -> Pred("P", [Const("X"), Zoe])
    fn make_query(entity: &str, predicate: &str) -> LogicBuffer {
        make_assertion(entity, predicate)
    }

    #[test]
    fn test_native_rule_simple_universal() {
        reset();
        // la .alis. gerku
        assert_buf(make_assertion("alis", "gerku"));
        // ro lo gerku cu danlu
        assert_buf(make_universal("gerku", "danlu"));
        // ? la .alis. danlu -> TRUE
        assert!(query(make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_entity_after_rule() {
        reset();
        // ro lo gerku cu danlu (rule first)
        assert_buf(make_universal("gerku", "danlu"));
        // la .alis. gerku (entity second — egglog rule fires on new facts)
        assert_buf(make_assertion("alis", "gerku"));
        // ? la .alis. danlu -> TRUE
        assert!(query(make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_selective_application() {
        reset();
        // la .alis. gerku
        assert_buf(make_assertion("alis", "gerku"));
        // la .bob. mlatu
        assert_buf(make_assertion("bob", "mlatu"));
        // ro lo gerku cu danlu
        assert_buf(make_universal("gerku", "danlu"));
        // ? la .alis. danlu -> TRUE (alis is gerku)
        assert!(query(make_query("alis", "danlu")));
        // ? la .bob. danlu -> FALSE (bob is mlatu, not gerku)
        assert!(!query(make_query("bob", "danlu")));
    }

    #[test]
    fn test_native_rule_transitive_chain() {
        reset();
        // ro lo gerku cu danlu
        assert_buf(make_universal("gerku", "danlu"));
        // ro lo danlu cu xanlu
        assert_buf(make_universal("danlu", "xanlu"));
        // la .alis. gerku
        assert_buf(make_assertion("alis", "gerku"));
        // ? la .alis. xanlu -> TRUE (gerku->danlu->xanlu)
        assert!(query(make_query("alis", "xanlu")));
    }

    #[test]
    fn test_native_rule_multiple_entities() {
        reset();
        // la .alis. gerku
        assert_buf(make_assertion("alis", "gerku"));
        // la .bob. gerku
        assert_buf(make_assertion("bob", "gerku"));
        // ro lo gerku cu danlu
        assert_buf(make_universal("gerku", "danlu"));
        // Both should derive danlu
        assert!(query(make_query("alis", "danlu")));
        assert!(query(make_query("bob", "danlu")));
    }

    #[test]
    fn test_native_rule_negated_universal() {
        reset();
        // la .alis. gerku
        assert_buf(make_assertion("alis", "gerku"));

        // ro lo gerku cu na danlu
        // ForAll("_v0", Or(Not(Pred("gerku", [Var, Zoe])), Not(Pred("danlu", [Var, Zoe]))))
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
        assert_buf(LogicBuffer { nodes, roots: vec![root] });

        // ? la .alis. danlu -> FALSE
        assert!(!query(make_query("alis", "danlu")));
    }

    #[test]
    fn test_native_rule_duplicate_rule_no_panic() {
        reset();
        // Assert the same universal twice — should not panic
        assert_buf(make_universal("gerku", "danlu"));
        assert_buf(make_universal("gerku", "danlu"));
        // Should still work correctly
        assert_buf(make_assertion("alis", "gerku"));
        assert!(query(make_query("alis", "danlu")));
    }
}
