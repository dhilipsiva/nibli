#[allow(warnings)]
mod bindings;

use crate::bindings::exports::lojban::nesy::reasoning::Guest;
use crate::bindings::lojban::nesy::ast_types::{LogicBuffer, LogicNode, LogicalTerm};
use egglog::EGraph;
use std::collections::{HashMap, HashSet};
use std::sync::{Mutex, OnceLock};

// ─── Global Persistent State ──────────────────────────────────

static EGRAPH: OnceLock<Mutex<EGraph>> = OnceLock::new();
static SKOLEM_COUNTER: OnceLock<Mutex<usize>> = OnceLock::new();
static KNOWN_ENTITIES: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
static UNIVERSAL_TEMPLATES: OnceLock<Mutex<Vec<UniversalTemplate>>> = OnceLock::new();

/// A stored universal formula for Herbrand instantiation.
/// When new entities appear, we instantiate the template for each.
struct UniversalTemplate {
    var_name: String,
    /// The body s-expression with (Var "var_name") as placeholder
    body_sexp: String,
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
            let instantiated = tmpl.body_sexp.replace(
                &format!("(Var \"{}\")", tmpl.var_name),
                &format!("(Const \"{}\")", name),
            );
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
    EGRAPH.get_or_init(|| {
        let mut egraph = EGraph::default();

        let schema_str = r#"
            ;; ═══════════════════════════════════════════════
            ;; Lojban NeSy Engine — FOL Schema & Rules
            ;; Phase 6b: Skolemization + Herbrand instantiation
            ;; ═══════════════════════════════════════════════

            ;; Atomic Terms
            (datatype Term
                (Var String)
                (Const String)
                (Desc String)
                (Zoe)
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

            ;; ───────────────────────────────────────────────
            ;; STRUCTURAL REWRITES
            ;; ───────────────────────────────────────────────

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

            ;; ───────────────────────────────────────────────
            ;; INFERENCE RULES
            ;; ───────────────────────────────────────────────

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

            ;; ───────────────────────────────────────────────
            ;; QUANTIFIER RULES (residual)
            ;; ───────────────────────────────────────────────

            ;; ∃-distribution over ∧
            (rule ((IsTrue (Exists v (And A B))))
                  ((IsTrue (And (Exists v A) (Exists v B)))))

            ;; ∀-distribution over ∧
            (rule ((IsTrue (ForAll v (And A B))))
                  ((IsTrue (And (ForAll v A) (ForAll v B)))))
        "#;

        egraph
            .parse_and_run_program(None, schema_str)
            .expect("Failed to load FOL schema and rules");

        Mutex::new(egraph)
    })
}

// ─── WIT Export Implementation ────────────────────────────────

struct ReasoningComponent;

impl Guest for ReasoningComponent {
    /// Assert facts with Skolemization (∃) and Herbrand instantiation (∀).
    fn assert_fact(logic: LogicBuffer) -> Result<(), String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        for &root_id in &logic.roots {
            // Phase 1: Collect existential variables for Skolemization
            let mut skolem_subs = HashMap::new();
            collect_exists_for_skolem(&logic, root_id, &mut skolem_subs);

            // Register Skolem constants as entities
            for sk in skolem_subs.values() {
                register_entity(sk, &mut egraph);
            }

            // Register named constants as entities
            collect_and_register_constants(&logic, root_id, &mut egraph);

            // Phase 2: Check for ForAll nodes and handle Herbrand instantiation
            let forall_entries = collect_forall_nodes(&logic, root_id, &skolem_subs);

            if !forall_entries.is_empty() {
                for (var_name, body_sexp) in &forall_entries {
                    println!(
                        "[Universal] ∀{} registered for Herbrand instantiation",
                        var_name
                    );

                    // Store template for future entity registration
                    let templates = UNIVERSAL_TEMPLATES.get_or_init(|| Mutex::new(Vec::new()));
                    templates.lock().unwrap().push(UniversalTemplate {
                        var_name: var_name.clone(),
                        body_sexp: body_sexp.clone(),
                    });

                    // Instantiate for all currently known entities
                    let entities = get_known_entities();
                    for entity in &entities {
                        let instantiated = body_sexp.replace(
                            &format!("(Var \"{}\")", var_name),
                            &format!("(Const \"{}\")", entity),
                        );
                        let command = format!("(IsTrue {})", instantiated);
                        if let Err(e) = egraph.parse_and_run_program(None, &command) {
                            return Err(format!(
                                "Failed to instantiate universal for {}: {}",
                                entity, e
                            ));
                        }
                    }
                    if !entities.is_empty() {
                        println!(
                            "[Universal] Instantiated for {} known entities",
                            entities.len()
                        );
                    }
                }
            }

            // Phase 3: Assert the (possibly Skolemized) formula itself
            if !skolem_subs.is_empty() {
                println!(
                    "[Skolem] {} variable(s) → {}",
                    skolem_subs.len(),
                    skolem_subs
                        .iter()
                        .map(|(v, sk)| format!("{} ↦ {}", v, sk))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }

            let sexp = reconstruct_sexp_with_subs(&logic, root_id, &skolem_subs);
            let command = format!("(IsTrue {})", sexp);
            if let Err(e) = egraph.parse_and_run_program(None, &command) {
                return Err(format!("Failed to assert fact: {}", e));
            }
        }
        Ok(())
    }

    /// Query entailment via recursive Rust-side formula decomposition.
    ///
    /// All connective logic (And/Or/Not) and quantifier resolution
    /// (Exists/ForAll) is handled in Rust. Only atomic predicates
    /// are delegated to egglog via `(check (IsTrue ...))`.
    fn query_entailment(logic: LogicBuffer) -> Result<bool, String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        // Saturate
        if let Err(e) = egraph.parse_and_run_program(None, "(run-schedule (saturate (run)))") {
            eprintln!(
                "[reasoning] saturate failed, falling back to bounded run: {}",
                e
            );
            if let Err(e2) = egraph.parse_and_run_program(None, "(run 100)") {
                return Err(format!("Saturation error: {}", e2));
            }
        }

        for &root_id in &logic.roots {
            if !check_formula_holds(&logic, root_id, &HashMap::new(), &mut egraph)? {
                return Ok(false);
            }
        }

        Ok(true)
    }
}

// ─── Recursive Formula Checking (Rust-side decomposition) ─────

/// Recursively check whether a formula holds, decomposing connectives
/// in Rust rather than relying on egglog conjunction introduction.
///
/// - Pred: check directly via egglog `(check (IsTrue ...))`
/// - And(A,B): both must hold
/// - Or(A,B): at least one must hold
/// - Not(A): A must NOT hold
/// - Exists: enumerate entities (delegated to caller)
/// - ForAll: strip wrapper (variable already substituted by caller)
fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, String>,
    egraph: &mut EGraph,
) -> Result<bool, String> {
    match &buffer.nodes[node_id as usize] {
        LogicNode::AndNode((l, r)) => {
            // Both conjuncts must hold
            Ok(check_formula_holds(buffer, *l, subs, egraph)?
                && check_formula_holds(buffer, *r, subs, egraph)?)
        }
        LogicNode::OrNode((l, r)) => {
            // At least one disjunct must hold
            Ok(check_formula_holds(buffer, *l, subs, egraph)?
                || check_formula_holds(buffer, *r, subs, egraph)?)
        }
        LogicNode::NotNode(inner) => {
            // Inner must NOT hold
            Ok(!check_formula_holds(buffer, *inner, subs, egraph)?)
        }
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => Ok(!check_formula_holds(buffer, *inner, subs, egraph)?),
        LogicNode::ExistsNode((v, body)) => {
            // If variable is already substituted, just check body
            if subs.contains_key(v.as_str()) {
                return check_formula_holds(buffer, *body, subs, egraph);
            }
            // Otherwise enumerate entities
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
            // If variable is already substituted, just check body
            if subs.contains_key(v.as_str()) {
                return check_formula_holds(buffer, *body, subs, egraph);
            }
            // Otherwise all entities must satisfy
            let entities = get_known_entities();
            if entities.is_empty() {
                return Ok(true); // Vacuously true
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

// ─── Skolemization Helpers ────────────────────────────────────

fn collect_exists_for_skolem(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, String>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            if !subs.contains_key(v.as_str()) {
                subs.insert(v.clone(), fresh_skolem());
            }
            collect_exists_for_skolem(buffer, *body, subs);
        }
        LogicNode::ForAllNode((_, body)) => {
            collect_exists_for_skolem(buffer, *body, subs);
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_exists_for_skolem(buffer, *l, subs);
            collect_exists_for_skolem(buffer, *r, subs);
        }
        LogicNode::NotNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs);
        }
        LogicNode::Predicate(_) => {}
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            collect_exists_for_skolem(buffer, *inner, subs);
        }
    }
}

/// Extract ForAll nodes: returns (var_name, body_sexp) pairs.
/// The body_sexp has the ForAll wrapper stripped and existentials Skolemized.
fn collect_forall_nodes(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
) -> Vec<(String, String)> {
    let mut entries = Vec::new();
    collect_forall_nodes_rec(buffer, node_id, skolem_subs, &mut entries);
    entries
}

fn collect_forall_nodes_rec(
    buffer: &LogicBuffer,
    node_id: u32,
    skolem_subs: &HashMap<String, String>,
    entries: &mut Vec<(String, String)>,
) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ForAllNode((v, body)) => {
            let body_sexp = reconstruct_sexp_with_subs(buffer, *body, skolem_subs);
            entries.push((v.clone(), body_sexp));
            // Don't recurse into body — the template is the complete body
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_forall_nodes_rec(buffer, *l, skolem_subs, entries);
            collect_forall_nodes_rec(buffer, *r, skolem_subs, entries);
        }
        LogicNode::NotNode(inner) | LogicNode::ExistsNode((_, inner)) => {
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

// ─── S-Expression Reconstruction ──────────────────────────────

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
                            format!("(Const \"{}\")", replacement)
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                    LogicalTerm::Number(n) => format!("(Num {})", n),
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
        LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner) => {
            format!("(Not {})", reconstruct_sexp_with_subs(buffer, *inner, subs))
        }
    }
}

fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    reconstruct_sexp_with_subs(buffer, node_id, &HashMap::new())
}

bindings::export!(ReasoningComponent with_types_in bindings);
