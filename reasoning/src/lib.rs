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

/// Maximum combinations when resolving existential queries.
/// For N entities and K existential variables, we try N^K substitutions.
const MAX_QUERY_COMBOS: usize = 10_000;

fn fresh_skolem() -> String {
    let counter = SKOLEM_COUNTER.get_or_init(|| Mutex::new(0));
    let mut c = counter.lock().unwrap();
    let sk = format!("sk_{}", *c);
    *c += 1;
    sk
}

fn register_entity(name: &str) {
    let entities = KNOWN_ENTITIES.get_or_init(|| Mutex::new(HashSet::new()));
    entities.lock().unwrap().insert(name.to_string());
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
            ;; Phase 6: Skolemization-aware
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

            ;; Conjunction Elimination: A ∧ B ⊢ A, B
            (rule ((IsTrue (And A B)))
                  ((IsTrue A) (IsTrue B)))

            ;; Disjunctive Syllogism: A ∨ B, ¬A ⊢ B
            (rule ((IsTrue (Or A B)) (IsTrue (Not A)))
                  ((IsTrue B)))

            ;; Modus Ponens: A → B, A ⊢ B
            (rule ((IsTrue (Implies A B)) (IsTrue A))
                  ((IsTrue B)))

            ;; Modus Tollens: A → B, ¬B ⊢ ¬A
            (rule ((IsTrue (Implies A B)) (IsTrue (Not B)))
                  ((IsTrue (Not A))))

            ;; ───────────────────────────────────────────────
            ;; QUANTIFIER RULES (legacy, for non-Skolemized data)
            ;; After Phase 6, assertions are Skolemized so these
            ;; only fire on residual or manually asserted formulas.
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
    /// Assert facts with Skolemization.
    ///
    /// All existential quantifiers are replaced with fresh Skolem constants.
    /// `∃x. gerku(x) ∧ barda(x)` becomes `gerku(sk_0) ∧ barda(sk_0)`.
    /// This eliminates variable aliasing across independent assertions.
    fn assert_fact(logic: LogicBuffer) -> Result<(), String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        for &root_id in &logic.roots {
            // Collect all ∃-bound variables and assign globally unique Skolem constants
            let mut skolem_subs = HashMap::new();
            collect_exists_for_skolem(&logic, root_id, &mut skolem_subs);

            // Register Skolem constants as known entities
            for sk in skolem_subs.values() {
                register_entity(sk);
            }

            // Register any named constants (la .bob. → "bob")
            collect_and_register_constants(&logic, root_id);

            // Build Skolemized s-expression (∃ wrappers removed, vars → Const)
            let sexp = reconstruct_sexp_with_subs(&logic, root_id, &skolem_subs);

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

            let command = format!("(IsTrue {})", sexp);
            if let Err(e) = egraph.parse_and_run_program(None, &command) {
                return Err(format!("Failed to assert fact: {}", e));
            }
        }
        Ok(())
    }

    /// Query entailment with existential resolution.
    ///
    /// For queries without existentials (e.g., `la .bob. cu klama`):
    ///   Direct structural check.
    ///
    /// For queries with existentials (e.g., `lo gerku cu barda`):
    ///   Tries all known entity substitutions for each ∃-variable.
    ///   Returns TRUE if any assignment satisfies the query.
    fn query_entailment(logic: LogicBuffer) -> Result<bool, String> {
        let egraph_mutex = get_egraph();
        let mut egraph = egraph_mutex.lock().unwrap();

        // Saturate inference rules to fixpoint
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
            // Collect existential variables in this query root
            let exist_vars = collect_exists_vars(&logic, root_id);

            if exist_vars.is_empty() {
                // ── No existentials: direct structural check ──
                let sexp = reconstruct_sexp(&logic, root_id);
                let command = format!("(check (IsTrue {}))", sexp);
                match egraph.parse_and_run_program(None, &command) {
                    Ok(_) => {} // This root checks out
                    Err(e) => {
                        let msg = e.to_string();
                        if msg.contains("Check failed") {
                            return Ok(false);
                        }
                        return Err(format!("Reasoning error: {}", msg));
                    }
                }
            } else {
                // ── Has existentials: try Skolem constant substitutions ──
                let entities = get_known_entities();
                if entities.is_empty() {
                    return Ok(false); // No entities in KB → can't satisfy ∃
                }

                let found = try_existential_resolution(
                    &logic,
                    root_id,
                    &exist_vars,
                    &entities,
                    &mut egraph,
                )?;
                if !found {
                    return Ok(false);
                }
            }
        }

        Ok(true)
    }
}

// ─── Skolemization Helpers ────────────────────────────────────

/// Walk the logic tree and assign a fresh Skolem constant to each ∃-bound variable.
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
    }
}

/// Collect names of all ∃-bound variables in the formula (for query resolution).
fn collect_exists_vars(buffer: &LogicBuffer, node_id: u32) -> Vec<String> {
    let mut vars = Vec::new();
    collect_exists_vars_rec(buffer, node_id, &mut vars);
    vars
}

fn collect_exists_vars_rec(buffer: &LogicBuffer, node_id: u32, vars: &mut Vec<String>) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::ExistsNode((v, body)) => {
            if !vars.contains(v) {
                vars.push(v.clone());
            }
            collect_exists_vars_rec(buffer, *body, vars);
        }
        LogicNode::ForAllNode((_, body)) => {
            collect_exists_vars_rec(buffer, *body, vars);
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_exists_vars_rec(buffer, *l, vars);
            collect_exists_vars_rec(buffer, *r, vars);
        }
        LogicNode::NotNode(inner) => {
            collect_exists_vars_rec(buffer, *inner, vars);
        }
        LogicNode::Predicate(_) => {}
    }
}

/// Register all Const terms found in the formula as known entities.
fn collect_and_register_constants(buffer: &LogicBuffer, node_id: u32) {
    match &buffer.nodes[node_id as usize] {
        LogicNode::Predicate((_, args)) => {
            for arg in args {
                if let LogicalTerm::Constant(c) = arg {
                    register_entity(c);
                }
            }
        }
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_and_register_constants(buffer, *l);
            collect_and_register_constants(buffer, *r);
        }
        LogicNode::NotNode(inner)
        | LogicNode::ExistsNode((_, inner))
        | LogicNode::ForAllNode((_, inner)) => {
            collect_and_register_constants(buffer, *inner);
        }
    }
}

// ─── Existential Query Resolution ─────────────────────────────

/// Try all combinations of known entities for existential variables.
/// Returns true if any substitution satisfies the query.
fn try_existential_resolution(
    buffer: &LogicBuffer,
    root_id: u32,
    exist_vars: &[String],
    entities: &[String],
    egraph: &mut EGraph,
) -> Result<bool, String> {
    let n = entities.len();
    let k = exist_vars.len();

    // Check combinatorial bound
    let total = n.checked_pow(k as u32).unwrap_or(usize::MAX);
    if total > MAX_QUERY_COMBOS {
        return Err(format!(
            "Existential query too complex: {} variables × {} entities = {} combinations (limit {}). \
             Narrow the query or assert fewer entities.",
            k, n, total, MAX_QUERY_COMBOS
        ));
    }

    // Iterate through all entity combinations (odometer algorithm)
    let mut indices = vec![0usize; k];

    loop {
        // Build substitution: exist_var[i] → entities[indices[i]]
        let mut subs = HashMap::with_capacity(k);
        for (i, var) in exist_vars.iter().enumerate() {
            subs.insert(var.clone(), entities[indices[i]].clone());
        }

        // Build substituted s-expression and check
        let sexp = reconstruct_sexp_with_subs(buffer, root_id, &subs);
        let command = format!("(check (IsTrue {}))", sexp);

        match egraph.parse_and_run_program(None, &command) {
            Ok(_) => return Ok(true), // Found a satisfying assignment
            Err(e) => {
                let msg = e.to_string();
                if !msg.contains("Check failed") {
                    return Err(format!("Reasoning error: {}", msg));
                }
                // This combination failed — try next
            }
        }

        // Increment odometer (rightmost index first)
        let mut carry = true;
        for i in (0..k).rev() {
            if carry {
                indices[i] += 1;
                if indices[i] >= n {
                    indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            break; // All combinations exhausted
        }
    }

    Ok(false)
}

// ─── S-Expression Reconstruction ──────────────────────────────

/// Reconstruct s-expression with variable substitutions.
///
/// When a substitution exists for an ∃-bound variable:
/// - The `Exists` wrapper is removed (Skolemized away)
/// - All `Variable(v)` occurrences become `Const(substitute)`
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
                            // Substituted: variable → constant
                            format!("(Const \"{}\")", replacement)
                        } else {
                            format!("(Var \"{}\")", v)
                        }
                    }
                    LogicalTerm::Constant(c) => format!("(Const \"{}\")", c),
                    LogicalTerm::Description(d) => format!("(Desc \"{}\")", d),
                    LogicalTerm::Unspecified => "(Zoe)".to_string(),
                };
                args_str = format!("(Cons {} {})", term_str, args_str);
            }
            format!("(Pred \"{}\" {})", rel, args_str)
        }
        LogicNode::ExistsNode((v, body)) => {
            if subs.contains_key(v.as_str()) {
                // Skolemized: strip Exists wrapper, body carries the substitution
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
            format!(
                "(ForAll \"{}\" {})",
                v,
                reconstruct_sexp_with_subs(buffer, *body, subs)
            )
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
    }
}

/// Original s-expression reconstruction (no substitutions).
/// Used for non-existential queries.
fn reconstruct_sexp(buffer: &LogicBuffer, node_id: u32) -> String {
    reconstruct_sexp_with_subs(buffer, node_id, &HashMap::new())
}

bindings::export!(ReasoningComponent with_types_in bindings);
