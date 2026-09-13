use super::*;
pub(super) use nibli_types::abstraction::ABSTRACTION_MARKER_PREFIX;
use nibli_types::abstraction::canonicalize_relation;
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};

// ═══════════════════════════════════════════════════════════════════
// PREDICATE SIGNATURE VALIDATION
// ═══════════════════════════════════════════════════════════════════

/// How a predicate's arity was determined.
#[derive(Clone, Debug)]
pub enum SignatureSource {
    /// Arity from the committed English corpus (known predicate).
    Dictionary,
    /// Arity inferred from the first assertion (not in the corpus).
    Inferred,
    /// An engine-synthesized `rel_xN` role predicate (from event
    /// decomposition — always arity 2 `(event, filler)`). Never user-authored,
    /// so it is NOT arity-validated: the "inferred from first use" label and
    /// the arity-mismatch warning would both be category-confused for it.
    Synthetic,
}

/// Whether a relation name is an engine-synthesized `rel_xN` role predicate
/// (event decomposition emits `goes_x1`, `goes_x2`, … — always arity 2). These
/// are never user-authored, so they are classified `Synthetic` and exempt from
/// arity validation. Matches the `_x<digits>` suffix (the same role-predicate
/// convention used in nibli-semantics, e.g. `helpers.rs`/`lib.rs`).
pub(super) fn is_synthetic_role_predicate(rel: &str) -> bool {
    match rel.rsplit_once("_x") {
        Some((base, suffix)) => {
            !base.is_empty() && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit())
        }
        None => false,
    }
}

/// Registered predicate signature: arity + how it was determined.
#[derive(Clone, Debug)]
pub struct PredicateSignature {
    pub arity: usize,
    pub source: SignatureSource,
    /// Optional sort constraint for each argument position.
    /// Empty string = any sort (no constraint). Set via `set_predicate_sorts`.
    pub arg_sorts: Vec<String>,
}

// ═══════════════════════════════════════════════════════════════════
// INTEGRITY CONSTRAINTS
// ═══════════════════════════════════════════════════════════════════

/// A per-conclusion-predicate execution override recorded by
/// `set_rule_forward` / `set_rule_priority`. `None` means "never set" —
/// the rule's own registration default applies.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct RuleExecOverride {
    pub(super) forward: Option<bool>,
    pub(super) priority: Option<u32>,
}

/// An integrity constraint: a set of conjuncts that must NOT all hold simultaneously.
/// If every conjunct is satisfied in the KB, the constraint is violated.
#[derive(Clone, Debug)]
pub struct IntegrityConstraint {
    /// Human-readable label, e.g. "mutual-exclusion: gerku ∧ mlatu".
    pub label: String,
    /// Facts that must NOT all be true at the same time.
    pub conjuncts: Vec<StoredFact>,
    /// Predicate names appearing in conjuncts (for fast filtering).
    pub predicates: Vec<String>,
}

/// A disjunctive rule conclusion `∀x. P(x) → (Q(x) ∨ R(x))`, kept as the integrity
/// constraint `¬(P(x) ∧ ¬Q(x) ∧ ¬R(x))` rather than a derivation rule — a disjunctive
/// head is NOT a Horn clause, so deriving either disjunct alone would be unsound.
/// `check_contradictions` flags it when, for one consistent binding, every `conditions`
/// template (P) holds by storage or derivation AND every disjunct group is EXPLICITLY
/// denied (a stored `na <predicate>` covers it). The positive use ("is X a Q or an R?")
/// is served by a disjunctive QUERY, not by this constraint.
#[derive(Clone, Debug)]
pub(super) struct DisjunctiveConstraint {
    /// Human-readable label, e.g. "gerku → danlu ∨ xanlu".
    pub(super) label: String,
    /// Antecedent P templates (pattern vars), like a rule's `typed_conditions`.
    pub(super) conditions: Vec<StoredFact>,
    /// One template group per disjunct; each event-decomposes to ≥1 leaf template.
    pub(super) disjuncts: Vec<Vec<StoredFact>>,
}

/// Check integrity constraints relevant to a predicate after a fact insertion.
/// Returns Err with a violation message if any constraint is fully satisfied.
pub(super) fn check_constraints_for_predicate(
    rel: &str,
    inner: &KnowledgeBaseInner,
) -> Option<String> {
    for constraint in &inner.integrity_constraints {
        if !constraint.predicates.iter().any(|p| p == rel) {
            continue;
        }
        let all_hold = constraint
            .conjuncts
            .iter()
            .all(|c| inner.fact_store.contains(c));
        if all_hold {
            let facts: Vec<String> = constraint
                .conjuncts
                .iter()
                .map(|c| c.to_display_string())
                .collect();
            return Some(format!(
                "Integrity violation '{}': {} all hold simultaneously",
                constraint.label,
                facts.join(" ∧ ")
            ));
        }
    }
    None
}

/// Bounds-checked node access. Returns a descriptive error instead of panicking
/// if node_id is out of range (e.g., from a malformed LogicBuffer).
pub(super) fn get_node(buffer: &LogicBuffer, node_id: u32) -> Result<&LogicNode, String> {
    buffer.nodes.get(node_id as usize).ok_or_else(|| {
        format!(
            "invalid node index {} (buffer has {} nodes)",
            node_id,
            buffer.nodes.len()
        )
    })
}

/// Validate the runtime's one-flavor-per-formula-path invariant at the raw
/// [`LogicBuffer`] boundary. KR and the AST compiler reject mixed tense/deontic
/// prefixes, but embedders and persisted rows can provide a buffer directly.
/// Descending two flavor wrappers on one path used to let the inner wrapper
/// overwrite the outer one in facts, rules, NAF, queries, and proof traces.
///
/// The walk is path-sensitive: `And(Past(P), Obligatory(Q))` is legal because
/// neither branch nests a flavor, while `Past(Not(Obligatory(P)))` rejects.
/// `(node, already_flavored)` memoization handles DAG sharing and cycles without
/// conflating a node reached through differently flavored paths.
pub(super) fn validate_single_flavor_paths(buffer: &LogicBuffer) -> Result<(), String> {
    let mut stack: Vec<(u32, bool)> = buffer
        .roots
        .iter()
        .copied()
        .map(|root| (root, false))
        .collect();
    let mut visited: HashSet<(u32, bool)> = HashSet::new();

    while let Some((node_id, already_flavored)) = stack.pop() {
        if !visited.insert((node_id, already_flavored)) {
            continue;
        }
        match get_node(buffer, node_id)? {
            LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
            LogicNode::AndNode((left, right)) | LogicNode::OrNode((left, right)) => {
                stack.push((*right, already_flavored));
                stack.push((*left, already_flavored));
            }
            LogicNode::NotNode(inner)
            | LogicNode::ExistsNode((_, inner))
            | LogicNode::ForAllNode((_, inner))
            | LogicNode::CountNode((_, _, inner)) => {
                stack.push((*inner, already_flavored));
            }
            LogicNode::PastNode(inner)
            | LogicNode::PresentNode(inner)
            | LogicNode::FutureNode(inner)
            | LogicNode::ObligatoryNode(inner)
            | LogicNode::PermittedNode(inner) => {
                if already_flavored {
                    return Err(
                        "nested tense/deontic LogicNode wrappers are unsupported: the \
                         reasoner stores one flavor per fact or rule literal; rejecting \
                         the LogicBuffer rather than silently discarding a wrapper"
                            .to_string(),
                    );
                }
                stack.push((*inner, true));
            }
        }
    }
    Ok(())
}

/// Reject exact-count formulas at assertion ingress. `CountNode` is an
/// entailment/query operator: it computes the cardinality of the current model,
/// but the fact/rule store has no persistent cardinality-constraint object to
/// enforce after later assertions, equality changes, retractions, or replay.
///
/// Walk only nodes reachable from `roots`. `LogicBuffer::split_roots()` keeps a
/// shared arena, so nodes belonging exclusively to sibling roots are inert and
/// must not make an otherwise ordinary root fail.
pub(super) fn validate_no_count_assertions(buffer: &LogicBuffer) -> Result<(), String> {
    if contains_asserted_count_node(buffer) {
        return Err(
            "exact-count formulas (`exactly N` and `no`) are query-only and cannot \
             be asserted: the knowledge base does not persist or enforce cardinality \
             constraints. Assert ordinary facts, then evaluate the exact-count \
             formula through a query."
                .to_string(),
        );
    }
    Ok(())
}

/// Reject executable compute formulas at assertion ingress. `ComputeNode` is a
/// query/proof operator: its result belongs to the current evaluation only and
/// cannot be represented as a persistent fact or rule literal.
///
/// As with exact-count validation, only nodes reachable from `roots` are
/// assertion content. Opaque abstraction bodies remain quoted content.
pub(super) fn validate_no_compute_assertions(buffer: &LogicBuffer) -> Result<(), String> {
    if contains_asserted_compute_node(buffer) {
        return Err(
            "compute formulas are query-only and cannot be asserted: executable \
             ComputeNode content is evaluated only during a query proof and is \
             not persisted as a fact or rule literal. Assert ordinary facts, \
             then evaluate the compute formula through a query."
                .to_string(),
        );
    }
    Ok(())
}

/// Whether an exact-count formula occurs in an asserted position reachable
/// from `roots`.
///
/// Unreachable arena entries are deliberately ignored: `LogicBuffer::split_roots`
/// shares the full node arena between independently processed roots. Opaque
/// abstraction bodies are ignored too: their formulas are quoted content, not
/// assertions in the surrounding knowledge base. The walk is cycle-safe for
/// untrusted BYO/persisted buffers.
pub fn contains_asserted_count_node(buffer: &LogicBuffer) -> bool {
    contains_reachable_assertion_node(buffer, |node| matches!(node, LogicNode::CountNode(_)))
}

/// Whether an executable compute formula occurs in an asserted position
/// reachable from `roots`. Unreachable arena entries and opaque abstraction
/// bodies are ignored under the same contract as [`contains_asserted_count_node`].
pub fn contains_asserted_compute_node(buffer: &LogicBuffer) -> bool {
    contains_reachable_assertion_node(buffer, |node| matches!(node, LogicNode::ComputeNode(_)))
}

/// The reserved reference-external-compute name occurring in an ASSERTED
/// position reachable from `roots`, if any.
///
/// Matches the anchor/flat spelling AND the decomposed role spellings
/// (`exponential_x1` …) by collapsing through `materialize::surface_relation`,
/// on both `Predicate` and `ComputeNode` nodes — so the refusal is identical
/// whether or not the session has registered the name (a registered anchor is
/// already a `ComputeNode`). A user relation literally named `exponential_x1`
/// collapses onto the reserved anchor and is refused too — reserved-prefix
/// squatting, the same conservatism `split_role`'s doc accepts. Unreachable
/// arena entries and opaque abstraction bodies are ignored under the same
/// contract as [`contains_asserted_count_node`].
pub fn asserted_external_compute_name(buffer: &LogicBuffer) -> Option<&'static str> {
    nibli_types::relations::REFERENCE_EXTERNAL_COMPUTE
        .iter()
        .copied()
        .find(|name| {
            contains_reachable_assertion_node(buffer, |node| match node {
                LogicNode::Predicate((rel, _)) | LogicNode::ComputeNode((rel, _)) => {
                    crate::materialize::surface_relation(rel) == *name
                }
                _ => false,
            })
        })
}

/// Reject the reference external-compute names (`exponential`, `logarithm`) in
/// every asserted position, REGISTERED OR NOT (decided 2026-08-09).
///
/// A relation becomes a `ComputeNode` at COMPILE time against the session's
/// live registry, so before this guard, registration ORDER was load-bearing:
/// `exponential(2, 3, 8).` asserted before `register_compute_predicate`
/// carried no compute node, stored as an ordinary fact, and answered `TRUE` —
/// then the moment any session registered the name, the query side dispatched
/// the backend instead and the stored fact became unreachable forever (still
/// listed, still retractable, never consulted). That is the assert/query
/// divergence class the comparison guard below closes, minus the guard.
///
/// Unlike the comparisons, the test here is the NAME, not the operands: every
/// committed place of these two relations is numeric (result/base/power;
/// result/number/base), so there is no relational reading to protect — and a
/// registered query forwards even symbolic operands to the backend, so no
/// operand shape keeps the store consulted. For every other committed-corpus
/// relation, the registration-time guard closes the same divergence:
/// `CoreSession::register_compute_predicate` refuses while live stored
/// statements reference its canonical compiled name. Registration is not a
/// text vocabulary or arity declaration.
///
/// **Re-open trigger** (GUARANTEES §Disclosed Sharp Edges): a corpus or import
/// source that needs either name as ordinary relational vocabulary, or a
/// configurable reference set — either turns this static list into policy and
/// would need the operand-style test the comparison guard uses.
pub fn validate_no_external_compute_names(buffer: &LogicBuffer) -> Result<(), String> {
    let Some(name) = asserted_external_compute_name(buffer) else {
        return Ok(());
    };
    Err(format!(
        "`{name}` is reserved for EXTERNAL COMPUTE and is query-only: a query \
         dispatches it to the registered compute backend (`:compute {name}` plus \
         a backend wiring such as `enable_compute_backend`) and the computed \
         verdict wins, so a stored `{name}` fact or rule literal would never be \
         consulted — unreachable the moment the name is registered anywhere. \
         Assert ordinary facts, then evaluate `{name}(…)` through a query. \
         (Quoted content such as `fact {{ {name}(8, 2, 3) }}` remains assertable.)"
    ))
}

/// Whether this stored buffer's assertion-reachable content references
/// `relation` (role spellings collapsed onto the anchor ON BOTH SIDES — a
/// role-spelled target like `eats_x1` scans as its anchor `eats`, or a
/// registration under the role spelling would find no blockers while marking
/// exactly the role conjuncts every stored `eats` fact carries; `ComputeNode`
/// spellings included). Opaque quoted content and sibling-root arena entries
/// do not count — a quoted mention must not block compute registration,
/// exactly as it does not block assertion. This is the registration-guard
/// primitive behind `KnowledgeBase::stored_statement_ids_referencing`.
pub(super) fn buffer_references_relation(buffer: &LogicBuffer, relation: &str) -> bool {
    let target = crate::materialize::surface_relation(relation);
    contains_reachable_assertion_node(buffer, |node| match node {
        LogicNode::Predicate((rel, _)) | LogicNode::ComputeNode((rel, _)) => {
            crate::materialize::surface_relation(rel) == target
        }
        _ => false,
    })
}

/// Walk the assertion-visible subgraph of a raw [`LogicBuffer`].
///
/// `LogicBuffer::split_roots()` retains a shared arena, and abstraction bodies
/// are quoted in the right branch of `And(marker, body)`, so neither may be
/// treated as live assertion content. This common walker keeps query-only
/// operator guards aligned on both boundaries.
fn contains_reachable_assertion_node(
    buffer: &LogicBuffer,
    rejected: impl Fn(&LogicNode) -> bool,
) -> bool {
    let mut stack = buffer.roots.clone();
    let mut visited = HashSet::new();

    while let Some(node_id) = stack.pop() {
        if !visited.insert(node_id) {
            continue;
        }
        let Some(node) = buffer.nodes.get(node_id as usize) else {
            continue;
        };
        if rejected(node) {
            return true;
        }
        match node {
            LogicNode::AndNode((left, right)) => {
                if !is_abstraction_marker(buffer, *left) {
                    stack.push(*right);
                }
                stack.push(*left);
            }
            LogicNode::OrNode((left, right)) => {
                stack.push(*right);
                stack.push(*left);
            }
            LogicNode::NotNode(inner)
            | LogicNode::ExistsNode((_, inner))
            | LogicNode::ForAllNode((_, inner))
            | LogicNode::PastNode(inner)
            | LogicNode::PresentNode(inner)
            | LogicNode::FutureNode(inner)
            | LogicNode::ObligatoryNode(inner)
            | LogicNode::PermittedNode(inner)
            | LogicNode::CountNode((_, _, inner)) => stack.push(*inner),
            LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
        }
    }
    false
}

/// Pure structural checks that must run before any assertion-side mutation.
/// The external-compute NAME guard runs before the generic `ComputeNode` guard
/// so the same text yields the same (most specific) refusal regardless of the
/// session's registration state.
pub(super) fn validate_assertion_buffer(buffer: &LogicBuffer) -> Result<(), String> {
    validate_single_flavor_paths(buffer)?;
    validate_no_external_compute_names(buffer)?;
    validate_no_count_assertions(buffer)?;
    validate_no_compute_assertions(buffer)?;
    validate_no_operational_comparisons(buffer)
}

/// Reject an asserted `greater` / `less` / `num_equal` whose operands could be NUMBERS at
/// evaluation time — in a rule as much as in a ground fact.
///
/// These relations are ordinary `Predicate` nodes in the IR, but a QUERY does not answer
/// them from the store: `try_evaluate_numeric_group` computes them, and the computed value
/// wins. An ASSERTION has no such path — rule compilation lowers the same atom to a plain
/// `StoredFact` template — so the two halves disagree, and every way that disagreement can
/// show up is wrong:
///
/// * A positive guard is INERT. `person($x) & quantity($x, $n) & greater($n, 15) -> fit($x)`
///   looks up `greater` in a store that holds none, so the rule never fires and `fit` is
///   under-derived.
/// * A negated guard OVERFIRES. `… & ~greater($n, 15) -> rotten($x)` succeeds for EVERY
///   binding, because the stored extension is empty — so a subject whose quantity really is
///   greater than 15 is still concluded `rotten`. That is a definitive wrong TRUE, the one
///   failure class this engine exists to prevent. Worse, the stratifier classifies the
///   comparison as a BASE relation, so its extension reads as complete-and-empty rather
///   than unknown.
/// * A rule HEAD is dead on arrival. `quantity($x, $n) -> greater($n, 100)` derives a fact
///   the query twin never consults, because computation runs first.
///
/// The `ComputeNode` guard above cannot cover this: these atoms are not `ComputeNode`s, and
/// banning the relation outright would also ban the legitimate RELATIONAL reading —
/// `greater(Alis, Bob)` meaning "taller than", which is answered from the store on both
/// sides and is therefore consistent.
///
/// So the test is on the OPERANDS, not the relation: an operand that is a number literal
/// (definitely computable) or a variable (could bind to one) makes the atom potentially
/// operational and is refused; an atom whose operands are all non-numeric ground terms
/// keeps the relational reading and asserts normally. Conservative in the safe direction —
/// a rejected atom is a compile error the author can see, an accepted one can never compile
/// to a store lookup whose query twin computes.
///
/// This is a REFUSAL, not a semantics, and as of 2026-08-08 it is also the DECISION: making a
/// rule-position comparison compute on bound values was evaluated in full and declined. Four
/// things settled it, none of which is visible from the surface syntax:
///
/// 1. **It is not an atom swap.** `greater` has FOUR places (`less` four, `num_equal` three), so
///    `greater($n, 15)` compiles to an anchor plus N role predicates. The per-atom operand test
///    below cannot divert a group; diversion has to be group-level across `typed_conditions`
///    AND `negated_exists_groups` (a `~greater` never enters `typed_conditions` at all —
///    `register_clause_rule` turns it into a `NegatedExistsGroup`), with
///    `negated_condition_indices` remapped at every consumer and `register_rule`'s dependency-edge
///    rollback kept equal to the edges actually pushed.
/// 2. **The guard cannot be made position-aware where it runs.** There is no `ImpliesNode`; a
///    rule reaches `preflight_assertion_buffer` as a quantified disjunction over a DAG with
///    shared subtrees, and `Or(Q, Not(P))` is a reversed rule. "Antecedent, not head" is not
///    recoverable here, so a rule-only relaxation has no place to live.
/// 3. **Neither differential oracle can check the result.** `nibli-verify`'s TPTP path is FOF
///    with numbers as `num_<n>` Herbrand constants, and the ASP path renders them the same way;
///    teaching clingo to compare them as integers is a global rendering change, and mixing
///    constants with integers under a relational operator is vacuously true by ASP-Core-2 term
///    order — a wrong oracle rather than a skip. A computed rule guard would ship unchecked by
///    the two gates that exist to catch exactly this.
/// 4. **`materialize::project_rule` does not already refuse it.** `Ineligible::ComputeCondition`
///    fires only on FLAT conditions; a decomposed comparison takes the event-group path and
///    projects as an ordinary atom, so the saturator would seed it EMPTY and mark it complete.
///    That is latent today only because this guard makes it unreachable.
///
/// The capability therefore stays closed, and the honest idioms are named in the error message.
/// **Re-open trigger:** a differential oracle that can judge arithmetic (a TPTP TFA path, or a
/// number rendering both translators share with clingo's integer builtins). Until one exists,
/// refusing remains forward-compatible — that change would only ever ACCEPT more, so nothing
/// refused today becomes wrong later. What DID change is the query side: a comparison now filters
/// witnesses in find/count/aggregate as well as deciding the boolean verdict.
pub fn validate_no_operational_comparisons(buffer: &LogicBuffer) -> Result<(), String> {
    let Some(rel) = operational_comparison_in_assertion(buffer) else {
        return Ok(());
    };
    Err(format!(
        "`{rel}` over numeric operands is a computed comparison, not an assertable fact or \
         rule literal: a query evaluates it arithmetically and the computed value wins, so \
         an asserted one is never consulted — inert in a rule antecedent, and under `~` it \
         succeeds for every binding because nothing is stored. Three ways to say what you \
         meant: (1) evaluate the comparison in a QUERY — it decides the verdict and also \
         filters witnesses, so `quantity($x, $n) & {rel}($n, …)` finds exactly the rows past \
         the threshold; (2) assert the CLASSIFICATION as an ordinary predicate and let rules \
         read that, the way a narrow-therapeutic-index drug is marked `thin(Varfarin).`; \
         (3) for ordering rather than magnitude, use the numeral-free time relations \
         (`earlier`/`later`, `continue`/`cease`) — see `pins/temporal-order.nibli`. \
         (A comparison between non-numeric terms, such as `greater(Alis, Bob)`, is an \
         ordinary relational fact and asserts normally.)"
    ))
}

/// The base comparison relation of the first potentially-operational atom reachable from
/// `roots`, if any.
///
/// Reachability and opaque-abstraction skipping match
/// [`contains_reachable_assertion_node`]: unreachable arena entries belong to sibling roots,
/// and a quoted abstraction body is not an assertion about the surrounding knowledge base.
fn operational_comparison_in_assertion(buffer: &LogicBuffer) -> Option<String> {
    let mut stack = buffer.roots.clone();
    let mut visited = HashSet::new();
    while let Some(node_id) = stack.pop() {
        if !visited.insert(node_id) {
            continue;
        }
        let Some(node) = buffer.nodes.get(node_id as usize) else {
            continue;
        };
        match node {
            LogicNode::Predicate((relation, args)) => {
                if let Some(rel) = operational_comparison_atom(relation, args) {
                    return Some(rel);
                }
            }
            LogicNode::AndNode((left, right)) => {
                if !is_abstraction_marker(buffer, *left) {
                    stack.push(*right);
                }
                stack.push(*left);
            }
            LogicNode::OrNode((left, right)) => {
                stack.push(*right);
                stack.push(*left);
            }
            LogicNode::NotNode(inner)
            | LogicNode::ExistsNode((_, inner))
            | LogicNode::ForAllNode((_, inner))
            | LogicNode::PastNode(inner)
            | LogicNode::PresentNode(inner)
            | LogicNode::FutureNode(inner)
            | LogicNode::ObligatoryNode(inner)
            | LogicNode::PermittedNode(inner)
            | LogicNode::CountNode((_, _, inner)) => stack.push(*inner),
            LogicNode::ComputeNode(_) => {}
        }
    }
    None
}

/// Whether one atom is a comparison carrying an operand that could be a number.
///
/// Two spellings reach here. The event-decomposed one is what the KR surface produces —
/// `greater($n, 15)` becomes `∃ev. greater(ev) ∧ greater_x1(ev, $n) ∧ greater_x2(ev, 15)`,
/// so the OPERAND sits at `args[1]` of the `_x1`/`_x2` role atoms and the bare `greater(ev)`
/// anchor carries none. The flat two-argument one is reachable through direct `LogicBuffer`
/// injection and persisted-buffer replay, which do not event-decompose.
///
/// Only places 1 and 2 are inspected: `try_numeric_comparison` reads exactly those, so a
/// number in place 3 is inert on both sides and not a divergence. `Unspecified` (an unfilled
/// place) and `Description` are non-numeric and never make an atom operational.
fn operational_comparison_atom(relation: &str, args: &[LogicalTerm]) -> Option<String> {
    let computable =
        |t: &LogicalTerm| matches!(t, LogicalTerm::Number(_) | LogicalTerm::Variable(_));
    for base in nibli_types::relations::NUMERIC_COMPARISONS {
        let decomposed_operand = relation
            .strip_prefix(base)
            .is_some_and(|s| s == "_x1" || s == "_x2");
        if decomposed_operand && args.len() >= 2 && computable(&args[1]) {
            return Some((*base).to_string());
        }
        if relation == *base && args.len() >= 2 && (computable(&args[0]) || computable(&args[1])) {
            return Some((*base).to_string());
        }
    }
    None
}

/// Canonicalize/validate internal abstraction markers before using them as
/// opacity boundaries, then apply every structural assertion guard. Callers run
/// this before id allocation; `process_assertion` repeats it for replay defense.
pub(super) fn preflight_assertion_buffer(buffer: &mut LogicBuffer) -> Result<(), String> {
    canonicalize_abstraction_markers(buffer)?;
    validate_assertion_buffer(buffer)
}

/// The constraint-ingress twin of the assertion guards above, for the
/// `StoredFact`-vector path (`register_constraint`) that never sees a
/// `LogicBuffer`. A constraint conjunct only ever matches STORED facts, so a
/// conjunct over a shape assertion ingress refuses can never match anything:
/// the constraint is vacuously satisfied forever — inert, not unsound — and
/// silently accepting it tells the caller a guarantee exists that does not.
/// Shares the two guards with well-defined stored-fact semantics: the
/// reference external-compute NAMES (query-only in every asserted position,
/// role spellings collapsed like [`asserted_external_compute_name`]) and the
/// operational numeric COMPARISONS (computed by queries, never stored —
/// operand logic mirrors [`operational_comparison_atom`]: `Number` and
/// `PatternVar` count as computable, relational `greater(Alis, Bob)` stays
/// registrable per `pins/numeric-comparison-boundary.nibli`).
pub(super) fn validate_constraint_conjunct(fact: &StoredFact) -> Result<(), String> {
    let surface = crate::materialize::surface_relation(fact.relation()).to_string();
    if nibli_types::relations::is_reference_external_compute(&surface) {
        return Err(format!(
            "`{surface}` is reserved for EXTERNAL COMPUTE and is query-only, so an \
             integrity-constraint conjunct naming it can never match a stored fact \
             — assertion ingress refuses `{surface}` facts, leaving the constraint \
             vacuously satisfied forever (inert by construction). Constrain \
             ordinary asserted relations instead."
        ));
    }
    let args = &fact.inner().args;
    let computable =
        |t: &GroundTerm| matches!(t, GroundTerm::Number(_) | GroundTerm::PatternVar(_));
    for base in nibli_types::relations::NUMERIC_COMPARISONS {
        let decomposed_operand = fact
            .relation()
            .strip_prefix(base)
            .is_some_and(|s| s == "_x1" || s == "_x2");
        let operational = (decomposed_operand && args.len() >= 2 && computable(&args[1]))
            || (fact.relation() == *base
                && args.len() >= 2
                && (computable(&args[0]) || computable(&args[1])));
        if operational {
            return Err(format!(
                "`{base}` over numeric operands is a computed comparison, not a stored \
                 fact, so an integrity-constraint conjunct over it can never match — \
                 assertion ingress refuses it and queries compute it instead, leaving \
                 the constraint vacuously satisfied forever (inert by construction). \
                 Constrain an asserted CLASSIFICATION predicate instead (the \
                 `thin(Varfarin).` pattern). (A comparison between non-numeric terms, \
                 such as `greater(Alis, Bob)`, is an ordinary relational fact and \
                 constrains normally.)"
            ));
        }
    }
    Ok(())
}

/// Relation-name prefix of the opaque abstraction marker emitted by nibli-semantics for
/// `event`/`fact`/`property`/`amount`/`concept`. The marker is a versioned,
/// lossless alpha-canonical unary predicate
/// over the abstraction referent; in `And(marker, body)` the right sibling is the
/// abstraction BODY, which reasoning treats as OPAQUE — never collected as ground
/// facts, never checked — so asserting an abstraction (a belief, an obligation's
/// content) does not leak its inner predicates as free-standing truths. The marker
/// itself IS reasoned over: same content → same marker (abstractions unify),
/// different content → different marker (no spurious match). The body survives only
/// for rendering. See nibli-semantics `apply_predicate` (Abstraction arm).
/// Parse every internal abstraction marker before it reaches storage/matching.
/// The full v1 key is semantic identity; its digest prefix is recomputed here,
/// so equal keys with different supplied digests canonicalize together and
/// colliding digests with different keys remain distinct. Legacy hash-only,
/// malformed, and unknown-version spellings fail closed.
pub(super) fn canonicalize_abstraction_markers(buffer: &mut LogicBuffer) -> Result<(), String> {
    for node in &mut buffer.nodes {
        let relation = match node {
            LogicNode::Predicate((relation, args))
                if relation.starts_with(ABSTRACTION_MARKER_PREFIX) =>
            {
                if args.len() != 1 {
                    return Err(format!(
                        "malformed opaque-abstraction marker `{relation}`: internal markers \
                         must be unary Predicate nodes, got arity {}",
                        args.len()
                    ));
                }
                relation
            }
            LogicNode::ComputeNode((relation, _))
                if relation.starts_with(ABSTRACTION_MARKER_PREFIX) =>
            {
                return Err(format!(
                    "malformed opaque-abstraction marker `{relation}`: internal markers must \
                     be unary Predicate nodes, never ComputeNode"
                ));
            }
            _ => continue,
        };
        if let Some(canonical) =
            canonicalize_relation(relation).map_err(|error| error.to_string())?
        {
            *relation = canonical;
        }
    }
    Ok(())
}

/// True if `node_id` is the opaque abstraction marker predicate.
pub(super) fn is_abstraction_marker(buffer: &LogicBuffer, node_id: u32) -> bool {
    matches!(
        get_node(buffer, node_id),
        Ok(LogicNode::Predicate((rel, _))) if rel.starts_with(ABSTRACTION_MARKER_PREFIX)
    )
}

// ─── Typed Fact Representation ────────────────────────────────────
//
// These types replace the internal representation string layer. Facts are stored and
// matched structurally instead of via string serialization/tokenization.

/// The semantic sort of an engine-generated witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SkolemSort {
    Individual,
    Event,
}

/// Why an engine-generated witness exists.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SkolemOrigin {
    Generated,
    ExistentialImport,
}

/// Exact, non-display identity of an engine-generated witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SkolemId {
    source: SkolemSource,
    binder_ordinal: u32,
    sort: SkolemSort,
    origin: SkolemOrigin,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum SkolemSource {
    Assertion(u64),
    CycleSentinel,
}

/// Exact Skolem identity plus a presentation-only `sk_N` serial.
///
/// Equality, hashing, and ordering deliberately ignore `display_ordinal`: a
/// rebuild may renumber the friendly label without changing semantic identity.
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SkolemSymbol {
    id: SkolemId,
    display_ordinal: u64,
}

impl SkolemSymbol {
    pub fn display_name(self) -> String {
        format!("sk_{}", self.display_ordinal)
    }

    pub fn sort(self) -> SkolemSort {
        self.id.sort
    }

    pub fn origin(self) -> SkolemOrigin {
        self.id.origin
    }

    pub fn id(self) -> SkolemId {
        self.id
    }

    pub(super) fn new(
        assertion_id: u64,
        binder_ordinal: u32,
        display_ordinal: u64,
        sort: SkolemSort,
        origin: SkolemOrigin,
    ) -> Self {
        Self {
            id: SkolemId {
                source: SkolemSource::Assertion(assertion_id),
                binder_ordinal,
                sort,
                origin,
            },
            display_ordinal,
        }
    }

    pub(super) fn cycle_sentinel() -> Self {
        Self {
            id: SkolemId {
                source: SkolemSource::CycleSentinel,
                binder_ordinal: 0,
                sort: SkolemSort::Event,
                origin: SkolemOrigin::Generated,
            },
            display_ordinal: 0,
        }
    }

    #[cfg(test)]
    pub(super) fn for_test(display_ordinal: u64) -> Self {
        Self::new(
            0,
            display_ordinal as u32,
            display_ordinal,
            SkolemSort::Individual,
            SkolemOrigin::Generated,
        )
    }

    #[cfg(test)]
    pub(super) fn event_for_test(display_ordinal: u64) -> Self {
        Self::new(
            0,
            display_ordinal as u32,
            display_ordinal,
            SkolemSort::Event,
            SkolemOrigin::Generated,
        )
    }
}

impl PartialEq for SkolemSymbol {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for SkolemSymbol {}

impl Hash for SkolemSymbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialOrd for SkolemSymbol {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SkolemSymbol {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/// A ground term — the typed representation of a concrete term.
/// Implements `Hash`/`Eq` for direct use in hash-indexed fact stores.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GroundTerm {
    /// User-authored named constant (e.g., "adam", "paris", or the legal
    /// equal-looking spelling "sk_0"). Never used for an internal witness.
    Constant(String),
    /// Engine-generated independent witness. Its display spelling is not identity.
    Skolem(SkolemSymbol),
    /// Floating-point number stored as bit pattern for Hash/Eq.
    Number(u64),
    /// Opaque description term (le-determiner).
    Description(String),
    /// Unspecified argument (zo'e).
    Unspecified,
    /// Dependent Skolem function (e.g., a typed symbol applied to `adam`).
    SkolemFn(SkolemSymbol, Box<GroundTerm>),
    /// Multi-dependency pairing for SkolemFn with multiple universals.
    DepPair(Box<GroundTerm>, Box<GroundTerm>),
    /// Pattern variable — only used in rule templates, never in the fact store.
    PatternVar(String),
    /// Typed compiler placeholder for an existential nested under a universal.
    SkolemPlaceholder(SkolemSymbol),
}

impl GroundTerm {
    pub(super) fn contains_compiler_only_term(&self) -> bool {
        match self {
            GroundTerm::PatternVar(_) | GroundTerm::SkolemPlaceholder(_) => true,
            GroundTerm::SkolemFn(_, dependency) => dependency.contains_compiler_only_term(),
            GroundTerm::DepPair(left, right) => {
                left.contains_compiler_only_term() || right.contains_compiler_only_term()
            }
            GroundTerm::Constant(_)
            | GroundTerm::Skolem(_)
            | GroundTerm::Number(_)
            | GroundTerm::Description(_)
            | GroundTerm::Unspecified => false,
        }
    }

    fn user_constant_display(s: &str) -> String {
        let skolem_like = s.strip_prefix("sk_").is_some_and(|rest| {
            let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
            digits > 0 && (digits == rest.len() || rest.as_bytes().get(digits) == Some(&b'('))
        });
        if skolem_like {
            format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
        } else {
            s.to_string()
        }
    }

    /// Create a Number term from f64.
    pub fn from_f64(v: f64) -> Self {
        GroundTerm::Number(v.to_bits())
    }

    /// Extract f64 from a Number term.
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            GroundTerm::Number(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }

    /// Human-readable display string.
    pub fn to_display_string(&self) -> String {
        match self {
            GroundTerm::Constant(s) => Self::user_constant_display(s),
            GroundTerm::Skolem(symbol) => symbol.display_name(),
            GroundTerm::Number(bits) => {
                let v = f64::from_bits(*bits);
                if v == v.floor() && v.abs() < 1e15 {
                    format!("{}", v as i64)
                } else {
                    format!("{v}")
                }
            }
            // Surface spelling of a description term — kept in lock-step with
            // `LogicalTerm::Description`'s `trace_display` (nibli-types/src/logic.rs).
            GroundTerm::Description(s) => format!("the {s}"),
            GroundTerm::Unspecified => "_".to_string(),
            GroundTerm::SkolemFn(symbol, dep) => {
                format!("{}({})", symbol.display_name(), dep.to_display_string())
            }
            GroundTerm::DepPair(a, b) => {
                format!("({}, {})", a.to_display_string(), b.to_display_string())
            }
            GroundTerm::PatternVar(s) => format!("?{s}"),
            GroundTerm::SkolemPlaceholder(symbol) => {
                format!("?{}(universal-dependent)", symbol.display_name())
            }
        }
    }
}

/// A ground predicate — relation name plus argument list.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GroundFact {
    pub relation: String,
    pub args: Vec<GroundTerm>,
}

impl GroundFact {
    pub fn new(relation: impl Into<String>, args: Vec<GroundTerm>) -> Self {
        GroundFact {
            relation: relation.into(),
            args,
        }
    }

    /// Human-readable display: relation(arg1, arg2, ...)
    pub fn to_display_string(&self) -> String {
        if self.args.is_empty() {
            self.relation.clone()
        } else {
            let args_str: Vec<String> = self.args.iter().map(|a| a.to_display_string()).collect();
            format!("{}({})", self.relation, args_str.join(", "))
        }
    }
}

/// A fact with optional tense/deontic wrapper — the atomic unit of the fact store.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StoredFact {
    Bare(GroundFact),
    Past(GroundFact),
    Present(GroundFact),
    Future(GroundFact),
    Obligatory(GroundFact),
    Permitted(GroundFact),
}

impl StoredFact {
    /// Get the inner predicate's relation name.
    pub fn relation(&self) -> &str {
        match self {
            StoredFact::Bare(f)
            | StoredFact::Past(f)
            | StoredFact::Present(f)
            | StoredFact::Future(f)
            | StoredFact::Obligatory(f)
            | StoredFact::Permitted(f) => &f.relation,
        }
    }

    /// Get a reference to the inner GroundFact.
    pub fn inner(&self) -> &GroundFact {
        match self {
            StoredFact::Bare(f)
            | StoredFact::Past(f)
            | StoredFact::Present(f)
            | StoredFact::Future(f)
            | StoredFact::Obligatory(f)
            | StoredFact::Permitted(f) => f,
        }
    }

    /// Get a mutable reference to the inner GroundFact.
    fn inner_mut(&mut self) -> &mut GroundFact {
        match self {
            StoredFact::Bare(f)
            | StoredFact::Past(f)
            | StoredFact::Present(f)
            | StoredFact::Future(f)
            | StoredFact::Obligatory(f)
            | StoredFact::Permitted(f) => f,
        }
    }

    /// Wrap a GroundFact with the same tense/deontic context as another StoredFact.
    pub fn with_tense_from(fact: GroundFact, source: &StoredFact) -> Self {
        match source {
            StoredFact::Bare(_) => StoredFact::Bare(fact),
            StoredFact::Past(_) => StoredFact::Past(fact),
            StoredFact::Present(_) => StoredFact::Present(fact),
            StoredFact::Future(_) => StoredFact::Future(fact),
            StoredFact::Obligatory(_) => StoredFact::Obligatory(fact),
            StoredFact::Permitted(_) => StoredFact::Permitted(fact),
        }
    }

    /// Wrap a GroundFact with a tense/deontic context.
    pub fn with_tense(fact: GroundFact, tense: Option<&str>) -> Self {
        match tense {
            Some("Past") => StoredFact::Past(fact),
            Some("Present") => StoredFact::Present(fact),
            Some("Future") => StoredFact::Future(fact),
            Some("Obligatory") => StoredFact::Obligatory(fact),
            Some("Permitted") => StoredFact::Permitted(fact),
            _ => StoredFact::Bare(fact),
        }
    }

    /// Human-readable display string.
    pub fn to_display_string(&self) -> String {
        match self {
            StoredFact::Bare(f) => f.to_display_string(),
            StoredFact::Past(f) => format!("Past({})", f.to_display_string()),
            StoredFact::Present(f) => format!("Present({})", f.to_display_string()),
            StoredFact::Future(f) => format!("Future({})", f.to_display_string()),
            StoredFact::Obligatory(f) => format!("Obligatory({})", f.to_display_string()),
            StoredFact::Permitted(f) => format!("Permitted({})", f.to_display_string()),
        }
    }
}

/// Enforce the concrete-side groundness precondition at persistence and store
/// ingress. Pattern variables and dependent-Skolem placeholders are compiler
/// staging terms for rule templates; accepting either as a concrete fact would
/// invalidate structural unification's `NoVar` premise.
pub fn validate_stored_fact_groundness(fact: &StoredFact) -> Result<(), String> {
    if fact
        .inner()
        .args
        .iter()
        .any(GroundTerm::contains_compiler_only_term)
    {
        return Err(format!(
            "stored fact '{}' contains a compiler-only pattern variable or Skolem placeholder",
            fact.to_display_string()
        ));
    }
    Ok(())
}

/// Validate and canonicalize an opaque-abstraction relation carried by a
/// compiled fact. This is the storage/programmatic-ingress twin of
/// [`canonicalize_abstraction_markers`]: persisted `StoredFact` rows and
/// integrity constraints do not retain the originating `LogicBuffer`, so the
/// relation itself is the only available identity boundary.
///
/// Non-marker facts are unchanged. A valid v1 marker has its non-semantic
/// digest prefix recomputed from the full key. Legacy hash-only, malformed,
/// unknown-version, and non-unary markers fail closed.
pub fn canonicalize_stored_fact_abstraction_marker(fact: &mut StoredFact) -> Result<(), String> {
    let inner = fact.inner_mut();
    if !inner.relation.starts_with(ABSTRACTION_MARKER_PREFIX) {
        return Ok(());
    }
    if inner.args.len() != 1 {
        return Err(format!(
            "malformed opaque-abstraction marker `{}`: internal markers must be unary stored facts, got arity {}",
            inner.relation,
            inner.args.len()
        ));
    }
    if let Some(canonical) =
        canonicalize_relation(&inner.relation).map_err(|error| error.to_string())?
    {
        inner.relation = canonical;
    }
    Ok(())
}

/// Structural unification: match a template (with PatternVars) against a concrete fact.
/// Returns variable bindings on success, None on mismatch.
pub fn unify_facts(
    template: &StoredFact,
    concrete: &StoredFact,
) -> Option<HashMap<String, GroundTerm>> {
    // Tense/deontic wrapper must match.
    let (t_inner, c_inner) = match (template, concrete) {
        (StoredFact::Bare(t), StoredFact::Bare(c)) => (t, c),
        (StoredFact::Past(t), StoredFact::Past(c)) => (t, c),
        (StoredFact::Present(t), StoredFact::Present(c)) => (t, c),
        (StoredFact::Future(t), StoredFact::Future(c)) => (t, c),
        (StoredFact::Obligatory(t), StoredFact::Obligatory(c)) => (t, c),
        (StoredFact::Permitted(t), StoredFact::Permitted(c)) => (t, c),
        _ => return None,
    };

    // Relation name must match.
    if t_inner.relation != c_inner.relation {
        return None;
    }

    // Arg count must match.
    if t_inner.args.len() != c_inner.args.len() {
        return None;
    }

    // Unify each argument pair.
    let mut bindings = HashMap::new();
    for (t_arg, c_arg) in t_inner.args.iter().zip(c_inner.args.iter()) {
        if !unify_terms(t_arg, c_arg, &mut bindings) {
            return None;
        }
    }
    Some(bindings)
}

/// Unify a template term against a concrete term, accumulating bindings.
fn unify_terms(
    template: &GroundTerm,
    concrete: &GroundTerm,
    bindings: &mut HashMap<String, GroundTerm>,
) -> bool {
    match template {
        GroundTerm::PatternVar(name) => {
            if let Some(existing) = bindings.get(name) {
                // Variable already bound — must match.
                existing == concrete
            } else {
                bindings.insert(name.clone(), concrete.clone());
                true
            }
        }
        // Structural match for non-variable terms.
        GroundTerm::Constant(a) => matches!(concrete, GroundTerm::Constant(b) if a == b),
        GroundTerm::Skolem(a) => matches!(concrete, GroundTerm::Skolem(b) if a == b),
        GroundTerm::Number(a) => matches!(concrete, GroundTerm::Number(b) if a == b),
        GroundTerm::Description(a) => matches!(concrete, GroundTerm::Description(b) if a == b),
        GroundTerm::Unspecified => matches!(concrete, GroundTerm::Unspecified),
        GroundTerm::SkolemFn(name_a, dep_a) => {
            if let GroundTerm::SkolemFn(name_b, dep_b) = concrete {
                name_a == name_b && unify_terms(dep_a, dep_b, bindings)
            } else {
                false
            }
        }
        GroundTerm::DepPair(a1, a2) => {
            if let GroundTerm::DepPair(b1, b2) = concrete {
                unify_terms(a1, b1, bindings) && unify_terms(a2, b2, bindings)
            } else {
                false
            }
        }
        GroundTerm::SkolemPlaceholder(_) => false,
    }
}

/// Apply bindings to a template fact, replacing PatternVars with bound values.
pub fn substitute_fact(
    template: &StoredFact,
    bindings: &HashMap<String, GroundTerm>,
) -> StoredFact {
    let sub_inner = |f: &GroundFact| -> GroundFact {
        GroundFact {
            relation: f.relation.clone(),
            args: f
                .args
                .iter()
                .map(|a| substitute_term(a, bindings).into_owned())
                .collect(),
        }
    };
    match template {
        StoredFact::Bare(f) => StoredFact::Bare(sub_inner(f)),
        StoredFact::Past(f) => StoredFact::Past(sub_inner(f)),
        StoredFact::Present(f) => StoredFact::Present(sub_inner(f)),
        StoredFact::Future(f) => StoredFact::Future(sub_inner(f)),
        StoredFact::Obligatory(f) => StoredFact::Obligatory(sub_inner(f)),
        StoredFact::Permitted(f) => StoredFact::Permitted(sub_inner(f)),
    }
}

/// Apply bindings to a single term.
pub fn substitute_term<'a>(
    term: &'a GroundTerm,
    bindings: &HashMap<String, GroundTerm>,
) -> Cow<'a, GroundTerm> {
    match term {
        GroundTerm::PatternVar(name) => match bindings.get(name) {
            Some(replacement) => Cow::Owned(replacement.clone()),
            None => Cow::Borrowed(term),
        },
        GroundTerm::SkolemFn(name, dep) => {
            let new_dep = substitute_term(dep, bindings);
            match new_dep {
                Cow::Borrowed(_) => Cow::Borrowed(term),
                Cow::Owned(d) => Cow::Owned(GroundTerm::SkolemFn(*name, Box::new(d))),
            }
        }
        GroundTerm::DepPair(a, b) => {
            let new_a = substitute_term(a, bindings);
            let new_b = substitute_term(b, bindings);
            match (&new_a, &new_b) {
                (Cow::Borrowed(_), Cow::Borrowed(_)) => Cow::Borrowed(term),
                _ => Cow::Owned(GroundTerm::DepPair(
                    Box::new(new_a.into_owned()),
                    Box::new(new_b.into_owned()),
                )),
            }
        }
        // All other terms are ground — no substitution needed.
        _ => Cow::Borrowed(term),
    }
}

// ─── Knowledge Base State ────────────────────────────────────────

/// Registry entry for a SkolemFn created by native rule compilation.
/// Used by query-side existential checking to generate SkolemFn witness terms.
#[derive(Clone)]
pub(super) struct SkolemFnEntry {
    pub(super) symbol: SkolemSymbol,
    pub(super) dep_count: usize,
}

/// Prefix used for dependent Skolem placeholder variables.
/// A dependent Skolem is an ∃ variable nested under a ∀.
/// Build a human-readable rule label from typed conditions and conclusions.
pub(super) fn build_typed_rule_label(
    conditions: &[StoredFact],
    conclusions: &[StoredFact],
) -> String {
    let conds: Vec<String> = conditions
        .iter()
        .map(|f| f.relation().to_string())
        .collect();
    let concls: Vec<String> = conclusions
        .iter()
        .map(|f| f.relation().to_string())
        .collect();
    if conds.is_empty() {
        concls.join(" ∧ ")
    } else {
        format!("{} → {}", conds.join(" ∧ "), concls.join(" ∧ "))
    }
}

/// A negated, event-decomposed restrictor (`poi na <predicate>`) compiled as a
/// negation-as-failure check over an existential group. The condition holds for a
/// bound universal `x` iff NO binding of `event_var` satisfies ALL `conditions` —
/// e.g. `Not(Exists(ev, zanru(ev) ∧ zanru_x1(ev, x__v0) ∧ zanru_x2(ev, zo'e)))`
/// ("x has not consented"). The inner conjuncts are flat templates sharing the
/// universal's pattern var (`x__v0`) and a group-local event pattern var
/// (`ev___ev0`) enumerated during firing. A flat negated ATOM (`na broda`) stays
/// in `negated_condition_indices`; only a negated EXISTENTIAL GROUP lands here.
#[derive(Clone)]
pub(super) struct NegatedExistsGroup {
    /// Inner conjunct templates, e.g. `[zanru(ev), zanru_x1(ev, x__v0), zanru_x2(ev, zo'e)]`.
    pub(super) conditions: Vec<StoredFact>,
    /// Group-local event pattern-var name (e.g. `"ev___ev0"`), enumerated during firing.
    pub(super) event_var: String,
}

/// Which lowering path produced an executable rule. The distinction is retained
/// in the identity because the old deduplication key deliberately separated a
/// conditionless rule from a bare universal, even when their flat templates
/// happened to be equal.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum RuleKind {
    Conditional,
    BareUniversal,
}

/// Alpha-normalized term used only for rule identity. Runtime templates keep
/// their original names; this view replaces binder and generated-Skolem names
/// with ordinals while preserving every equality/dependency relationship.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum RuleTermIdentity {
    Constant(String),
    GeneratedGroundSkolem {
        ordinal: usize,
        sort: SkolemSort,
        origin: SkolemOrigin,
    },
    Number(u64),
    Description(String),
    Unspecified,
    SkolemFn {
        ordinal: usize,
        sort: SkolemSort,
        origin: SkolemOrigin,
        dependency: Box<RuleTermIdentity>,
    },
    DepPair(Box<RuleTermIdentity>, Box<RuleTermIdentity>),
    PatternVar(usize),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum RuleFactFlavor {
    Bare,
    Past,
    Present,
    Future,
    Obligatory,
    Permitted,
}

/// Lossless, immutable identity of one executable fact template.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct RuleFactIdentity {
    flavor: RuleFactFlavor,
    relation: String,
    args: Vec<RuleTermIdentity>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct NegatedExistsGroupIdentity {
    conditions: Vec<RuleFactIdentity>,
    event_var: usize,
}

/// Full semantic identity of an executable rule. Human labels, mutable
/// priorities, and source assertion ids are deliberately absent; every field
/// that changes firing behavior is present.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct RuleIdentity {
    kind: RuleKind,
    pattern_var_names: Vec<usize>,
    conditions: Vec<RuleFactIdentity>,
    conclusions: Vec<RuleFactIdentity>,
    negated_condition_indices: Vec<usize>,
    negated_exists_groups: Vec<NegatedExistsGroupIdentity>,
    forward: bool,
}

/// Stable citation of one executable rule produced by an asserted buffer.
///
/// One assertion may lower to multiple rules (for example, DNF branches), so
/// the durable assertion id alone is not enough.  The local ordinal is reset
/// for each buffer and incremented at every `register_rule` attempt, including
/// an attempt whose semantic identity is already registered.  Replaying the
/// same buffer under the same assertion id therefore reconstructs the same
/// source ids while duplicate assertions remain separately citable.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) struct RuleSourceId {
    pub(super) assertion_id: u64,
    pub(super) local_ordinal: u32,
}

#[derive(Clone)]
struct RuleIdentityEntry {
    identity: Arc<RuleIdentity>,
    /// Every active asserted rule source with this full semantic identity.
    /// Kept sorted and duplicate-free for deterministic proof output.
    sources: Vec<RuleSourceId>,
    /// Assertion-side metadata, deliberately outside executable-rule identity.
    /// A description universal may need to add its xorlo presupposition even
    /// when an alpha-equivalent prenex rule already registered the executable
    /// path. Once claimed, later duplicates do not mint another witness.
    existential_imported: bool,
}

#[derive(Default)]
struct RuleIdentityNormalizer {
    pattern_vars: HashMap<String, usize>,
    skolem_fns: HashMap<SkolemId, usize>,
    ground_skolems: HashMap<SkolemId, usize>,
}

impl RuleIdentityNormalizer {
    fn pattern_var(&mut self, name: &str) -> usize {
        let next = self.pattern_vars.len();
        *self.pattern_vars.entry(name.to_string()).or_insert(next)
    }

    fn skolem_fn(&mut self, symbol: SkolemSymbol) -> usize {
        let next = self.skolem_fns.len();
        *self.skolem_fns.entry(symbol.id()).or_insert(next)
    }

    fn ground_skolem(&mut self, symbol: SkolemSymbol) -> usize {
        let next = self.ground_skolems.len();
        *self.ground_skolems.entry(symbol.id()).or_insert(next)
    }

    fn term(&mut self, term: &GroundTerm) -> RuleTermIdentity {
        match term {
            GroundTerm::Constant(name) => RuleTermIdentity::Constant(name.clone()),
            GroundTerm::Skolem(symbol) => RuleTermIdentity::GeneratedGroundSkolem {
                ordinal: self.ground_skolem(*symbol),
                sort: symbol.sort(),
                origin: symbol.origin(),
            },
            GroundTerm::Number(bits) => RuleTermIdentity::Number(*bits),
            GroundTerm::Description(name) => RuleTermIdentity::Description(name.clone()),
            GroundTerm::Unspecified => RuleTermIdentity::Unspecified,
            GroundTerm::SkolemFn(symbol, dependency) => RuleTermIdentity::SkolemFn {
                ordinal: self.skolem_fn(*symbol),
                sort: symbol.sort(),
                origin: symbol.origin(),
                dependency: Box::new(self.term(dependency)),
            },
            GroundTerm::DepPair(left, right) => {
                RuleTermIdentity::DepPair(Box::new(self.term(left)), Box::new(self.term(right)))
            }
            GroundTerm::PatternVar(name) => RuleTermIdentity::PatternVar(self.pattern_var(name)),
            GroundTerm::SkolemPlaceholder(symbol) => RuleTermIdentity::GeneratedGroundSkolem {
                ordinal: self.ground_skolem(*symbol),
                sort: symbol.sort(),
                origin: symbol.origin(),
            },
        }
    }

    fn fact(&mut self, fact: &StoredFact) -> RuleFactIdentity {
        let (flavor, inner) = match fact {
            StoredFact::Bare(inner) => (RuleFactFlavor::Bare, inner),
            StoredFact::Past(inner) => (RuleFactFlavor::Past, inner),
            StoredFact::Present(inner) => (RuleFactFlavor::Present, inner),
            StoredFact::Future(inner) => (RuleFactFlavor::Future, inner),
            StoredFact::Obligatory(inner) => (RuleFactFlavor::Obligatory, inner),
            StoredFact::Permitted(inner) => (RuleFactFlavor::Permitted, inner),
        };
        RuleFactIdentity {
            flavor,
            relation: inner.relation.clone(),
            args: inner.args.iter().map(|term| self.term(term)).collect(),
        }
    }
}

impl RuleIdentity {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        kind: RuleKind,
        pattern_var_names: &[String],
        conditions: &[StoredFact],
        conclusions: &[StoredFact],
        negated_condition_indices: &[usize],
        negated_exists_groups: &[NegatedExistsGroup],
        forward: bool,
    ) -> Self {
        let mut normalizer = RuleIdentityNormalizer::default();
        let pattern_var_names = pattern_var_names
            .iter()
            .map(|name| normalizer.pattern_var(name))
            .collect();
        let conditions = conditions
            .iter()
            .map(|fact| normalizer.fact(fact))
            .collect();
        let conclusions = conclusions
            .iter()
            .map(|fact| normalizer.fact(fact))
            .collect();
        let negated_exists_groups = negated_exists_groups
            .iter()
            .map(|group| NegatedExistsGroupIdentity {
                conditions: group
                    .conditions
                    .iter()
                    .map(|fact| normalizer.fact(fact))
                    .collect(),
                event_var: normalizer.pattern_var(&group.event_var),
            })
            .collect();
        Self {
            kind,
            pattern_var_names,
            conditions,
            conclusions,
            negated_condition_indices: negated_condition_indices.to_vec(),
            negated_exists_groups,
            forward,
        }
    }
}

type RuleDigest = fn(&RuleIdentity) -> u64;

fn default_rule_digest(identity: &RuleIdentity) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    identity.hash(&mut hasher);
    hasher.finish()
}

/// Collision-safe rule identity index. The digest selects a bucket only; a
/// rule is a duplicate exactly when its full canonical identity compares equal.
#[derive(Clone)]
pub(super) struct RuleIdentityIndex {
    buckets: HashMap<u64, Vec<RuleIdentityEntry>>,
    digest: RuleDigest,
}

impl Default for RuleIdentityIndex {
    fn default() -> Self {
        Self {
            buckets: HashMap::new(),
            digest: default_rule_digest,
        }
    }
}

impl RuleIdentityIndex {
    pub(super) fn contains(&self, identity: &RuleIdentity) -> bool {
        let digest = (self.digest)(identity);
        self.buckets.get(&digest).is_some_and(|bucket| {
            bucket
                .iter()
                .any(|known| known.identity.as_ref() == identity)
        })
    }

    /// If the semantic identity already exists, attach this assertion's rule
    /// source and claim any description-universal import side effect.  Returns
    /// the interned full identity plus whether this call must mint the import.
    /// `None` means this is a genuinely new executable identity.
    pub(super) fn register_existing_source(
        &mut self,
        identity: &RuleIdentity,
        source: Option<RuleSourceId>,
        requests_existential_import: bool,
    ) -> Option<(Arc<RuleIdentity>, bool)> {
        let digest = (self.digest)(identity);
        let entry = self.buckets.get_mut(&digest).and_then(|bucket| {
            bucket
                .iter_mut()
                .find(|known| known.identity.as_ref() == identity)
        })?;

        if let Some(source) = source
            && !entry.sources.contains(&source)
        {
            entry.sources.push(source);
            entry.sources.sort_unstable();
        }

        let existential_import_required =
            requests_existential_import && !entry.existential_imported;
        if existential_import_required {
            entry.existential_imported = true;
        }
        Some((Arc::clone(&entry.identity), existential_import_required))
    }

    pub(super) fn insert(
        &mut self,
        identity: RuleIdentity,
        existential_imported: bool,
        source: Option<RuleSourceId>,
    ) -> Option<Arc<RuleIdentity>> {
        let digest = (self.digest)(&identity);
        let bucket = self.buckets.entry(digest).or_default();
        if bucket
            .iter()
            .any(|known| known.identity.as_ref() == &identity)
        {
            None
        } else {
            let identity = Arc::new(identity);
            let sources = source.into_iter().collect();
            bucket.push(RuleIdentityEntry {
                identity: Arc::clone(&identity),
                sources,
                existential_imported,
            });
            Some(identity)
        }
    }

    /// Active, durable sources for a full semantic rule identity.
    pub(super) fn source_ids(&self, identity: &RuleIdentity) -> Option<&[RuleSourceId]> {
        let digest = (self.digest)(identity);
        self.buckets.get(&digest).and_then(|bucket| {
            bucket
                .iter()
                .find(|known| known.identity.as_ref() == identity)
                .map(|known| known.sources.as_slice())
        })
    }

    pub(super) fn clear(&mut self) {
        self.buckets.clear();
    }

    #[cfg(test)]
    pub(super) fn force_digest_for_test(&mut self, digest: RuleDigest) {
        assert!(
            self.buckets.is_empty(),
            "the collision-test digest must be installed before rules are registered"
        );
        self.digest = digest;
    }

    #[cfg(test)]
    pub(super) fn identity_count(&self) -> usize {
        self.buckets.values().map(Vec::len).sum()
    }
}

/// Why a content-identical [`StoredFact`] is present in the truth store.
///
/// Origin is deliberately a sidecar rather than part of `StoredFact` identity:
/// duplicate assertions and multiple derivations support one logical tuple,
/// and making support participate in equality would break lookup, unification,
/// materialisation, and the argument-position index.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) enum StoredFactOrigin {
    /// A ground leaf emitted directly by one active user/KB assertion record.
    Assertion { assertion_id: u64 },
    /// A conclusion eagerly inserted by a positive forward rule.  The actual
    /// substituted premises are retained so proof construction never has to
    /// mislabel the tuple as an axiom or depend on a later depth-limited search.
    ForwardDerived {
        rule_identity: Arc<RuleIdentity>,
        premises: Vec<StoredFact>,
    },
    /// A fact minted by the explicitly enabled existential-import profile.
    /// This is licensed by a particular asserted rule, but is not itself a
    /// directly asserted ground fact.
    Presupposition { rule_source: RuleSourceId },
    /// An unattributed in-crate insertion (currently test/support code only).
    /// Proof rendering must never present this as a user assertion.
    Internal,
}

/// Records the structure of a compiled universal rule for backward-chaining provenance.
/// Templates use bare pattern variables (e.g., `x__v0`) instead of bound values.
#[derive(Clone)]
pub(super) struct UniversalRuleRecord {
    /// Full collision-safe semantic identity.  Human labels and mutable
    /// execution settings are not identity boundaries.
    pub(super) identity: Arc<RuleIdentity>,
    /// Human-readable label, e.g. "dog → animal"
    pub(super) label: String,
    /// Condition templates (with PatternVar terms for structural unification).
    pub(super) typed_conditions: Vec<StoredFact>,
    /// Executable conclusion templates (with PatternVar terms for unification).
    /// Quoted body atoms contribute dependency edges at registration, but never
    /// become executable conclusions in the surrounding knowledge base.
    pub(super) typed_conclusions: Vec<StoredFact>,
    /// Pattern variable names used in templates, e.g. ["x__v0"].
    pub(super) pattern_var_names: Vec<String>,
    /// Indices into `typed_conditions` that were originally under negation.
    /// Used for stratification checking — a negated condition creates a
    /// "negative" dependency edge in the predicate dependency graph.
    pub(super) negated_condition_indices: Vec<usize>,
    /// Negated event-decomposed restrictor groups (`poi na <predicate>`), each
    /// evaluated by NAF over an existential during firing. Empty for ordinary rules.
    pub(super) negated_exists_groups: Vec<NegatedExistsGroup>,
    /// When true, this rule fires eagerly on fact assertion (forward chaining).
    /// When false (default), the rule only fires via backward-chaining queries.
    pub(super) forward: bool,
    /// Rule priority (default 0). Higher = more important. When multiple rules
    /// match a goal, higher-priority rules are tried first (defeasible reasoning).
    pub(super) priority: u32,
}

/// Registry entry for a single asserted fact, supporting retraction and rebuild.
#[derive(Clone)]
pub(super) struct FactRecord {
    pub(super) id: u64,
    pub(super) buffer: Option<LogicBuffer>,
    pub(super) label: String,
    pub(super) retracted: bool,
}

/// All mutable KB state behind a single RefCell.
pub(super) struct KnowledgeBaseInner {
    /// An ambiguous durable commit requires reopening this KB before further use.
    pub(super) recovery_required: Option<String>,
    /// Presentation-only `sk_N` serial. Semantic identity is source-scoped.
    pub(super) skolem_counter: u64,
    /// Binder-local ordinal reset for each asserted LogicBuffer.
    pub(super) skolem_local_counter: u32,
    pub(super) known_entities: HashSet<GroundTerm>,
    /// Event-sort Skolem witnesses (from `_ev*` variables). Tracked for witness search
    /// and proof tracing, but NOT registered in `known_entities`
    /// to prevent quadratic blowup in guarded conjunction introduction.
    pub(super) known_event_entities: HashSet<GroundTerm>,
    /// Known description terms (from `le` determiner), tracked separately for InDomain.
    pub(super) known_descriptions: HashSet<String>,
    /// Finite numbers asserted into predicate facts (f64 bit patterns) —
    /// quantifier-domain members of the INDIVIDUAL sort, so `every` /
    /// `exactly N` / `some` all range over them (GUARANTEES §Disclosed Sharp
    /// Edges). Populated by `note_number` from `collect_and_note_constants`;
    /// query-time compute evaluation never grows the quantifier domain.
    pub(super) known_numbers: HashSet<u64>,
    pub(super) known_rules: RuleIdentityIndex,
    pub(super) skolem_fn_registry: Vec<SkolemFnEntry>,
    /// Derived individual membership and its completeness, rebuilt per query pass.
    pub(super) query_domain: QueryDomain,
    /// Pluggable fact store (in-memory or persistent).
    pub(super) fact_store: Box<dyn crate::fact_store::FactStore>,
    /// Multi-valued support for each content-identical tuple in `fact_store`.
    /// Every stored fact has a non-empty entry and no entry exists without its
    /// fact. Duplicate assertions therefore remain separately citable while the
    /// hot truth/index store stays set-valued.
    pub(super) fact_origins: HashMap<StoredFact, Vec<StoredFactOrigin>>,
    /// Compiled universal rule templates indexed by conclusion predicate name.
    /// Each predicate name maps to the rules whose conclusion templates mention it.
    /// Arc-wrapped so the backward-chain read path can borrow rules without cloning.
    /// INVARIANT: every bucket is kept sorted by DESCENDING priority at mutation
    /// time (`register_rule`, `set_rule_priority` call `sort_rule_bucket`), so the
    /// hot read path (`matching_rules_typed`) borrows a pre-sorted slice — no
    /// per-node clone or re-sort.
    pub(super) universal_rules: HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
    /// Monotonically increasing fact ID counter.
    pub(super) fact_counter: u64,
    /// Registry of all asserted facts (including retracted ones, for ID stability).
    // Compiled assertion payloads are immutable except on withdrawal. Share
    // them across isolated candidates; withdrawal uses copy-on-write.
    pub(super) fact_registry: HashMap<u64, Arc<FactRecord>>,
    /// Suppresses diagnostic prints during rebuild replay.
    pub(super) rebuilding: bool,
    /// Fresh, unpublished fixture construction may validate the graph once at
    /// completion. Ordinary assertion and replay keep their existing checks.
    pub(super) deferred_stratification: bool,
    /// Configuration parameter preserved across reset/rebuild (kept for WIT API compatibility).
    /// Cached typed domain members — invalidated when entities/descriptions change.
    pub(super) typed_domain_members_cache: Vec<GroundTerm>,
    /// Cached domain members of the INDIVIDUAL sort only (entities + le-descriptions,
    /// excluding event Skolems). The direct ForAll evaluator quantifies an
    /// individual variable, so it ranges over this — an event Skolem is never a
    /// legitimate counterexample for an individual universal. Built alongside the
    /// full cache; same dirty flag.
    pub(super) typed_non_event_members_cache: Vec<GroundTerm>,
    pub(super) domain_members_dirty: bool,
    /// Maximum backward-chaining depth for inference (default: 10).
    pub(super) max_chain_depth: usize,
    /// Predicate dependency graph for stratification checking.
    /// Maps conclusion predicate → Vec<(condition predicate, is_negative)>.
    pub(super) pred_dep_graph: HashMap<String, Vec<(String, bool)>>,
    /// Union-Find parent map for du-equivalence. Maps term → parent term.
    pub(super) equivalence_parent: HashMap<GroundTerm, GroundTerm>,
    /// Reverse index: canonical representative → all members of its class.
    pub(super) equivalence_classes: HashMap<GroundTerm, Vec<GroundTerm>>,
    /// Directly asserted equality evidence, retained as an undirected adjacency
    /// graph of the actual `equals(a,b)` facts. Union-find answers equivalence
    /// quickly but destroys the path that licensed it; proof construction uses
    /// this graph to recover real (possibly transitive) equality children.
    pub(super) equality_adjacency: HashMap<GroundTerm, Vec<(GroundTerm, StoredFact)>>,
    /// Predicate signature registry: tracks arity + source for each predicate.
    /// Populated lazily on first assertion. Warns on arity mismatch.
    pub(super) predicate_registry: HashMap<String, PredicateSignature>,
    /// Integrity constraints: conjunct sets that must NOT all hold simultaneously.
    /// Checked after each fact insertion. Violations are warnings in permissive mode.
    pub(super) integrity_constraints: Vec<IntegrityConstraint>,
    /// Argument-position index: (relation, arg_position) → {value → [facts]}.
    /// Speeds up witness extraction and ground-argument queries.
    pub(super) arg_position_index: HashMap<(String, usize), HashMap<GroundTerm, Vec<StoredFact>>>,
    /// Rule execution overrides (`set_rule_forward` / `set_rule_priority`),
    /// keyed by conclusion predicate — SESSION CONFIGURATION, like `strict`:
    /// consulted at every rule registration (`register_rule`'s bucket push), so
    /// the rebuild a retraction performs reapplies them by construction when
    /// replay re-registers the surviving rules. Deliberately absent from
    /// `rebuild_inner`'s clear list; cleared by `reset()` (the rules they
    /// configure die with the KB content).
    pub(super) rule_exec_overrides: HashMap<String, RuleExecOverride>,
    /// The current assertion's fact_registry ID (set during process_assertion).
    /// Used by compile_forall_to_rule to record rule sources.
    pub(super) current_assertion_id: Option<u64>,
    /// Per-buffer rule-source ordinal. Reset with the Skolem binder scope and
    /// incremented for every registration attempt, including duplicates.
    pub(super) current_rule_ordinal: u32,
    /// Depth counter for forward chaining recursion. Prevents infinite loops.
    pub(super) forward_depth: usize,
    /// Sort hierarchy: sort_name → set of parent sort names (transitive).
    /// e.g., "person" → {"animal"}, "animal" → {"entity"}
    pub(super) sort_hierarchy: HashMap<String, HashSet<String>>,
    /// Entity sort assignments: entity_name → sort_name.
    /// e.g., "adam" → "person"
    pub(super) entity_sorts: HashMap<String, String>,
    /// Predicates being traced for interactive debugging.
    /// When a traced predicate is encountered during reasoning, diagnostic
    /// output is printed showing depth, rule matches, and condition results.
    pub(super) traced_predicates: HashSet<String>,
    /// Explicitly asserted NEGATIVE ground facts (`na <predicate>`), stored as
    /// template groups for contradiction detection (`check_contradictions`).
    /// Each group is the conjunction of leaves under one negation, with event
    /// Skolem arguments generalized to pattern variables (see
    /// `record_negative_ground_fact`). Negatives never enter the positive fact
    /// store or predicate index — queries keep NAF/CWA semantics unchanged.
    pub(super) negative_facts: HashSet<Vec<StoredFact>>,
    /// Assertion ids whose explicit negations cannot be represented by the
    /// negative registry. Replayed and retracted together with that registry.
    pub(super) negative_scan_gaps: HashSet<u64>,
    /// Disjunctive rule conclusions registered as integrity constraints (see
    /// `DisjunctiveConstraint`). DERIVED from assertions → cleared on reset/rebuild
    /// and re-derived on replay (mirrors `negative_facts`/rules, NOT the standalone
    /// programmatic `integrity_constraints`).
    pub(super) disjunctive_constraints: Vec<DisjunctiveConstraint>,
    /// Cooperative cancellation flag (None = never cancels). Set by a native
    /// caller (the nibli-server request watchdog) when a query's wall-clock
    /// budget elapses; checked at the central reasoning entry points, which
    /// abort via the `Result::Err` channel. Default `None` keeps nibli-host/nibli-pipeline/
    /// tests byte-identical and needs no clock — the WASI sandbox forbids one.
    pub(super) cancel: Option<Arc<std::sync::atomic::AtomicBool>>,
    /// Per-instance external compute dispatch (replaces the old thread-local
    /// `register_compute_dispatch`, which the multithreaded server could never
    /// register because each tokio worker had its own `None` thread-local). Set
    /// via `KnowledgeBase::set_compute_dispatch`. Like `cancel`, this is
    /// CONFIGURATION, not derived state — NOT cleared by `reset()`. `None` means
    /// external predicates return an error (built-in arithmetic still works).
    pub(super) compute_eval: Option<crate::compute::EvalFn>,
    pub(super) compute_batch_eval: Option<crate::compute::BatchEvalFn>,
    /// Per-instance predicate-result cache (was a thread-local shared across all
    /// KBs on a thread). Interior-mutable because the backward-chain reads/writes
    /// it through a SHARED `&inner` (`check_predicate_in_kb_typed`). Only
    /// definitive True/False are cached; cleared at every KB mutation and at
    /// query start. `pred_cache_enabled` gates lookups (off during assertion
    /// replay, on during a query so results table across iterative-deepening
    /// passes). Per-KB isolation is a strict improvement for the multithreaded
    /// server (the old thread-local leaked across distinct KBs on a reused
    /// blocking-pool worker); byte-identical for single-KB embedders.
    pub(super) pred_cache: RefCell<HashMap<StoredFact, QueryResult>>,
    pub(super) pred_cache_enabled: Cell<bool>,
    /// SOUND DEPTH-CUT TABLE (the deep-chain-cliff fix): goal → the MAXIMUM
    /// remaining budget (`max_chain_depth - depth`) at which the goal is
    /// KNOWN to return `ResourceExceeded(Depth)`. Budget monotonicity makes
    /// the entry reusable for any remaining budget ≤ the recorded one (less
    /// budget can never prove more, and a definitive False requires an
    /// exhaustive search a smaller budget cuts even earlier) — within a
    /// deepening pass AND across passes (a deeper pass queries a larger
    /// budget, misses, re-derives once, raises the entry). Entries are only
    /// written when the derivation subtree saw NO cycle cut
    /// (`cycle_cut_epoch` unchanged) — a cycle-contaminated Depth is
    /// path-dependent and tabling it would be a completeness regression.
    /// Same lifecycle as `pred_cache` (cleared by `clear_typed_pred_cache`,
    /// gated by `pred_cache_enabled`, empty in Clone/reset). This is what
    /// keeps iterative deepening from re-deriving every horizon-cut subgoal
    /// ~30×/hop (see GUARANTEES §Completeness).
    pub(super) depth_cut_table: RefCell<HashMap<StoredFact, usize>>,
    /// Monotone counter bumped at every cycle cut — the contamination
    /// detector for `depth_cut_table` inserts (snapshot before deriving a
    /// goal; unchanged ⇒ the subtree's Depth verdict is path-independent).
    pub(super) cycle_cut_epoch: Cell<u64>,
    /// Monotone counter bumped whenever `negate_result_tracked` collapses any
    /// `Unknown(_)` into `NafDependent`. It is a diagnostic record of collapse
    /// sites for the final-leaf regression guards.
    ///
    /// The collapse is deliberate and Lean-pinned. The epoch never decides collection
    /// membership: every final non-definitive leaf refuses, while an abandoned internal
    /// attempt cannot turn an ultimately definitive leaf into an error.
    ///
    /// Wraparound is irrelevant: every use is an inequality against a snapshot.
    /// Zeroed by `Clone` (so `with_assumptions` never inherits a snapshot across KB
    /// instances) and not touched by `reset()`.
    pub(super) naf_cut_epoch: Cell<u64>,
    /// Transient SHARED budget for du-equivalence variant derivations
    /// (`DU_VARIANT_BOUND`): the OUTERMOST fallback invocation owns it
    /// (None → Some(bound)), nested probe fallbacks drain the same budget —
    /// a variant's Cartesian product is the SAME class product as the
    /// original goal's, so nested re-enumeration is redundant work, and the
    /// shared budget caps the TOTAL probe count per top-level fallback.
    /// Always restored to None by the owner.
    pub(super) du_variant_budget: Cell<Option<usize>>,
    /// Diagnostic verbosity. When `false` (the default) the informational stdout
    /// `println!` diagnostics (`[Rule]`/`[Skolem]`/`[Constraint] Registered`) are
    /// suppressed — a silent library for the server/validate/tavla. nibli-pipeline (the
    /// nibli-host REPL) and the native `nibli` REPL opt in via `set_verbose(true)`.
    /// Like `cancel`/`compute_eval`, this is CONFIGURATION, not derived state —
    /// NOT cleared by `reset()`. The `eprintln!` warning/error sites ignore it.
    pub(super) verbose: bool,
    /// STRICT MODE (opt-in): arity mismatches and integrity-constraint
    /// violations REJECT the offending fact instead of warn-and-insert. Like
    /// `verbose`, configuration — NOT cleared by `reset()`, and inert during
    /// `rebuilding` (a retraction replay must faithfully restore facts that
    /// were accepted when asserted).
    pub(super) strict: bool,
    /// Legacy EXISTENTIAL-IMPORT MODE (default OFF). When true, a DESCRIPTION
    /// universal (`animal(every dog).`)
    /// mints an origin-tagged internal witness so `∃x. dog(x)` holds and the
    /// witness participates in every logical find/count surface. Clean-core
    /// injects no entity (NIBLI_KR §14.4 item 3).
    /// Like `strict`,
    /// this is CONFIGURATION — NOT cleared by `reset()`.
    pub(super) existential_import: bool,
    /// DERIVED-ONLY (intensional / IDB) relations — declared in the KB itself by
    /// `derived_only("<relation>").`, or programmatically via
    /// `KnowledgeBase::declare_derived`. A relation in this set may ONLY become
    /// true by derivation; a direct ground assertion of it is REJECTED
    /// fail-closed in `process_assertion`, which unwinds the whole assertion
    /// atomically.
    ///
    /// The point is EDB/IDB separation. Without it a rule only ADDS a derivation
    /// path and never REMOVES assertability, so a KB that derives an authority
    /// credential (`… -> permits(Review, $a).`) cannot stop anyone from simply
    /// asserting `permits(Review, Sock).` and handing themselves one. Closing the
    /// relation turns "write one fact" into "edit the knowledge base", which is
    /// diffable and reviewable — that change in the shape of the attack is the
    /// whole value, and it is why this rejects rather than lints.
    ///
    /// Deliberately absent from `rebuild_inner`'s clear list, so a relation
    /// cannot become assertable again after a RETRACTION replay. It IS cleared by
    /// `reset()`, which wipes the KB: unlike `strict`/`existential_import` this is
    /// KB content declared in the KB text, not session configuration.
    pub(super) derived_only: HashSet<String>,
    /// ADMITTED (closed) base vocabulary — declared in the KB itself by
    /// `admits("<relation>").`, or programmatically via
    /// `KnowledgeBase::declare_admitted`. While this set is EMPTY the KB is OPEN
    /// and every corpus name may be asserted, which is v0.1's behaviour and stays
    /// the default. The FIRST declaration CLOSES the vocabulary: from then on a
    /// ground assertion whose relation is not admitted is REJECTED fail-closed in
    /// `process_assertion`, atomically, with the same shape `derived_only` uses.
    ///
    /// It is the DUAL of `derived_only`, and the two together close the extensional
    /// side completely: `derived_only(R)` says R may not be asserted, `admits(R)`
    /// says only R (and its fellows) may be. Without the second half a knowledge
    /// base can state what it refuses to take as evidence but not what it TAKES —
    /// so any corpus name at all still enters, and a document claiming "the record
    /// has exactly these entries" is claiming something the engine does not check.
    ///
    /// Same lifecycle as `derived_only`: absent from `rebuild_inner`'s clear list
    /// (a retraction replay cannot re-open the vocabulary) but cleared by
    /// `reset()`, because it is KB content rather than session configuration.
    pub(super) admitted: HashSet<String>,
    /// Constants minted as existential-import witnesses at
    /// description-universal registration (`animal(every dog).` presupposes
    /// ≥1 dog under the explicit legacy profile). They satisfy and are exposed
    /// by ∃/∀/find/count like every other logical domain member; the set exists
    /// to disclose their origin, not to exclude them.
    /// Violations collected by `assert_typed_fact` while strict mode rejects
    /// facts; drained by `process_assertion` into its error return. Internal
    /// forward-chaining insertions also reject loudly but have no user call to
    /// fail; their entries are cleared at the next assertion boundary.
    pub(super) strict_violations: Vec<String>,
    /// STRATUM-ORDERED MATERIALISATION (see [`crate::materialize`]): the saturated
    /// extensions of the surface relations read under `~`, so a NAF check is a set
    /// membership test instead of an exhaustive proof attempt.
    ///
    /// Built lazily at query start and dropped by `invalidate_materialization` at every
    /// KB MUTATION — not at query start, unlike `pred_cache`: this is a claim about the
    /// KB's content, so an unchanged KB should answer its second query from the same
    /// extension. Empty in `Clone`/`new`. It is ALSO cleared inside `rebuild_inner`,
    /// because `KnowledgeBase::rebuild` is the one rebuild entry point that does not
    /// pair itself with `invalidate_pred_cache`, and a stale saturation surviving a
    /// rebuild would answer `~p(x)` from a knowledge base that no longer exists.
    pub(super) materialized: RefCell<Option<crate::materialize::Materialized>>,
    /// Immutable rule projection and dependency strata shared by snapshots.
    /// Ground tuple changes do not alter this plan; their eligibility remains
    /// checked separately when the extensional store is seeded.
    pub(super) materialization_plan: RefCell<Option<Arc<crate::materialize::MaterializationPlan>>>,
    /// MATERIALISATION MODE (default ON). Like `strict`/`existential_import` this is
    /// session CONFIGURATION, not derived state — NOT cleared by `reset()`. Off means
    /// every NAF takes the backward-chaining path, which is what the differential gate
    /// compares against.
    pub(super) materialization: bool,
    /// Per-QUERY switch for the POSITIVE lookup only (the `ExistsNode` fast path); the
    /// NAF probe is unaffected. Lowered for the whole of a proof-traced query.
    ///
    /// Why a query-scoped flag rather than a `!S::RECORDING` test at the probe: the
    /// traced query runs in TWO phases, an untraced probe to find the resolving depth and
    /// then one recording build at that depth. Gating on the sink would let phase 1
    /// resolve at depth 1 by lookup and then hand phase 2 a depth the backward chainer
    /// cannot reach — turning a TRUE into `ResourceExceeded(Depth)`. Both phases must
    /// agree on which evaluator they are using.
    pub(super) positive_lookup: Cell<bool>,
    /// Transient (per `query_find`): set when witness enumeration evaluates a
    /// candidate whose final leaf is `Unknown(_)` or `ResourceExceeded(_)` rather
    /// than definitive False. `query_find_inner` resets it before enumeration and
    /// checks it after, so `count_witnesses` / `aggregate` REFUSE to emit a partial
    /// collection as definitive.
    /// Not configuration; not cleared by `reset()` (query_find owns its lifecycle).
    pub(super) find_enumeration_incomplete: bool,
    /// Transient (per `query_find`): witness enumeration is running, so external
    /// compute MUST NOT be dispatched.
    ///
    /// Enumeration evaluates its body once per candidate, so a dispatching leaf would
    /// issue one request per candidate over a transport with no request binding,
    /// idempotency, or replay detection (GUARANTEES §External Compute Admission
    /// Policy). The budget is therefore ZERO, and it is enforced here rather than at
    /// each caller: `dispatch_to_backend` / `dispatch_batch_to_backend` are the single
    /// choke point every route funnels through, so a new evaluation path cannot forget
    /// to honour it.
    ///
    /// This is a SCOPE refusal, not an outage: the resulting
    /// `Unknown(BackendUnavailable)` is non-definitive, so find/count/aggregate refuse
    /// as incomplete rather than undercount — but the backend was never
    /// consulted and may be perfectly healthy. Anything decidable LOCALLY (a numeric
    /// comparison, or built-in arithmetic over resolved operands) is decided before
    /// reaching a dispatch and is unaffected.
    ///
    /// Scoped to the DYNAMIC EXTENT of `query_find_inner`, which sets it on the way in
    /// and clears it on the way out (including every error path). The entailment
    /// entries also clear it as defence in depth. `reset()` does not touch it.
    pub(super) find_enumeration: bool,
}

impl Clone for KnowledgeBaseInner {
    fn clone(&self) -> Self {
        Self {
            recovery_required: self.recovery_required.clone(),
            skolem_counter: self.skolem_counter,
            skolem_local_counter: self.skolem_local_counter,
            known_entities: self.known_entities.clone(),
            known_event_entities: self.known_event_entities.clone(),
            known_descriptions: self.known_descriptions.clone(),
            known_numbers: self.known_numbers.clone(),
            known_rules: self.known_rules.clone(),
            skolem_fn_registry: self.skolem_fn_registry.clone(),
            query_domain: QueryDomain::default(),
            fact_store: self.fact_store.clone_box(),
            fact_origins: self.fact_origins.clone(),
            universal_rules: self.universal_rules.clone(),
            fact_counter: self.fact_counter,
            fact_registry: self.fact_registry.clone(),
            rebuilding: false,
            deferred_stratification: false,
            typed_domain_members_cache: self.typed_domain_members_cache.clone(),
            typed_non_event_members_cache: self.typed_non_event_members_cache.clone(),
            domain_members_dirty: true,
            max_chain_depth: self.max_chain_depth,
            pred_dep_graph: self.pred_dep_graph.clone(),
            equivalence_parent: self.equivalence_parent.clone(),
            equivalence_classes: self.equivalence_classes.clone(),
            equality_adjacency: self.equality_adjacency.clone(),
            predicate_registry: self.predicate_registry.clone(),
            integrity_constraints: self.integrity_constraints.clone(),
            arg_position_index: self.arg_position_index.clone(),
            rule_exec_overrides: self.rule_exec_overrides.clone(),
            current_assertion_id: None,
            current_rule_ordinal: 0,
            forward_depth: 0,
            sort_hierarchy: self.sort_hierarchy.clone(),
            entity_sorts: self.entity_sorts.clone(),
            traced_predicates: self.traced_predicates.clone(),
            negative_facts: self.negative_facts.clone(),
            negative_scan_gaps: self.negative_scan_gaps.clone(),
            disjunctive_constraints: self.disjunctive_constraints.clone(),
            cancel: self.cancel.clone(),
            compute_eval: self.compute_eval,
            compute_batch_eval: self.compute_batch_eval,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
            depth_cut_table: RefCell::new(HashMap::new()),
            cycle_cut_epoch: Cell::new(0),
            naf_cut_epoch: Cell::new(0),
            du_variant_budget: Cell::new(None),
            verbose: self.verbose,
            strict: self.strict,
            existential_import: self.existential_import,
            derived_only: self.derived_only.clone(),
            admitted: self.admitted.clone(),
            strict_violations: Vec::new(),
            materialized: RefCell::new(None),
            materialization_plan: RefCell::new(self.materialization_plan.borrow().clone()),
            materialization: self.materialization,
            positive_lookup: Cell::new(true),
            find_enumeration_incomplete: false,
            find_enumeration: false,
        }
    }
}

impl KnowledgeBaseInner {
    pub(super) fn new() -> Self {
        Self {
            recovery_required: None,
            skolem_counter: 0,
            skolem_local_counter: 0,
            known_entities: HashSet::new(),
            known_event_entities: HashSet::new(),
            known_descriptions: HashSet::new(),
            known_numbers: HashSet::new(),
            known_rules: RuleIdentityIndex::default(),
            skolem_fn_registry: Vec::new(),
            query_domain: QueryDomain::default(),
            fact_store: Box::new(crate::fact_store::InMemoryFactStore::new()),
            fact_origins: HashMap::new(),
            universal_rules: HashMap::new(),
            fact_counter: 0,
            fact_registry: HashMap::new(),
            rebuilding: false,
            deferred_stratification: false,
            typed_domain_members_cache: Vec::new(),
            typed_non_event_members_cache: Vec::new(),
            domain_members_dirty: true,
            max_chain_depth: 10,
            pred_dep_graph: HashMap::new(),
            equivalence_parent: HashMap::new(),
            equivalence_classes: HashMap::new(),
            equality_adjacency: HashMap::new(),
            predicate_registry: HashMap::new(),
            integrity_constraints: Vec::new(),
            arg_position_index: HashMap::new(),
            rule_exec_overrides: HashMap::new(),
            current_assertion_id: None,
            current_rule_ordinal: 0,
            forward_depth: 0,
            sort_hierarchy: HashMap::new(),
            entity_sorts: HashMap::new(),
            traced_predicates: HashSet::new(),
            negative_facts: HashSet::new(),
            negative_scan_gaps: HashSet::new(),
            disjunctive_constraints: Vec::new(),
            cancel: None,
            compute_eval: None,
            compute_batch_eval: None,
            pred_cache: RefCell::new(HashMap::new()),
            pred_cache_enabled: Cell::new(false),
            depth_cut_table: RefCell::new(HashMap::new()),
            cycle_cut_epoch: Cell::new(0),
            naf_cut_epoch: Cell::new(0),
            du_variant_budget: Cell::new(None),
            verbose: false,
            strict: false,
            // Clean-core is the high-assurance default: universals do not mint
            // entities. Legacy xorlo-style existential import is explicit opt-in.
            existential_import: false,
            derived_only: HashSet::new(),
            admitted: HashSet::new(),
            strict_violations: Vec::new(),
            materialized: RefCell::new(None),
            materialization_plan: RefCell::new(None),
            // Materialisation defaults ON. Turning it off restores the pure
            // backward-chaining path byte-for-byte, which is what makes the ON/OFF
            // differential in `nibli-verify` expressible.
            materialization: true,
            positive_lookup: Cell::new(true),
            find_enumeration_incomplete: false,
            find_enumeration: false,
        }
    }

    pub(super) fn reset(&mut self) {
        self.skolem_counter = 0;
        self.skolem_local_counter = 0;
        self.known_entities.clear();
        self.known_event_entities.clear();
        self.known_descriptions.clear();
        self.known_numbers.clear();
        self.known_rules.clear();
        self.skolem_fn_registry.clear();
        self.query_domain = QueryDomain::default();
        self.fact_store.clear();
        self.fact_origins.clear();
        self.universal_rules.clear();
        self.fact_counter = 0;
        self.fact_registry.clear();
        self.rebuilding = false;
        self.typed_domain_members_cache.clear();
        self.typed_non_event_members_cache.clear();
        self.domain_members_dirty = true;
        self.pred_dep_graph.clear();
        self.equivalence_parent.clear();
        self.equivalence_classes.clear();
        self.equality_adjacency.clear();
        self.predicate_registry.clear();
        self.arg_position_index.clear();
        // Session-configured execution overrides die with the rules they
        // configure (reset() drops KB content; a fresh KB starts unconfigured).
        self.rule_exec_overrides.clear();
        self.current_assertion_id = None;
        self.current_rule_ordinal = 0;
        self.forward_depth = 0;
        self.negative_facts.clear();
        self.negative_scan_gaps.clear();
        self.disjunctive_constraints.clear();
        // `derived_only` IS cleared here, unlike `strict`/`existential_import`:
        // it is KB CONTENT (declared by a `derived_only("…")` statement in the KB
        // text), not session configuration, so a wiped KB must start with no
        // closures. Retraction safety does NOT depend on this — `rebuild_inner`
        // has its own clear list which deliberately omits `derived_only`, and the
        // declaration is re-asserted by replay regardless.
        self.derived_only.clear();
        self.admitted.clear();
        self.pred_cache.borrow_mut().clear();
        self.pred_cache_enabled.set(false);
        self.depth_cut_table.borrow_mut().clear();
        // The saturation is derived from facts+rules that no longer exist.
        *self.materialized.borrow_mut() = None;
        *self.materialization_plan.borrow_mut() = None;
        // Note: integrity_constraints, compute_eval/compute_batch_eval, cancel,
        // verbose, strict, existential_import, and materialization are NOT cleared on
        // reset —
        // they're structural declarations / configuration, not derived state.
        // Imported-witness origin is carried structurally by each typed Skolem;
        // reset clears the witnesses while the flag that gates minting survives.
        // Clear explicitly if needed.
    }

    /// Whether informational stdout diagnostics should print: only when the
    /// caller opted into verbosity AND we are not mid-rebuild (replay re-emits
    /// already-seen state). The `eprintln!` warning/error sites are independent.
    #[inline]
    pub(super) fn diag_enabled(&self) -> bool {
        !self.rebuilding && self.verbose
    }

    pub(super) fn fresh_fact_id(&mut self) -> Result<u64, String> {
        let id = self.fact_counter;
        self.fact_counter = self.fact_counter.checked_add(1).ok_or_else(|| {
            "fact-id space exhausted; assertion ids are monotonic semantic Skolem sources"
                .to_string()
        })?;
        Ok(id)
    }

    pub(super) fn begin_skolem_scope(&mut self) {
        self.skolem_local_counter = 0;
        self.current_rule_ordinal = 0;
    }

    /// Mint the stable source id for the next rule registration attempt in the
    /// current asserted buffer. Internal-only callers have no assertion source
    /// and return `None`; no synthetic user id is fabricated for them.
    pub(super) fn next_rule_source_id(&mut self) -> Result<Option<RuleSourceId>, String> {
        let Some(assertion_id) = self.current_assertion_id else {
            return Ok(None);
        };
        let local_ordinal = self.current_rule_ordinal;
        self.current_rule_ordinal = self.current_rule_ordinal.checked_add(1).ok_or_else(|| {
            format!("assertion #{assertion_id} exhausted the per-buffer rule-source ordinal space")
        })?;
        Ok(Some(RuleSourceId {
            assertion_id,
            local_ordinal,
        }))
    }

    /// All active supports for an exact stored tuple.
    pub(super) fn fact_origins_for(&self, fact: &StoredFact) -> &[StoredFactOrigin] {
        self.fact_origins
            .get(fact)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Full content/support consistency check used by invariant tests and
    /// debug assertions at lifecycle boundaries (not on the insertion hot path,
    /// where a full scan would make corpus loading quadratic).
    pub(super) fn fact_origin_invariant_holds(&self) -> bool {
        self.fact_store
            .all_facts()
            .all(|fact| !self.fact_origins_for(fact).is_empty())
            && self
                .fact_origins
                .iter()
                .all(|(fact, origins)| !origins.is_empty() && self.fact_store.contains(fact))
    }

    pub(super) fn fresh_skolem(&mut self, sort: SkolemSort, origin: SkolemOrigin) -> SkolemSymbol {
        let assertion_id = self
            .current_assertion_id
            .expect("Skolem witnesses are minted only inside an attributed assertion");
        let symbol = SkolemSymbol::new(
            assertion_id,
            self.skolem_local_counter,
            self.skolem_counter,
            sort,
            origin,
        );
        self.skolem_local_counter = self
            .skolem_local_counter
            .checked_add(1)
            .expect("one assertion exhausted the Skolem binder-ordinal space");
        self.skolem_counter = self
            .skolem_counter
            .checked_add(1)
            .expect("the knowledge base exhausted the Skolem display space");
        symbol
    }

    pub(super) fn note_entity(&mut self, term: GroundTerm) {
        debug_assert!(matches!(
            term,
            GroundTerm::Constant(_) | GroundTerm::Skolem(_)
        ));
        if self.known_entities.insert(term) {
            self.domain_members_dirty = true;
        }
    }

    /// Track an event Skolem constant for witness search and proof tracing,
    /// without registering it in `known_entities`.
    pub(super) fn note_event_entity(&mut self, term: GroundTerm) {
        debug_assert!(matches!(
            term,
            GroundTerm::Skolem(symbol) if symbol.sort() == SkolemSort::Event
        ));
        if self.known_event_entities.insert(term) {
            self.domain_members_dirty = true;
        }
    }

    pub(super) fn note_description(&mut self, name: &str) {
        if self.known_descriptions.insert(name.to_string()) {
            self.domain_members_dirty = true;
        }
    }

    /// Track a finite number asserted into a predicate fact as a quantifier-domain
    /// member. Non-finite values (NaN/±inf) are deliberately excluded; stored
    /// non-finite facts remain index-reachable, while exact `CountNode` continues
    /// to enumerate this finite-only general domain.
    pub(super) fn note_number(&mut self, value: f64) {
        if value.is_finite() && self.known_numbers.insert(value.to_bits()) {
            self.domain_members_dirty = true;
        }
    }

    /// Return all known domain members as (representation, LogicalTerm) pairs.
    /// Ensure the domain members cache is up-to-date. Call before any query.
    pub(super) fn ensure_domain_members_cached(&mut self) {
        if !self.domain_members_dirty {
            return;
        }
        let mut typed_members = Vec::new();
        // The non-event (individual) cache: entities + le-descriptions, no event
        // Skolems. Built in the SAME pass — individual-sort members go into both.
        let mut non_event_members = Vec::new();
        for e in &self.known_entities {
            typed_members.push(e.clone());
            non_event_members.push(e.clone());
        }
        for e in &self.known_event_entities {
            // Event Skolems are a distinct sort — full cache only.
            typed_members.push(e.clone());
        }
        for d in &self.known_descriptions {
            let t = GroundTerm::Description(d.clone());
            typed_members.push(t.clone());
            non_event_members.push(t);
        }
        for bits in &self.known_numbers {
            // Asserted numbers are INDIVIDUAL-sort members: both caches, so
            // universal, count, and existential evaluation all reach them.
            let t = GroundTerm::Number(*bits);
            typed_members.push(t.clone());
            non_event_members.push(t);
        }

        // Determinism: the source sets are HashSets whose iteration order
        // depends on the process hasher seed. Sort once at the cache boundary
        // so domain iteration (ForAll/Exists evaluation, witness search,
        // ForallVerified proof output) is byte-reproducible across runs.
        typed_members.sort();
        non_event_members.sort();

        self.typed_domain_members_cache = typed_members;
        self.typed_non_event_members_cache = non_event_members;
        self.domain_members_dirty = false;
    }

    /// Return typed domain members. Call ensure_domain_members_cached() first.
    pub(super) fn all_typed_domain_members(&self) -> &[GroundTerm] {
        &self.typed_domain_members_cache
    }

    /// Return the INDIVIDUAL-sort domain members (entities + le-descriptions,
    /// excluding event Skolems). Used by the direct ForAll evaluator — an event
    /// Skolem is never a legitimate counterexample for an individual universal.
    /// Call ensure_domain_members_cached() first.
    pub(super) fn all_non_event_domain_members(&self) -> &[GroundTerm] {
        &self.typed_non_event_members_cache
    }
}

// ═══════════════════════════════════════════════════════════════════
// EQUALITY / UNION-FIND for `du` predicate
// ═══════════════════════════════════════════════════════════════════

/// Find the canonical representative of a term (path-compressing).
pub(super) fn find_canonical(
    parent: &mut HashMap<GroundTerm, GroundTerm>,
    term: &GroundTerm,
) -> GroundTerm {
    let p = match parent.get(term) {
        Some(p) => p.clone(),
        None => return term.clone(),
    };
    if &p == term {
        return p;
    }
    let root = find_canonical(parent, &p);
    // Path compression
    parent.insert(term.clone(), root.clone());
    root
}

/// Non-compressing find (for `&` contexts where mutation is not available).
pub(super) fn find_canonical_readonly(
    parent: &HashMap<GroundTerm, GroundTerm>,
    term: &GroundTerm,
) -> GroundTerm {
    let mut current = term.clone();
    loop {
        match parent.get(&current) {
            Some(p) if p != &current => current = p.clone(),
            _ => return current,
        }
    }
}

/// Congruence for the engine's typed, source-scoped witness functions. Only
/// dependency terms are normalized; the symbol's source, ordinal, sort and
/// origin remain part of identity.
pub(super) fn canonical_witness_term(
    parent: &HashMap<GroundTerm, GroundTerm>,
    term: &GroundTerm,
) -> GroundTerm {
    let representative = find_canonical_readonly(parent, term);
    match representative {
        GroundTerm::SkolemFn(symbol, dependency) => GroundTerm::SkolemFn(
            symbol,
            Box::new(canonical_witness_term(parent, &dependency)),
        ),
        GroundTerm::DepPair(left, right) => GroundTerm::DepPair(
            Box::new(canonical_witness_term(parent, &left)),
            Box::new(canonical_witness_term(parent, &right)),
        ),
        other => other,
    }
}

/// Union two terms under the `du` equivalence relation.
pub(super) fn union_terms(inner: &mut KnowledgeBaseInner, a: &GroundTerm, b: &GroundTerm) {
    let root_a = find_canonical(&mut inner.equivalence_parent, a);
    let root_b = find_canonical(&mut inner.equivalence_parent, b);
    if root_a == root_b {
        return; // Already equivalent.
    }

    // Merge smaller class into larger (union by size).
    let size_a = inner
        .equivalence_classes
        .get(&root_a)
        .map_or(1, |c| c.len());
    let size_b = inner
        .equivalence_classes
        .get(&root_b)
        .map_or(1, |c| c.len());
    let (winner, loser) = if size_a >= size_b {
        (root_a, root_b)
    } else {
        (root_b, root_a)
    };

    // A `du` link is a GLOBAL guard on materialisation, not a tuple: `saturate`
    // refuses the whole KB while an equivalence exists, because a seed carries no
    // equivalence expansion (`Ara = Bel` + stored `rotten(Bel)` would leave
    // `~rotten(Ara)` reading as "no witness" — a definitive wrong TRUE). That
    // guard runs at BUILD time, so a saturation built before this merge must die
    // NOW. Anchored here at the mutation point rather than left to the caller's
    // `invalidate_pred_cache`, which the assert path no longer performs
    // unconditionally.
    crate::reasoning::invalidate_materialization(inner);
    *inner.materialization_plan.borrow_mut() = None;

    // Point loser at winner.
    inner
        .equivalence_parent
        .insert(loser.clone(), winner.clone());

    // Merge class lists.
    let loser_class = inner
        .equivalence_classes
        .remove(&loser)
        .unwrap_or_else(|| vec![loser.clone()]);
    let winner_class = inner
        .equivalence_classes
        .entry(winner.clone())
        .or_insert_with(|| vec![winner.clone()]);
    winner_class.extend(loser_class);
}

/// Register one directly sourced (`Assertion` or `Internal`), bare equality in
/// both union-find and the evidence-preserving adjacency graph. Keep this
/// separate from generic fact insertion: forward-derived or presupposed
/// `equals` facts have never changed
/// the engine's equivalence classes, and broadening that semantic boundary is
/// not part of provenance tracking.
pub(super) fn record_direct_equality_fact(inner: &mut KnowledgeBaseInner, fact: &StoredFact) {
    let StoredFact::Bare(gf) = fact else {
        return;
    };
    if gf.relation != nibli_types::relations::IDENTITY || gf.args.len() != 2 {
        return;
    }

    let left = gf.args[0].clone();
    let right = gf.args[1].clone();
    union_terms(inner, &left, &right);

    let mut add_edge = |from: GroundTerm, to: GroundTerm| {
        let edges = inner.equality_adjacency.entry(from).or_default();
        if !edges
            .iter()
            .any(|(neighbor, evidence)| neighbor == &to && evidence == fact)
        {
            edges.push((to, fact.clone()));
        }
    };
    add_edge(left.clone(), right.clone());
    add_edge(right, left);
}

/// Recover a deterministic path of actual directly sourced equality facts.
/// Union-find can answer whether two terms are equivalent, but path compression
/// and union-by-size erase the evidence chain.  Proof construction uses this
/// adjacency path and traces every returned fact through the ordinary origin
/// sidecar; it must never synthesize an unsupported endpoint equality.
pub(super) fn equality_path_facts(
    inner: &KnowledgeBaseInner,
    from: &GroundTerm,
    to: &GroundTerm,
) -> Option<Vec<StoredFact>> {
    if from == to {
        return Some(Vec::new());
    }
    // A typed witness function respects the equalities of its dependencies.
    // Cite the actual input equalities, never invent an asserted f(a)=f(b).
    match (from, to) {
        (GroundTerm::SkolemFn(a, x), GroundTerm::SkolemFn(b, y)) if a == b => {
            return equality_path_facts(inner, x, y);
        }
        (GroundTerm::DepPair(a, b), GroundTerm::DepPair(c, d)) => {
            let mut facts = equality_path_facts(inner, a, c)?;
            facts.extend(equality_path_facts(inner, b, d)?);
            return Some(facts);
        }
        _ => {}
    }

    let mut queue = std::collections::VecDeque::from([from.clone()]);
    let mut visited = HashSet::from([from.clone()]);
    let mut parent: HashMap<GroundTerm, (GroundTerm, StoredFact)> = HashMap::new();

    while let Some(current) = queue.pop_front() {
        let Some(edges) = inner.equality_adjacency.get(&current) else {
            continue;
        };
        // Assertion/replay order is already stable by fact id.  Sort by the
        // structural neighboring term as an additional guard against any future
        // caller that records the same accepted edges in a different order.
        let mut ordered: Vec<&(GroundTerm, StoredFact)> = edges.iter().collect();
        ordered.sort_by(|(left, _), (right, _)| left.cmp(right));
        for (neighbor, evidence) in ordered {
            if !visited.insert(neighbor.clone()) {
                continue;
            }
            parent.insert(neighbor.clone(), (current.clone(), evidence.clone()));
            if neighbor == to {
                let mut path = Vec::new();
                let mut cursor = to.clone();
                while &cursor != from {
                    let (previous, edge) = parent.get(&cursor)?.clone();
                    path.push(edge);
                    cursor = previous;
                }
                path.reverse();
                return Some(path);
            }
            queue.push_back(neighbor.clone());
        }
    }
    None
}

/// Get all members of a term's equivalence class (readonly).
pub(super) fn get_equivalence_class_readonly(
    parent: &HashMap<GroundTerm, GroundTerm>,
    classes: &HashMap<GroundTerm, Vec<GroundTerm>>,
    term: &GroundTerm,
) -> Vec<GroundTerm> {
    let canon = find_canonical_readonly(parent, term);
    let mut out = classes
        .get(&canon)
        .cloned()
        .unwrap_or_else(|| vec![term.clone()]);
    // Congruence is symbolic, never a product of the dependencies' aliases.
    // Twenty-one equal dependency positions already have 2^21 spellings.
    out.push(canonical_witness_term(parent, term));
    out.sort();
    out.dedup();
    out
}

pub(super) fn unify_facts_with_witness_congruence(
    template: &StoredFact,
    concrete: &StoredFact,
    inner: &KnowledgeBaseInner,
) -> Option<HashMap<String, GroundTerm>> {
    if inner.equivalence_parent.is_empty() {
        return unify_facts(template, concrete);
    }
    let normalize = |fact: &StoredFact| {
        StoredFact::with_tense_from(
            GroundFact::new(
                fact.relation(),
                fact.inner()
                    .args
                    .iter()
                    .map(|term| match term {
                        GroundTerm::SkolemFn(_, _) | GroundTerm::DepPair(_, _) => {
                            canonical_witness_term(&inner.equivalence_parent, term)
                        }
                        _ => term.clone(),
                    })
                    .collect(),
            ),
            fact,
        )
    };
    unify_facts(&normalize(template), &normalize(concrete))
}

// ═══════════════════════════════════════════════════════════════════
// SORT HIERARCHY
// ═══════════════════════════════════════════════════════════════════

/// Check if `actual_sort` is compatible with `expected_sort`.
/// Compatible means: actual == expected, or actual is a subsort of expected
/// (transitively through the sort hierarchy).
pub(super) fn is_sort_compatible(
    hierarchy: &HashMap<String, HashSet<String>>,
    actual: &str,
    expected: &str,
) -> bool {
    if actual == expected {
        return true;
    }
    // BFS/DFS up the hierarchy from actual to see if we reach expected.
    let mut visited = HashSet::new();
    let mut stack = vec![actual.to_string()];
    while let Some(current) = stack.pop() {
        if !visited.insert(current.clone()) {
            continue;
        }
        if let Some(parents) = hierarchy.get(&current) {
            for parent in parents {
                if parent == expected {
                    return true;
                }
                stack.push(parent.clone());
            }
        }
    }
    false
}

/// The WIT-exported resource type.
/// wit-bindgen generates `&self` for methods, so RefCell provides mutability.
/// This is sound because WASI components are single-threaded.
///
/// Safety: KnowledgeBase is intentionally !Send and !Sync (RefCell is not thread-safe).
/// If you need thread-safe access, wrap in Arc<Mutex<>> at the call site (as nibli-server does).
#[cfg_attr(
    all(not(target_arch = "wasm32"), target_has_atomic = "ptr"),
    doc = "WARNING: This type uses RefCell for interior mutability. \
           It is NOT thread-safe. Use Arc<Mutex<KnowledgeBase>> for multi-threaded contexts."
)]
pub struct KnowledgeBase {
    pub(super) inner: RefCell<KnowledgeBaseInner>,
}

/// Lazy cartesian product iterator over GroundTerm slices.
/// Yields Vec<GroundTerm> combinations (cloned) with given arity.
pub(super) struct GroundTermCartesianProduct<'a> {
    terms: &'a [GroundTerm],
    dep_count: usize,
    indices: Vec<usize>,
    done: bool,
}

impl<'a> GroundTermCartesianProduct<'a> {
    pub(super) fn new(terms: &'a [GroundTerm], dep_count: usize) -> Self {
        let done = dep_count > 0 && terms.is_empty();
        Self {
            terms,
            dep_count,
            indices: vec![0; dep_count],
            done,
        }
    }
}

impl<'a> Iterator for GroundTermCartesianProduct<'a> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        if self.dep_count == 0 {
            self.done = true;
            return Some(vec![]);
        }
        let combo: Vec<GroundTerm> = self
            .indices
            .iter()
            .map(|&i| self.terms[i].clone())
            .collect();
        let mut carry = true;
        for i in (0..self.dep_count).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.terms.len() {
                    self.indices[i] = 0;
                } else {
                    carry = false;
                }
            }
        }
        if carry {
            self.done = true;
        }
        Some(combo)
    }
}

// ─── Per-instance predicate result cache (on `KnowledgeBaseInner`) ────

/// Clear and enable the predicate result cache. Called at the start of
/// each top-level query. The cache persists across iterative deepening
/// iterations within a single query (tabling benefit) but is cleared
/// between separate user queries for correctness.
pub(super) fn clear_and_enable_pred_cache(inner: &KnowledgeBaseInner) {
    clear_typed_pred_cache(inner);
    inner.pred_cache_enabled.set(true);
}

/// Enable the predicate cache without clearing. Used within iterative
/// deepening to preserve cached results across depth iterations.
pub(super) fn enable_pred_cache(inner: &KnowledgeBaseInner) {
    inner.pred_cache_enabled.set(true);
}

/// Invalidate the predicate result cache WITHOUT touching the saturation.
///
/// For the ROLLBACK path only (`KnowledgeBase::rollback_inner`): a refused
/// assertion leaves the logical state exactly as it was, so the derived
/// predicate cache is cleared out of caution while the saturated extensions —
/// which the rollback provably did not invalidate — survive. Every other
/// mutation path must use [`invalidate_pred_cache`], which drops both.
pub(super) fn invalidate_pred_cache_keeping_saturation(inner: &KnowledgeBaseInner) {
    clear_typed_pred_cache(inner);
    inner.pred_cache_enabled.set(false);
}

/// Invalidate the predicate result cache. Call after any KB mutation
/// (assert, retract, reset) to prevent stale cached results.
pub(super) fn invalidate_pred_cache(inner: &KnowledgeBaseInner) {
    clear_typed_pred_cache(inner);
    // The saturated extensions are content-derived, so a mutation invalidates them too
    // (see `invalidate_materialization` for why this is NOT folded into
    // `clear_typed_pred_cache`).
    invalidate_materialization(inner);
    inner.pred_cache_enabled.set(false);
}

/// Detector for the tense/deontic fail-closed guard below: does the subtree
/// contain a material-conditional shape (an `Or` with a `Not` operand on either
/// side) reachable through the same transparent wrappers
/// `register_ground_material_conditional` itself walks (Exists/And/tense)?
/// Pure — no registration side effects (the `tense_wraps_skolemized_exists_over_forall`
/// detector-then-reject precedent).
fn tensed_body_hides_conditional(buffer: &LogicBuffer, node_id: u32) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::ExistsNode((_, body)) => tensed_body_hides_conditional(buffer, *body),
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => tensed_body_hides_conditional(buffer, *n),
        LogicNode::AndNode((l, r)) => {
            tensed_body_hides_conditional(buffer, *l) || tensed_body_hides_conditional(buffer, *r)
        }
        LogicNode::OrNode((l, r)) => {
            matches!(get_node(buffer, *l), Ok(LogicNode::NotNode(_)))
                || matches!(get_node(buffer, *r), Ok(LogicNode::NotNode(_)))
        }
        _ => false,
    }
}

pub(super) fn register_ground_material_conditional(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
) -> Result<bool, String> {
    // Walk through Skolemized Exists and tense wrappers to find the Or(Not(...), ...) pattern.
    // Returns whether a material-conditional rule was registered, so the caller can detect a
    // zero-ingest assertion (a bare disjunction registers nothing here and stores no facts).
    let Ok(node) = get_node(buffer, node_id) else {
        return Ok(false);
    };
    let registered = match node {
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            register_ground_material_conditional(buffer, *body, subs, inner)?
        }
        // Tense/deontic wrapper. SURFACE-UNREACHABLE for conditionals: tense (past/now/
        // future) and deontics (must/may) are proposition-level, never wrapping a sentence
        // connective — a tensed conditional does not parse — so nibli-semantics never produces
        // `Past(Or(Not(P), Q))`. A RAW-FOL injector can, though, and the old transparent
        // strip silently compiled it to an unqualified Bare rule, which can fire on
        // facts the tensed conditional never licensed. FAIL CLOSED on that shape instead
        // (mirroring `compile_forall_to_rule`'s whole-rule-tense rejection); plain tensed/
        // deontic facts still recurse harmlessly to `false` as before.
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => {
            if tensed_body_hides_conditional(buffer, *n) {
                return Err(
                    "cannot register a tense (past/now/future) or deontic (must/may) \
                     wrapping a ground material conditional: an unqualified backward-chaining \
                     rule cannot carry whole-rule tense or modality without over-claiming \
                     on untensed facts. Rejecting the assertion to preserve soundness; \
                     restate the temporal/deontic scope on the relevant predicate instead."
                        .to_string(),
                );
            }
            register_ground_material_conditional(buffer, *n, subs, inner)?
        }
        LogicNode::AndNode((l, r)) => {
            let left = register_ground_material_conditional(buffer, *l, subs, inner)?;
            let right = register_ground_material_conditional(buffer, *r, subs, inner)?;
            left || right
        }
        LogicNode::OrNode((l, r)) => {
            // Check for Or(Not(P), Q) — material conditional P → Q
            // The Not here encodes implication (P→Q ≡ ¬P∨Q), not body-negation.
            // The dependency Q→P is positive, so negated_condition_indices is empty.
            if matches!(get_node(buffer, *l), Ok(LogicNode::NotNode(_))) {
                // Reuse the universal-rule compiler with zero entity universals: condition-side
                // event existentials become `ev__` pattern vars (matching any asserted event)
                // and conclusion-side existentials become skolem witnesses, so event-decomposed
                // operands reason via modus ponens. Plain predicates compile identically to the
                // old path, and dedup + negated-condition handling come for free.
                compile_forall_to_rule(buffer, node_id, subs, inner)?;
                true
            }
            // Also check Or(Q, Not(P)) — reversed order (commutativity). nibli-semantics's
            // `->`/`<->` always emit Not-on-left, but a `~` on the RIGHT operand of a
            // disjunction (KR `goes(me) | ~eats(me).`) lands here. Same conditional
            // (¬P∨Q ≡ P→Q), so route through the SAME compiler as the forward arm —
            // `decompose_implication` only matches Not-on-LEFT, so present it a swapped
            // copy: clone the buffer and append `Or(Not P, Q)` (all child indices stay
            // valid; the new node sits at the max index, preserving the post-order
            // invariant). Condition-side event existentials become `ev__` pattern vars,
            // so the rule FIRES on later assertions (this arm used to bake the
            // assertion's own event-sort Skolems — an inert rule; and for a
            // non-leaf Not body it registered a zero-condition rule that derived the
            // consequent unconditionally — both repaired by the swap route).
            else if matches!(get_node(buffer, *r), Ok(LogicNode::NotNode(_))) {
                let mut swapped = buffer.clone();
                swapped.nodes.push(LogicNode::OrNode((*r, *l)));
                let swapped_id = (swapped.nodes.len() - 1) as u32;
                compile_forall_to_rule(&swapped, swapped_id, subs, inner)?;
                true
            } else {
                // A bare disjunction Or(P, Q) with no negation is not a material
                // conditional: it registers no rule and stores no fact (the caller's
                // zero-ingest guard rejects it rather than reporting a phantom assertion).
                false
            }
        }
        _ => false,
    };
    Ok(registered)
}

/// True if the root, after stripping transparent wrappers, is a negated ground fact
/// (`na <predicate>`). Under the closed-world assumption `¬P` is already entailed
/// whenever `P` is not derivable, so a negative premise stores nothing in the
/// positive store; it IS recorded in the negative-fact registry (via
/// `record_negative_ground_fact`) so a later contrary positive is flagged by
/// `check_contradictions`. The zero-ingest guard must NOT reject these — see
/// `all_conjuncts_reduce_to_negation` for the conjunction generalization.
fn root_reduces_to_negation(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::NotNode(_) => true,
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => root_reduces_to_negation(buffer, *n, subs),
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            root_reduces_to_negation(buffer, *body, subs)
        }
        _ => false,
    }
}

/// True if every conjunct of a top-level And-spine reduces to a negation
/// (`na A .i je na B`, a GIhA chain of all-`na` tails). Generalizes
/// `root_reduces_to_negation`: a single negated root trivially satisfies it.
/// Such an assertion has representable content — each negated conjunct is
/// recorded in the negative-fact registry exactly like a standalone `na`
/// assertion — so the zero-ingest guard must not reject it. An abstraction
/// group (`And(__abs_<id>, body)`) is NOT a negative-only conjunction: its
/// marker is a positive leaf.
fn all_conjuncts_reduce_to_negation(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::AndNode((l, r)) if !is_abstraction_marker(buffer, *l) => {
            all_conjuncts_reduce_to_negation(buffer, *l, subs)
                && all_conjuncts_reduce_to_negation(buffer, *r, subs)
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            all_conjuncts_reduce_to_negation(buffer, *body, subs)
        }
        // Tense/deontic wrappers around a NotNode are handled by
        // `find_negation_body`'s own descent (a wrapper around a whole
        // And-spine does not occur: nibli-semantics wraps tense per predication).
        // The exemption holds only for negations the registry can FULLY
        // represent — an impure body (e.g. Not(Or(..))) must fall through to
        // the loud fail-closed rejection, not become a silent no-op.
        _ => match find_negation_body(buffer, node_id, subs, None) {
            Some((body, _)) => negation_body_purely_representable(buffer, body, subs),
            None => false,
        },
    }
}

/// True if a negation BODY is a pure positive conjunction — the only shape the
/// negative-fact registry can represent faithfully. `collect_ground_facts`
/// silently drops NotNode/OrNode/ForAll leaves, so recording a body that
/// contains one would register a STRENGTHENED claim: `¬(P ∧ ¬Q)` — e.g. the
/// `Not(And(..))` half of nibli-semantics's Xor lowering, or a `jenai` under a proposition
/// `na` — would degrade to the group [P], i.e. `¬P`, fabricating contradiction
/// reports on consistent KBs. Mirrors `collect_ground_facts`' transparent
/// arms; an abstraction group counts as representable (the marker predicate
/// stands for the whole opaque body by design).
fn negation_body_purely_representable(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let Ok(node) = get_node(buffer, node_id) else {
        return false;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            if is_abstraction_marker(buffer, *l) {
                true
            } else {
                negation_body_purely_representable(buffer, *l, subs)
                    && negation_body_purely_representable(buffer, *r, subs)
            }
        }
        LogicNode::ExistsNode((v, body)) => {
            subs.contains_key(v.as_str()) && negation_body_purely_representable(buffer, *body, subs)
        }
        LogicNode::PastNode(n)
        | LogicNode::PresentNode(n)
        | LogicNode::FutureNode(n)
        | LogicNode::ObligatoryNode(n)
        | LogicNode::PermittedNode(n) => negation_body_purely_representable(buffer, *n, subs),
        LogicNode::Predicate(_) => true,
        _ => false,
    }
}

/// Walk a top-level And-spine and record EVERY conjunct that reduces to a
/// negation in the negative-fact registry (`P .i je na Q`, a `na`-negated
/// GIhA tail, or a bare negated root). `collect_ground_facts` skips `NotNode`
/// leaves — a negation is not a positive ground fact — so without this walk a
/// negated conjunct inside a compound assertion would vanish with no trace,
/// while the SAME negation asserted alone is recorded (an asymmetry that
/// silently dropped the `na` half of `mi klama .i je mi na citka`). Mirrors
/// `collect_ground_facts`' structural arms; abstraction bodies stay opaque
/// (their inner negations are quoted content, not asserted claims). Called
/// only after the ground path's fail-closed guards pass, so a rejected
/// assertion records nothing.
fn record_negative_conjuncts(
    inner: &mut KnowledgeBaseInner,
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::AndNode((l, r)) => {
            if !is_abstraction_marker(buffer, *l) {
                record_negative_conjuncts(inner, buffer, *l, subs);
                record_negative_conjuncts(inner, buffer, *r, subs);
            }
        }
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            record_negative_conjuncts(inner, buffer, *body, subs)
        }
        // Any non-And conjunct: record from THIS node (not its inner NotNode)
        // so `find_negation_body` accumulates a tense/deontic wrapper into the
        // stored template, exactly as a root-level negation would.
        _ => {
            if root_reduces_to_negation(buffer, node_id, subs) {
                record_negative_ground_fact(inner, buffer, node_id, subs);
            }
        }
    }
}

/// Descend through tense/deontic wrappers and Skolemized Exists to the NotNode,
/// returning the negation body and the accumulated tense context. Companion to
/// `root_reduces_to_negation` (which decides THAT a root is a negation; this
/// returns WHERE its body is). Tense tracking mirrors `collect_ground_facts`:
/// Temporal and deontic wrappers both preserve their stored-fact flavor.
fn find_negation_body(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&'static str>,
) -> Option<(u32, Option<&'static str>)> {
    let node = get_node(buffer, node_id).ok()?;
    match node {
        LogicNode::NotNode(body) => Some((*body, tense)),
        LogicNode::PastNode(n) => find_negation_body(buffer, *n, subs, Some("Past")),
        LogicNode::PresentNode(n) => find_negation_body(buffer, *n, subs, Some("Present")),
        LogicNode::FutureNode(n) => find_negation_body(buffer, *n, subs, Some("Future")),
        LogicNode::ObligatoryNode(n) => find_negation_body(buffer, *n, subs, Some("Obligatory")),
        LogicNode::PermittedNode(n) => find_negation_body(buffer, *n, subs, Some("Permitted")),
        LogicNode::ExistsNode((v, body)) if subs.contains_key(v.as_str()) => {
            find_negation_body(buffer, *body, subs, tense)
        }
        _ => None,
    }
}

/// Record a negated ground root (`na <predicate>`) as an explicit negative-fact
/// template group for contradiction detection.
///
/// THE EVENT TRAP: nibli-semantics event-decomposes every predication, so
/// `la .adam. na gerku` compiles to ¬∃e.(gerku(e) ∧ gerku_x1(e, adam) ∧
/// gerku_x2(e, zo'e)), and Skolemization gives the negative leaves an event
/// Skolem (e.g. sk_0) that can NEVER equal the fresh event Skolem a later
/// contrary positive receives (sk_1) — naive `StoredFact` equality would never
/// match. We therefore GENERALIZE event arguments: every constant that was
/// introduced as an event Skolem (an `_ev*` variable; the ground path has
/// already registered it via `note_event_entity`, so `known_event_entities` is
/// the authoritative set — the same set witness search and proof tracing use to
/// distinguish event entities) is replaced by a `PatternVar`, one per DISTINCT
/// event constant, preserving event coreference within the group.
/// `check_contradictions` then unifies the whole group against asserted
/// positives under a single consistent binding (`negative_group_holds`).
///
/// Queries are NOT affected: negative facts live in their own registry, never
/// in the positive fact store or predicate index (NAF/CWA unchanged — a
/// negative premise stays assertable, and `Not` is still computed by
/// failure-to-derive).
pub(super) fn record_negative_ground_fact(
    inner: &mut KnowledgeBaseInner,
    buffer: &LogicBuffer,
    root_id: u32,
    skolem_subs: &HashMap<String, GroundTerm>,
) {
    let Some((body_id, tense)) = find_negation_body(buffer, root_id, skolem_subs, None) else {
        return;
    };
    if !negation_body_purely_representable(buffer, body_id, skolem_subs) {
        // The body contains sub-formulas `collect_ground_facts` would DROP
        // (a nested Not/Or/ForAll, e.g. the Not(And(P, ¬Q)) half of an Xor
        // lowering, or `na … jenai …`). Recording the partial body would
        // register a STRENGTHENED negation (¬(P ∧ ¬Q) degraded to ¬P) and
        // fabricate contradiction reports on consistent KBs — keep the
        // closed-world no-op instead, but disclose this gap to scan callers.
        if let Some(id) = inner.current_assertion_id {
            inner.negative_scan_gaps.insert(id);
        }
        return;
    }
    let mut leaves = Vec::new();
    collect_ground_facts(buffer, body_id, skolem_subs, tense, &mut leaves);
    if leaves.is_empty() {
        // Nothing representable under the negation (e.g. ¬¬P, ¬(P ∨ Q)) —
        // keep the closed-world no-op rather than recording an empty group
        // (an empty group would unify trivially and flag a false contradiction).
        if let Some(id) = inner.current_assertion_id {
            inner.negative_scan_gaps.insert(id);
        }
        return;
    }

    let mut event_var_map: HashMap<GroundTerm, String> = HashMap::new();
    let templates: Vec<StoredFact> = leaves
        .iter()
        .map(|f| generalize_event_args(f, &inner.known_event_entities, &mut event_var_map))
        .collect();
    inner.negative_facts.insert(templates);
}

/// Replace event-sort Skolems in a fact with pattern variables (one per
/// distinct event witness), so a negative template matches a contrary positive
/// regardless of which fresh event Skolem that positive assertion received.
/// `PatternVar` never occurs in stored ground facts, so the generalized form
/// cannot collide with a genuine stored fact.
fn generalize_event_args(
    fact: &StoredFact,
    event_entities: &HashSet<GroundTerm>,
    event_var_map: &mut HashMap<GroundTerm, String>,
) -> StoredFact {
    let gf = fact.inner();
    let args: Vec<GroundTerm> = gf
        .args
        .iter()
        .map(|arg| match arg {
            GroundTerm::Skolem(_) if event_entities.contains(arg) => {
                let next_idx = event_var_map.len();
                let pvar = event_var_map
                    .entry(arg.clone())
                    .or_insert_with(|| format!("__neg_ev{next_idx}"))
                    .clone();
                GroundTerm::PatternVar(pvar)
            }
            other => other.clone(),
        })
        .collect();
    StoredFact::with_tense_from(GroundFact::new(gf.relation.clone(), args), fact)
}

/// Does a negative template group hold against the positive truth store?
/// True when a single consistent binding of the group's pattern variables (the
/// generalized event arguments) satisfies EVERY template — requiring the whole
/// group to share one event binding prevents false positives from unrelated
/// events that merely share a predicate. Same-tense matching only (the
/// `StoredFact` wrapper must agree, via `unify_facts`). Direct assertions and
/// eagerly stored forward conclusions are consulted; backward-only derivations
/// are out of scope by design.
pub(super) fn negative_group_holds(
    templates: &[StoredFact],
    store: &dyn crate::fact_store::FactStore,
) -> bool {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        store: &dyn crate::fact_store::FactStore,
    ) -> bool {
        let Some(template) = templates.get(idx) else {
            return true; // Every template satisfied under this binding.
        };
        let bound = substitute_fact(template, bindings);
        let Some(candidates) = store.lookup_predicate(bound.relation()) else {
            return false;
        };
        for fact in candidates {
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                if solve(templates, idx + 1, &merged, store) {
                    return true;
                }
            }
        }
        false
    }
    solve(templates, 0, &HashMap::new(), store)
}

/// Enumerate ALL consistent bindings of a template group's pattern variables against
/// the asserted positive store — the all-bindings analog of `negative_group_holds`.
/// Used by the disjunctive-conclusion constraint check, which must try each binding
/// where the antecedent P holds. (Same one-consistent-binding-per-template solve.)
pub(super) fn solve_group_bindings(
    templates: &[StoredFact],
    store: &dyn crate::fact_store::FactStore,
) -> Vec<HashMap<String, GroundTerm>> {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        store: &dyn crate::fact_store::FactStore,
        out: &mut Vec<HashMap<String, GroundTerm>>,
    ) {
        let Some(template) = templates.get(idx) else {
            out.push(bindings.clone());
            return;
        };
        let bound = substitute_fact(template, bindings);
        let Some(candidates) = store.lookup_predicate(bound.relation()) else {
            return;
        };
        for fact in candidates {
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                solve(templates, idx + 1, &merged, store, out);
            }
        }
    }
    let mut out = Vec::new();
    solve(templates, 0, &HashMap::new(), store, &mut out);
    out
}

/// True if a stored `na <predicate>` group (its `__neg_ev` pattern vars bindable) unifies
/// ENTIRELY against `facts` under one consistent binding — i.e. the (already
/// P-substituted, ground) disjunct group is explicitly denied. Mirrors
/// `negative_group_holds` but matches against a fact list rather than the store.
fn neg_group_covers(templates: &[StoredFact], facts: &[StoredFact]) -> bool {
    fn solve(
        templates: &[StoredFact],
        idx: usize,
        bindings: &HashMap<String, GroundTerm>,
        facts: &[StoredFact],
    ) -> bool {
        let Some(template) = templates.get(idx) else {
            return true;
        };
        let bound = substitute_fact(template, bindings);
        for fact in facts {
            if bound.relation() != fact.relation() {
                continue;
            }
            if let Some(new_bindings) = unify_facts(&bound, fact) {
                let mut merged = bindings.clone();
                merged.extend(new_bindings);
                if solve(templates, idx + 1, &merged, facts) {
                    return true;
                }
            }
        }
        false
    }
    solve(templates, 0, &HashMap::new(), facts)
}

/// True if `disjunct` (a P-substituted, ground disjunct template group) is explicitly
/// denied by some stored `na <predicate>` group. The disjunct's event is an existential
/// witness (SkolemFn) and the `na` group's event is a `__neg_ev` pattern var, so they
/// unify freely; only the entity arguments (and tense, via `unify_facts`) must agree.
pub(super) fn disjunct_explicitly_denied(
    disjunct: &[StoredFact],
    negative_facts: &HashSet<Vec<StoredFact>>,
) -> bool {
    negative_facts
        .iter()
        .any(|neg_group| neg_group_covers(neg_group, disjunct))
}

/// Process a logic buffer into the knowledge base without recording in the fact registry.
/// Used by both initial assertion and rebuild-on-retract replay.
/// True if `node_id` is a `ForAllNode`, possibly under leading tense/deontic
/// wrappers (`pu ro lo gerku cu danlu` → `Past(ForAll(...))`). Such a
/// whole-rule-tensed/deontic universal is routed to the RULE path so
/// `compile_forall_to_rule` rejects it on its spine with the clear whole-rule
/// message — instead of falling to the ground path, where it collects no fact
/// and is rejected with the misleading "bare disjunction" zero-ingest message.
/// A bare `ForAll` returns true immediately; `Past(Predicate)` / `Past(Or(..))`
/// etc. return false (correctly staying on the ground path).
fn node_is_forall_through_tense(buffer: &LogicBuffer, node_id: u32) -> bool {
    let mut current = node_id;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::ForAllNode(_)) => return true,
            Ok(LogicNode::PastNode(n))
            | Ok(LogicNode::PresentNode(n))
            | Ok(LogicNode::FutureNode(n))
            | Ok(LogicNode::ObligatoryNode(n))
            | Ok(LogicNode::PermittedNode(n)) => current = *n,
            _ => return false,
        }
    }
}

/// If `node_id` is a chain of leading ground-skolemized `Exists` nodes wrapping a
/// `ForAll` (`da citka ro lo gerku` → `Exists(da, ForAll(x, …))`), return the
/// inner `ForAll` node id. Phase-1 skolemization (`collect_exists_for_skolem`)
/// maps each leading ∃ — which has no enclosing universals at the root — to a
/// fresh ground constant in `subs`, so routing the inner ∀ to
/// `compile_forall_to_rule` (which substitutes those ground skolems into the rule
/// templates) is sound: `∃y.∀x.P(x,y)` is equisatisfiable with `∀x.P(x,sk₀)` for
/// a fresh constant sk₀. Returns `None` unless at least one ground-skolemized ∃
/// wraps a `ForAll` (so a pure ∃∃ ground assertion stays on the ground path).
/// Does NOT strip tense/deontic — a whole-rule-tensed ∃∀ is handled separately.
fn leading_skolemized_exists_over_forall(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> Option<u32> {
    let mut current = node_id;
    let mut peeled = false;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::ExistsNode((v, body))) => match subs.get(v.as_str()) {
                Some(gt) if !is_skdep(gt) => {
                    peeled = true;
                    current = *body;
                }
                _ => return None,
            },
            Ok(LogicNode::ForAllNode(_)) if peeled => return Some(current),
            _ => return None,
        }
    }
}

/// True if a tense (`pu`/`ca`/`ba`) or deontic (`ei`/`e'e`) wrapper sits over a
/// leading-∃-over-∀ rule (`pu da citka ro lo gerku` → `Past(Exists(da, ForAll))`).
/// Such a whole-rule tense cannot be soundly carried by an unqualified
/// backward-chaining rule (mirrors `compile_forall_to_rule`'s spine rejection),
/// so the caller rejects it with the clear whole-rule-tense message instead of
/// letting the ground path misreport it as a "bare disjunction".
fn tense_wraps_skolemized_exists_over_forall(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
) -> bool {
    let mut current = node_id;
    let mut saw_tense = false;
    loop {
        match get_node(buffer, current) {
            Ok(LogicNode::PastNode(n))
            | Ok(LogicNode::PresentNode(n))
            | Ok(LogicNode::FutureNode(n))
            | Ok(LogicNode::ObligatoryNode(n))
            | Ok(LogicNode::PermittedNode(n)) => {
                saw_tense = true;
                current = *n;
            }
            _ => {
                return saw_tense
                    && leading_skolemized_exists_over_forall(buffer, current, subs).is_some();
            }
        }
    }
}

/// Binders introduced only within quoted content do not assert outer-domain
/// membership. The abstraction referent and binders outside the quote retain
/// their ordinary scope, including a leading existential used in the body.
fn quoted_only_existential_binders(buffer: &LogicBuffer, root: u32) -> HashSet<String> {
    let mut pending = vec![(root, false)];
    let mut visited = HashSet::new();
    let mut quoted_binders = HashSet::new();
    let mut outer_binders = HashSet::new();
    while let Some((node_id, quoted)) = pending.pop() {
        if !visited.insert((node_id, quoted)) {
            continue;
        }
        let Ok(node) = get_node(buffer, node_id) else {
            continue;
        };
        match node {
            LogicNode::ExistsNode((name, body)) => {
                if quoted {
                    quoted_binders.insert(name.clone());
                } else {
                    outer_binders.insert(name.clone());
                }
                pending.push((*body, quoted));
            }
            LogicNode::AndNode((left, right)) => {
                pending.push((*left, quoted));
                pending.push((*right, quoted || is_abstraction_marker(buffer, *left)));
            }
            LogicNode::OrNode((left, right)) => {
                pending.push((*left, quoted));
                pending.push((*right, quoted));
            }
            LogicNode::ForAllNode((_, body))
            | LogicNode::NotNode(body)
            | LogicNode::PastNode(body)
            | LogicNode::PresentNode(body)
            | LogicNode::FutureNode(body)
            | LogicNode::ObligatoryNode(body)
            | LogicNode::PermittedNode(body)
            | LogicNode::CountNode((_, _, body)) => pending.push((*body, quoted)),
            LogicNode::Predicate(_) | LogicNode::ComputeNode(_) => {}
        }
    }
    // Serialized legacy buffers identify binders by name. Preserve a binder
    // also reached in outer scope rather than suppressing its asserted witness.
    quoted_binders.retain(|name| !outer_binders.contains(name));
    quoted_binders
}

pub(super) fn process_assertion(
    inner: &mut KnowledgeBaseInner,
    logic: &mut LogicBuffer,
) -> Result<(), String> {
    preflight_assertion_buffer(logic)?;
    inner.begin_skolem_scope();
    // Strict-mode violations from PREVIOUS internal forward chaining (which
    // has no user error channel) must not bleed into THIS assertion's verdict.
    inner.strict_violations.clear();
    for &root_id in &logic.roots {
        if root_id as usize >= logic.nodes.len() {
            eprintln!(
                "[Warning] skipping invalid root index {} (buffer has {} nodes)",
                root_id,
                logic.nodes.len()
            );
            continue;
        }
        // Phase 1: Collect existential variables for Skolemization.
        let mut skolem_subs = HashMap::new();
        let mut enclosing_universals = Vec::new();
        collect_exists_for_skolem(
            logic,
            root_id,
            &mut skolem_subs,
            &mut enclosing_universals,
            inner,
        );

        // Log Skolem substitutions (suppressed during rebuild + when not verbose)
        if inner.diag_enabled() && !skolem_subs.is_empty() {
            // Determinism: skolem_subs is a HashMap — sort by variable name so
            // the printed mapping order is byte-reproducible across runs.
            let mut entries: Vec<(&String, &GroundTerm)> = skolem_subs.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            let mapping: Vec<String> = entries
                .iter()
                .map(|(v, gt)| {
                    if let Some(symbol) = skdep_symbol(gt) {
                        format!("{} ↦ {}(∀-dependent)", v, symbol.display_name())
                    } else {
                        format!("{} ↦ {}", v, gt.to_display_string())
                    }
                })
                .collect();
            println!(
                "[Skolem] {} variable(s) → {}",
                skolem_subs.len(),
                mapping.join(", ")
            );
        }

        // Phase 2: Only unconditionally asserted individual witnesses seed the
        // domain. A ground conditional's consequent also has zero-dependency
        // Skolems, but those require successful rule activation first. Its
        // antecedent existentials are patterns, not existential premises.
        // Individuals introduced inside quoted content never seed this domain.
        let conditional_binders = conditional_existential_binders(logic, root_id);
        let quoted_binders = quoted_only_existential_binders(logic, root_id);
        for (var, gt) in &skolem_subs {
            if !is_skdep(gt) {
                if let GroundTerm::Skolem(symbol) = gt {
                    if var.starts_with("_ev") {
                        inner.note_event_entity(GroundTerm::Skolem(*symbol));
                    } else if !conditional_binders.contains(var) && !quoted_binders.contains(var) {
                        inner.note_entity(GroundTerm::Skolem(*symbol));
                    }
                }
            }
        }
        collect_and_note_constants(logic, root_id, inner);

        // Dispatch on root shape. A universal (optionally under whole-rule
        // tense/deontic, which `compile_forall_to_rule` rejects on its spine with
        // the clear message) takes the rule path. A leading bare variable
        // outscoping a universal (`da citka ro lo gerku` → ∃da.∀x) takes the ∃∀
        // rule path. Everything else is a ground formula.
        let is_forall = node_is_forall_through_tense(logic, root_id);

        if is_forall {
            // ═══ NATIVE RULE PATH ═══
            compile_forall_to_rule(logic, root_id, &skolem_subs, inner)?;
        } else if let Some(inner_forall_id) =
            leading_skolemized_exists_over_forall(logic, root_id, &skolem_subs)
        {
            // ═══ ∃∀ RULE PATH ═══ A leading bare variable outscopes a universal.
            // Phase-1 already skolemized each leading ∃ to a fresh ground constant
            // (no enclosing universals at the root), so route the inner ForAll to
            // rule compilation; `compile_forall_to_rule` substitutes the ground
            // skolem into the rule templates. Sound: ∃y.∀x.P(x,y) ≡ ∀x.P(x,sk₀).
            compile_forall_to_rule(logic, inner_forall_id, &skolem_subs, inner)?;
        } else if tense_wraps_skolemized_exists_over_forall(logic, root_id, &skolem_subs) {
            // A tense/deontic wrapping a whole ∃∀ rule (`pu da citka ro lo gerku`)
            // cannot carry whole-rule tense soundly — reject with the same clear
            // message `compile_forall_to_rule` uses for `pu ro lo gerku cu danlu`,
            // rather than the ground path's misleading "bare disjunction" error.
            return Err(
                "cannot compile a tense (past/now/future) or deontic (must/may) \
                 wrapping a whole universal/conditional rule: an unqualified \
                 backward-chaining rule cannot carry whole-rule tense or \
                 modality without over-claiming on untensed facts. Rejecting \
                 the assertion to preserve soundness; restate the \
                 temporal/deontic scope on the relevant predicate instead."
                    .to_string(),
            );
        } else {
            // ═══ GROUND FORMULA PATH ═══

            // Flatten top-level conjunctions and assert each leaf as a typed fact.
            let mut typed_leaves = Vec::new();
            collect_ground_facts(logic, root_id, &skolem_subs, None, &mut typed_leaves);

            // (A numeric comparison used to be refused HERE, on the collected leaves.
            // `validate_no_operational_comparisons` now refuses it on the BUFFER, inside the
            // `preflight_assertion_buffer` call at the top of this function — before id
            // allocation, so a rejected `greater(3, 1).` no longer burns a fact id, and in
            // rule positions this walk never reached.)

            // FAIL CLOSED: EDB/IDB separation. A relation declared derived-only
            // may become true ONLY by derivation, so a direct ground assertion of
            // it is refused and the whole assertion unwinds (the caller's
            // `rebuild_inner` rollback). Checked BEFORE any leaf is stored, so a
            // multi-leaf conjunction cannot half-land.
            //
            // Only the event TYPE leaf is tested (`permits(ev)`), never the role
            // leaves (`permits_x1(ev, …)`): the type leaf is present for every
            // event-decomposed assertion and for flat injected facts alike, and
            // testing role names would misfire on an unrelated relation that
            // merely shares a prefix.
            if let Some(rel) = asserted_derived_only(&typed_leaves, &inner.derived_only) {
                return Err(format!(
                    "`{rel}` is declared derived-only (`derived_only(\"{rel}\")`): it can be \
                     concluded by a rule but never asserted directly. Assert the facts its \
                     rule derives from instead — or, if this relation really should be a base \
                     fact in this model, remove its `derived_only` declaration (a visible, \
                     reviewable edit, which is the point)."
                ));
            }

            // CLOSED VOCABULARY. The dual of the check above: `derived_only` says
            // which relations may not be asserted, `admits` says which may. While
            // `admitted` is empty the KB is OPEN and nothing changes — that is the
            // v0.1 behaviour and every existing knowledge base keeps it.
            //
            // Same leaf discipline as `derived_only`: only the bare event-TYPE leaf
            // is tested, never the `_xN` role leaves, so a relation is judged by the
            // name its author wrote rather than by a decomposition artifact.
            if let Some(rel) = asserted_unadmitted(&typed_leaves, &inner.admitted) {
                return Err(format!(
                    "`{rel}` is not admitted vocabulary: this knowledge base declared its \
                     base vocabulary closed with `admits(\"…\")`, and `{rel}` is not in it. \
                     Add `admits(\"{rel}\")` ABOVE the first `{rel}` assertion if this \
                     relation really belongs in the record — a visible, reviewable edit, \
                     which is the point."
                ));
            }

            let nothing_collected = typed_leaves.is_empty();
            let mut pending_declarations: Vec<String> = Vec::new();
            let mut pending_admits: Vec<String> = Vec::new();
            for fact in &typed_leaves {
                // Intercept the `derived_only("<relation>")` META-DECLARATION and
                // record it. The declaration itself still stores like any fact, so
                // it survives `:export`, buffer replay, and is queryable — the
                // KB's own closure list is inspectable rather than hidden engine
                // state. Read off the ROLE leaf, which carries the string.
                if let StoredFact::Bare(gf) = fact
                    && gf.relation == DERIVED_ONLY_ROLE
                    && let Some(GroundTerm::Constant(rel)) = gf.args.get(1)
                {
                    pending_declarations.push(rel.clone());
                }
                // Same interception for the `admits("<relation>")` declaration.
                if let StoredFact::Bare(gf) = fact
                    && gf.relation == ADMITS_ROLE
                    && let Some(GroundTerm::Constant(rel)) = gf.args.get(1)
                {
                    pending_admits.push(rel.clone());
                }
            }

            // FAIL CLOSED: an INERT declaration. The check fires at assert time,
            // so `derived_only("permits")` protects only what is asserted AFTER
            // it. A declaration placed below the facts it means to close is
            // therefore a no-op — and, worst of all, a SILENT one: the file
            // loads at zero errors and looks exactly like a working closure.
            // That is a false green that could survive a long time, so make it
            // unrepresentable rather than merely detectable.
            //
            // Only ASSERTED facts can trigger this: derivations are computed by
            // backward chaining and never stored, so closing a relation that a
            // rule concludes is always fine no matter where the declaration sits.
            for rel in &pending_declarations {
                if inner.derived_only.contains(rel) {
                    continue; // idempotent re-declaration
                }
                if inner
                    .fact_store
                    .lookup_predicate(rel)
                    .is_some_and(|s| !s.is_empty())
                {
                    return Err(format!(
                        "`derived_only(\"{rel}\")` comes too late: `{rel}` has already been \
                         asserted in this knowledge base, so the declaration would silently \
                         protect nothing. Move it ABOVE the first `{rel}` assertion — or, if \
                         those assertions are the mistake, remove them."
                    ));
                }
            }
            for rel in pending_declarations {
                inner.derived_only.insert(rel);
            }

            // FAIL CLOSED ON ORDER, for the same reason `derived_only` does — but
            // the hazard is the mirror image. A `derived_only` placed too late
            // protects nothing; an `admits` placed too late silently GRANDFATHERS
            // everything already asserted, so the vocabulary a reader counts in the
            // file is not the vocabulary the engine closed. Both are false greens.
            //
            // The whole admits block must therefore precede every ground fact: at
            // the moment the vocabulary CLOSES, the store must hold nothing but
            // declarations. That is checkable without knowing the rest of the block
            // (which has not been read yet), and it makes the reading order the
            // writing order.
            if !pending_admits.is_empty() && inner.admitted.is_empty() {
                if let Some(rel) = first_non_declaration_relation(inner) {
                    return Err(format!(
                        "`admits(\"{}\")` comes too late: `{rel}` was already asserted, so \
                         closing the vocabulary here would silently admit it along with \
                         everything else above. Move the whole `admits` block ABOVE the \
                         first ordinary assertion.",
                        pending_admits[0]
                    ));
                }
            }
            for rel in pending_admits {
                inner.admitted.insert(rel);
            }

            for fact in typed_leaves {
                assert_typed_fact(fact, inner);
            }

            // Register ground material conditionals for backward-chaining
            let registered =
                register_ground_material_conditional(logic, root_id, &skolem_subs, inner)?;

            // FAIL CLOSED: a ground root that stored no fact AND registered no rule has no
            // representable content — a bare disjunction (`.i ja`) or an exclusive-or
            // (`.i ju`, which nibli-semantics flattens to And(Or, Not(And)) that this path cannot
            // hold). Returning Ok with a fact id would misrepresent it as asserted when
            // querying it back yields False. Negated ground facts (`na <predicate>`,
            // including a conjunction whose EVERY conjunct is negated) are accepted —
            // they store nothing in the POSITIVE store (NAF/CWA query semantics
            // unchanged) but are recorded in the negative-fact registry so a later
            // contrary positive is flagged by `check_contradictions`. Universals never
            // reach this branch — they take the rule path above.
            if nothing_collected
                && !registered
                && !all_conjuncts_reduce_to_negation(logic, root_id, &skolem_subs)
            {
                return Err(
                    "assertion has no representable content: a bare disjunction, an \
                     exclusive-or, or a negation whose body is not a plain conjunction \
                     of positive facts ingests no facts and registers no rules. \
                     Rejecting to preserve soundness rather than reporting it as \
                     asserted (querying it back would return False)."
                        .to_string(),
                );
            }

            // Record every conjunct that reduces to a negation (a bare negated
            // root, `P .i je na Q`, a `na`-negated GIhA tail) in the
            // negative-fact registry. Runs AFTER the fail-closed guards so a
            // rejected assertion records nothing. Previously only a root-level
            // negation was recorded — a negated conjunct inside a compound
            // assertion was silently dropped.
            record_negative_conjuncts(inner, logic, root_id, &skolem_subs);
        }
    }
    // STRICT MODE: any fact this assertion tried to insert that was rejected
    // (arity mismatch / integrity-constraint violation) fails the whole
    // assertion. The caller (`assert_fact_inner`) then rolls back ATOMICALLY —
    // its registry rebuild discards every partial mutation of the failed
    // assertion, and the replay runs with `rebuilding = true`, where strict is
    // inert (previously-accepted facts restore faithfully).
    if !inner.strict_violations.is_empty() {
        let joined = inner.strict_violations.drain(..).collect::<Vec<_>>();
        return Err(format!("strict mode rejected: {}", joined.join("; ")));
    }
    Ok(())
}

/// The relation whose declaration closes another relation to direct assertion,
/// and the event role that carries the closed relation's NAME. A `derived_only`
/// assertion event-decomposes to `derived_only(ev) ∧ derived_only_x1(ev, "rel")`.
pub(super) const DERIVED_ONLY: &str = "derived_only";
pub(super) const DERIVED_ONLY_ROLE: &str = "derived_only_x1";
pub(super) const ADMITS: &str = "admits";
pub(super) const ADMITS_ROLE: &str = "admits_x1";

/// Detect a direct ground assertion of a DERIVED-ONLY relation among the
/// collected leaves. Returns the offending relation name.
///
/// Only the bare event-TYPE leaf is considered (`permits(ev)` / a flat injected
/// `permits(a, b)`), never the `_xN` role leaves — see the call site. The
/// declaration relation itself is exempt: `derived_only("derived_only")` would
/// otherwise be unable to store its own declaration.
fn asserted_derived_only(leaves: &[StoredFact], closed: &HashSet<String>) -> Option<String> {
    if closed.is_empty() {
        return None;
    }
    leaves.iter().find_map(|f| {
        let gf = f.inner();
        (gf.relation != DERIVED_ONLY && closed.contains(gf.relation.as_str()))
            .then(|| gf.relation.clone())
    })
}

/// Detect a ground assertion of a relation OUTSIDE the admitted vocabulary.
/// Returns the offending relation name. The mirror of `asserted_derived_only`,
/// and it shares that function's leaf discipline exactly: only the bare
/// event-TYPE leaf is judged, never the `_xN` role leaves.
///
/// An EMPTY `admitted` set means the vocabulary was never closed, so nothing is
/// refused — that is the default and the whole v0.1 corpus keeps working.
///
/// Both DECLARATION relations are exempt, and must be: `admits("admits")` could
/// not otherwise store its own declaration, and a KB that closes its vocabulary
/// still has to be able to write `derived_only("…")` beside it. Exempting them is
/// safe because neither carries model content — they are the KB talking about
/// itself, and both are already refused as ordinary vocabulary by having no
/// meaning outside this interception.
fn asserted_unadmitted(leaves: &[StoredFact], admitted: &HashSet<String>) -> Option<String> {
    if admitted.is_empty() {
        return None;
    }
    leaves.iter().find_map(|f| {
        let gf = f.inner();
        let rel = gf.relation.as_str();
        (rel != ADMITS
            && rel != DERIVED_ONLY
            && !admitted.contains(rel)
            && crate::materialize::surface_relation(rel) == rel)
            .then(|| gf.relation.clone())
    })
}

/// The first relation in the store that is not one of the two meta-declarations —
/// i.e. evidence that ordinary assertions have already landed. Used to refuse an
/// `admits` block that arrives after the facts it would silently grandfather.
fn first_non_declaration_relation(inner: &KnowledgeBaseInner) -> Option<String> {
    let mut found: Option<String> = None;
    for f in inner.fact_store.all_facts() {
        let rel = f.inner().relation.clone();
        let base = crate::materialize::surface_relation(&rel).to_string();
        if base == ADMITS || base == DERIVED_ONLY {
            continue;
        }
        // Deterministic: the store iterates a HashSet, so take the minimum rather
        // than whichever happens to come first.
        if found.as_deref().is_none_or(|cur| base.as_str() < cur) {
            found = Some(base);
        }
    }
    found
}

// Test-only accounting for rule-derived candidate Cartesian visits.
#[cfg(test)]
thread_local! {
    static ENTAILMENT_CANDIDATE_CARTESIAN_STEPS: RefCell<HashMap<String, usize>> =
        RefCell::new(HashMap::new());
}

#[cfg(test)]
pub(super) fn reset_entailment_candidate_cartesian_steps() {
    ENTAILMENT_CANDIDATE_CARTESIAN_STEPS.with(|steps| steps.borrow_mut().clear());
}

#[cfg(test)]
pub(super) fn entailment_candidate_cartesian_steps(relation: &str) -> usize {
    ENTAILMENT_CANDIDATE_CARTESIAN_STEPS
        .with(|steps| steps.borrow().get(relation).copied().unwrap_or_default())
}

#[cfg(test)]
pub(super) fn entailment_candidate_cartesian_total_steps() -> usize {
    ENTAILMENT_CANDIDATE_CARTESIAN_STEPS.with(|steps| steps.borrow().values().copied().sum())
}

#[inline]
fn note_entailment_candidate_cartesian_step(_relation: &str) {
    #[cfg(test)]
    ENTAILMENT_CANDIDATE_CARTESIAN_STEPS.with(|steps| {
        *steps.borrow_mut().entry(_relation.to_string()).or_default() += 1;
    });
}

/// Entailment-side ∃ candidate narrowing (the ∃-heavy query blowup fix).
///
/// Narrows only from mandatory positive, store-backed anchors. Any satisfying witness
/// must satisfy every such anchor, so each index/rule-derived candidate set is a complete
/// superset; `None` means the caller must use the full domain-and-registry scan.
pub(super) fn collect_entailment_candidates(
    buffer: &LogicBuffer,
    body_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    tense: Option<&str>,
) -> Option<Vec<GroundTerm>> {
    let mut anchors = Vec::new();
    collect_mandatory_anchors(buffer, body_id, var_name, subs, tense, &mut anchors);
    // A role predicate of a compute relation must not anchor even when the
    // relation is externally REGISTERED rather than built-in (`exponential_x1`):
    // the static classifier cannot know the registry, but the registered head is
    // visible in this very body subtree as a ComputeNode — refuse any anchor
    // sharing its surface relation.
    let mut compute_heads: HashSet<&str> = HashSet::new();
    collect_compute_heads(buffer, body_id, &mut compute_heads);
    if !compute_heads.is_empty() {
        anchors
            .retain(|a| !compute_heads.contains(crate::materialize::surface_relation(&a.relation)));
    }
    if anchors.is_empty() {
        return None;
    }
    let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
    let mut candidates = select_narrowest_anchor_candidates(&anchors, inner, &members);
    let mut priority_terms = Vec::new();
    let mut seen = HashSet::new();
    collect_candidate_priority_terms(buffer, body_id, subs, &mut priority_terms, &mut seen);
    prioritize_candidates_by_dependency(&mut candidates, &priority_terms);
    Some(candidates)
}

/// Gather ground terms already present in the query body, in structural order.
/// They are search-order hints only: every complete candidate is still retained.
/// This lets a dependent witness such as `sk_rule($subject)` try the query's
/// concrete subject before unrelated domain members without coupling the engine
/// to any predicate name or opaque-body spelling.
fn collect_candidate_priority_terms(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &HashMap<String, GroundTerm>,
    terms: &mut Vec<GroundTerm>,
    seen: &mut HashSet<GroundTerm>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::Predicate((_, args)) | LogicNode::ComputeNode((_, args)) => {
            for arg in args {
                let term = match arg {
                    LogicalTerm::Variable(name) => subs.get(name).cloned(),
                    LogicalTerm::Constant(value) => Some(GroundTerm::Constant(value.clone())),
                    LogicalTerm::Description(value) => Some(GroundTerm::Description(value.clone())),
                    LogicalTerm::Number(value) => Some(GroundTerm::Number(value.to_bits())),
                    LogicalTerm::Unspecified => None,
                };
                if let Some(term) = term
                    && seen.insert(term.clone())
                {
                    terms.push(term);
                }
            }
        }
        LogicNode::AndNode((left, right)) | LogicNode::OrNode((left, right)) => {
            collect_candidate_priority_terms(buffer, *left, subs, terms, seen);
            collect_candidate_priority_terms(buffer, *right, subs, terms, seen);
        }
        LogicNode::NotNode(inner)
        | LogicNode::ExistsNode((_, inner))
        | LogicNode::ForAllNode((_, inner))
        | LogicNode::PastNode(inner)
        | LogicNode::PresentNode(inner)
        | LogicNode::FutureNode(inner)
        | LogicNode::ObligatoryNode(inner)
        | LogicNode::PermittedNode(inner) => {
            collect_candidate_priority_terms(buffer, *inner, subs, terms, seen);
        }
        LogicNode::CountNode((_, _, body)) => {
            collect_candidate_priority_terms(buffer, *body, subs, terms, seen);
        }
    }
}

fn term_contains_priority_term(term: &GroundTerm, priority: &GroundTerm) -> bool {
    term == priority
        || match term {
            GroundTerm::SkolemFn(_, dependency) => {
                term_contains_priority_term(dependency, priority)
            }
            GroundTerm::DepPair(left, right) => {
                term_contains_priority_term(left, priority)
                    || term_contains_priority_term(right, priority)
            }
            _ => false,
        }
}

fn prioritize_candidates_by_dependency(
    candidates: &mut [GroundTerm],
    priority_terms: &[GroundTerm],
) {
    if priority_terms.is_empty() {
        return;
    }
    candidates.sort_by(|left, right| {
        let left_priority = priority_terms
            .iter()
            .position(|term| term_contains_priority_term(left, term))
            .unwrap_or(usize::MAX);
        let right_priority = priority_terms
            .iter()
            .position(|term| term_contains_priority_term(right, term))
            .unwrap_or(usize::MAX);
        left_priority
            .cmp(&right_priority)
            .then_with(|| left.cmp(right))
    });
}

/// Relations whose truth is not store-backed (query-time evaluation /
/// equivalence machinery) — never sound to narrow candidates from. Classifies
/// the SURFACE relation, so a decomposed role predicate of an arithmetic or
/// comparison relation (`sum_x1`, `greater_x2`) is refused like its base: its
/// store extension is not a complete account of query-time evaluation
/// (`validate_no_operational_comparisons` also refuses comparison atoms with
/// potentially-numeric operands at assertion ingress), so an
/// empty index entry is not "no witness", and a mandatory anchor built on one
/// let its empty candidate set win the narrowing pick — turning
/// `sum(some big, 2, 3).` into a definitive FALSE.
pub(crate) fn is_non_indexable_relation(rel: &str) -> bool {
    let base = crate::materialize::surface_relation(rel);
    nibli_types::relations::is_identity(base)
        || nibli_types::relations::is_numeric_comparison(base)
        || nibli_types::relations::is_builtin_arithmetic(base)
}

/// Candidate narrowing for a negated-exists group's event variable — the
/// firing-time analog of `collect_entailment_candidates`, driven by the group's
/// `StoredFact` condition TEMPLATES rather than a buffer sub-tree. Returns the
/// smallest superset of events that could satisfy the inner existential: index
/// hits (events at the var position of a stored fact of the relation,
/// equivalence-expanded) ∪ rule-derivable witnesses. Soundness: a witness `ev`
/// satisfying ALL conditions satisfies the anchor condition too, so it is in the
/// anchor's candidate set — narrowing never drops a real witness (so it never
/// produces a spurious "no witness" → spurious obligation). Without it the group
/// enumerates the full `members^k` pool per firing. `None` when no condition
/// cleanly anchors the event var (caller falls back to the full pool).
pub(super) fn collect_group_event_candidates(
    conditions: &[StoredFact],
    event_var: &str,
    inner: &KnowledgeBaseInner,
) -> Option<Vec<GroundTerm>> {
    let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
    let mut anchors = Vec::new();
    for cond in conditions {
        let gf = cond.inner();
        if is_non_indexable_relation(&gf.relation) {
            continue;
        }
        // The event var must appear exactly once (as a PatternVar) in this cond.
        let positions: Vec<usize> = gf
            .args
            .iter()
            .enumerate()
            .filter(|(_, a)| matches!(a, GroundTerm::PatternVar(s) if s == event_var))
            .map(|(i, _)| i)
            .collect();
        if positions.len() != 1 {
            continue;
        }
        anchors.push(PredicateAnchor {
            relation: gf.relation.clone(),
            var_position: positions[0],
            args: vec![LogicalTerm::Unspecified; gf.args.len()],
            ground_args: Some(gf.args.clone()),
            tense: match cond {
                StoredFact::Past(_) => Some("Past"),
                StoredFact::Present(_) => Some("Present"),
                StoredFact::Future(_) => Some("Future"),
                StoredFact::Obligatory(_) => Some("Obligatory"),
                StoredFact::Permitted(_) => Some("Permitted"),
                _ => None,
            },
        });
    }
    (!anchors.is_empty()).then(|| select_narrowest_anchor_candidates(&anchors, inner, &members))
}

/// Like `collect_predicate_anchors`, but only MANDATORY anchors: descends
/// And/tense/deontic/quantifier bodies, but NOT Or branches (optional) and
/// NOT compute nodes or query-time-evaluated relations.
fn collect_mandatory_anchors(
    buffer: &LogicBuffer,
    node_id: u32,
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
    tense: Option<&str>,
    anchors: &mut Vec<PredicateAnchor>,
) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::Predicate((rel, args)) => {
            if is_non_indexable_relation(rel) {
                return;
            }
            if let Some(pos) = find_var_position(args, var_name, subs) {
                anchors.push(PredicateAnchor {
                    relation: rel.clone(),
                    var_position: pos,
                    args: args.clone(),
                    ground_args: Some(
                        args.iter()
                            .map(|arg| match arg {
                                LogicalTerm::Variable(name) => subs
                                    .get(name)
                                    .cloned()
                                    .unwrap_or_else(|| GroundTerm::PatternVar(name.clone())),
                                LogicalTerm::Constant(value) => GroundTerm::Constant(value.clone()),
                                LogicalTerm::Description(value) => {
                                    GroundTerm::Description(value.clone())
                                }
                                LogicalTerm::Number(value) => GroundTerm::Number(value.to_bits()),
                                LogicalTerm::Unspecified => GroundTerm::Unspecified,
                            })
                            .collect(),
                    ),
                    tense: tense_to_static(tense),
                });
            }
        }
        LogicNode::AndNode((l, r)) => {
            collect_mandatory_anchors(buffer, *l, var_name, subs, tense, anchors);
            collect_mandatory_anchors(buffer, *r, var_name, subs, tense, anchors);
        }
        LogicNode::PastNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Past"), anchors);
        }
        LogicNode::PresentNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Present"), anchors);
        }
        LogicNode::FutureNode(inner_id) => {
            collect_mandatory_anchors(buffer, *inner_id, var_name, subs, Some("Future"), anchors);
        }
        LogicNode::ObligatoryNode(inner_id) => {
            collect_mandatory_anchors(
                buffer,
                *inner_id,
                var_name,
                subs,
                Some("Obligatory"),
                anchors,
            );
        }
        LogicNode::PermittedNode(inner_id) => {
            collect_mandatory_anchors(
                buffer,
                *inner_id,
                var_name,
                subs,
                Some("Permitted"),
                anchors,
            );
        }
        // A nested quantifier's body conjuncts are still mandatory for OUR
        // variable (nibli-semantics generates unique variable names, so no shadowing).
        LogicNode::ExistsNode((_, body)) | LogicNode::ForAllNode((_, body)) => {
            collect_mandatory_anchors(buffer, *body, var_name, subs, tense, anchors);
        }
        // OrNode: optional branches can't narrow. NotNode: negated predicates
        // can't anchor. CountNode/ComputeNode/others: not store-backed anchors.
        _ => {}
    }
}

/// Collect every `ComputeNode` head relation in the subtree. Companion to the
/// anchor sweep: `collect_mandatory_anchors` ignores ComputeNodes themselves,
/// but their ROLE predicates (`exponential_x1`) look like ordinary store-backed
/// predicates, and for a REGISTERED (non-built-in) compute relation only the
/// head's presence in the body marks the relation as query-time-evaluated.
fn collect_compute_heads<'b>(buffer: &'b LogicBuffer, node_id: u32, heads: &mut HashSet<&'b str>) {
    let Ok(node) = get_node(buffer, node_id) else {
        return;
    };
    match node {
        LogicNode::ComputeNode((rel, _)) => {
            heads.insert(rel.as_str());
        }
        LogicNode::Predicate(_) => {}
        LogicNode::AndNode((l, r)) | LogicNode::OrNode((l, r)) => {
            collect_compute_heads(buffer, *l, heads);
            collect_compute_heads(buffer, *r, heads);
        }
        LogicNode::NotNode(id)
        | LogicNode::ExistsNode((_, id))
        | LogicNode::ForAllNode((_, id))
        | LogicNode::PastNode(id)
        | LogicNode::PresentNode(id)
        | LogicNode::FutureNode(id)
        | LogicNode::ObligatoryNode(id)
        | LogicNode::PermittedNode(id) => {
            collect_compute_heads(buffer, *id, heads);
        }
        LogicNode::CountNode((_, _, body)) => {
            collect_compute_heads(buffer, *body, heads);
        }
    }
}

fn candidate_limit_reached(candidates: &HashSet<GroundTerm>, stop_at: Option<usize>) -> bool {
    stop_at.is_some_and(|limit| candidates.len() >= limit)
}

fn insert_bounded_candidate(
    candidates: &mut HashSet<GroundTerm>,
    candidate: GroundTerm,
    stop_at: Option<usize>,
) -> bool {
    // `something` may occur in stored role data, but it is not a witness value.
    if candidate != GroundTerm::Unspecified {
        candidates.insert(candidate);
    }
    candidate_limit_reached(candidates, stop_at)
}

fn saturating_cartesian_size(member_count: usize, dep_count: usize) -> usize {
    (0..dep_count).fold(1usize, |size, _| size.saturating_mul(member_count))
}

fn term_contains_pattern_var(term: &GroundTerm) -> bool {
    match term {
        GroundTerm::PatternVar(_) => true,
        GroundTerm::SkolemFn(_, dep) => term_contains_pattern_var(dep),
        GroundTerm::DepPair(left, right) => {
            term_contains_pattern_var(left) || term_contains_pattern_var(right)
        }
        _ => false,
    }
}

/// Distinct unresolved variables inside one already-specialized candidate term, in
/// structural first-occurrence order. A dependent witness such as
/// `sk_rule(Grounded, $remaining)` has one search dimension, not the registry
/// family's original two. Repeated variables stay one dimension so their equality is
/// preserved when the term is instantiated.
fn unresolved_pattern_vars(term: &GroundTerm) -> Vec<String> {
    fn walk(term: &GroundTerm, seen: &mut HashSet<String>, vars: &mut Vec<String>) {
        match term {
            GroundTerm::PatternVar(name) => {
                if seen.insert(name.clone()) {
                    vars.push(name.clone());
                }
            }
            GroundTerm::SkolemFn(_, dep) => walk(dep, seen, vars),
            GroundTerm::DepPair(left, right) => {
                walk(left, seen, vars);
                walk(right, seen, vars);
            }
            _ => {}
        }
    }

    let mut seen = HashSet::new();
    let mut vars = Vec::new();
    walk(term, &mut seen, &mut vars);
    vars
}

/// Apply the anchor's already-bound non-witness arguments to a matching rule conclusion.
/// A head `kind_x1(sk_kind($x), $x)` anchored at `kind_x1($event, Subject)` therefore
/// yields exactly `sk_kind(Subject)`, not `sk_kind(member)` for every domain member.
/// Equality classes disable this narrowing: an equivalent spelling may still match via
/// the ordinary fallback, so keeping the broader template is the sound choice.
fn specialize_conclusion_candidate(
    anchor: &PredicateAnchor,
    conclusion_args: &[GroundTerm],
    inner: &KnowledgeBaseInner,
) -> Option<GroundTerm> {
    let candidate = conclusion_args.get(anchor.var_position)?;
    if !inner.equivalence_parent.is_empty() {
        return Some(candidate.clone());
    }
    let Some(ground_args) = &anchor.ground_args else {
        return Some(candidate.clone());
    };
    if ground_args.len() != conclusion_args.len() {
        return None;
    }
    let mut bindings = HashMap::new();
    for (idx, (template, expected)) in conclusion_args.iter().zip(ground_args).enumerate() {
        if idx == anchor.var_position
            || *expected == GroundTerm::Unspecified
            || term_contains_pattern_var(expected)
        {
            continue;
        }
        if !unify_terms(template, expected, &mut bindings) {
            return None;
        }
    }
    Some(substitute_term(candidate, &bindings).into_owned())
}

/// Cheap upper estimate used only to choose which mandatory anchor to collect first. The
/// chosen anchor is still collected exactly; an estimate can affect work, never witnesses.
fn estimated_anchor_candidate_cost(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    member_count: usize,
) -> usize {
    let mut cost = inner
        .fact_store
        .lookup_predicate(anchor.relation.as_str())
        .map_or(0, |facts| facts.len());
    let global_pool = inner
        .skolem_fn_registry
        .iter()
        .fold(member_count, |size, entry| {
            size.saturating_add(saturating_cartesian_size(member_count, entry.dep_count))
        });
    for rule in inner
        .universal_rules
        .get(anchor.relation.as_str())
        .into_iter()
        .flatten()
    {
        for conclusion in &rule.typed_conclusions {
            if conclusion.relation() != anchor.relation {
                continue;
            }
            let args = &conclusion.inner().args;
            if args.len() != anchor.args.len() {
                continue;
            }
            let Some(candidate) = specialize_conclusion_candidate(anchor, args, inner) else {
                continue;
            };
            let contribution = if !term_contains_pattern_var(&candidate) {
                1
            } else {
                match &candidate {
                    GroundTerm::PatternVar(_) => global_pool,
                    GroundTerm::SkolemFn(_, _) | GroundTerm::DepPair(_, _) => {
                        saturating_cartesian_size(
                            member_count,
                            unresolved_pattern_vars(&candidate).len(),
                        )
                    }
                    _ => 1,
                }
            };
            cost = cost.saturating_add(contribution);
        }
    }
    cost
}

/// Choose the smallest complete mandatory-anchor superset without eagerly building every
/// larger set. Estimates choose work order; original anchor order remains the deterministic
/// tie-breaker for equal exact sets.
fn select_narrowest_anchor_candidates(
    anchors: &[PredicateAnchor],
    inner: &KnowledgeBaseInner,
    members: &[GroundTerm],
) -> Vec<GroundTerm> {
    let mut order: Vec<usize> = (0..anchors.len()).collect();
    order.sort_by_key(|&idx| {
        (
            estimated_anchor_candidate_cost(&anchors[idx], inner, members.len()),
            idx,
        )
    });

    let mut best: Option<(usize, HashSet<GroundTerm>)> = None;
    for idx in order {
        if best.as_ref().is_some_and(|(_, set)| set.is_empty()) {
            break;
        }
        let stop_at = best.as_ref().map(|(best_idx, set)| {
            if idx < *best_idx {
                // An earlier equal-sized anchor wins the historical tie, so distinguish
                // equality from strictly larger by collecting one extra candidate.
                set.len().saturating_add(1)
            } else {
                // A later equal-sized anchor cannot win; reaching the current size is
                // already enough to abandon it.
                set.len()
            }
        });
        let (candidates, complete) =
            collect_anchor_candidates(&anchors[idx], inner, members, stop_at);
        if !complete {
            continue;
        }
        let replace = match &best {
            None => true,
            Some((best_idx, current)) => {
                candidates.len() < current.len()
                    || (candidates.len() == current.len() && idx < *best_idx)
            }
        };
        if replace {
            best = Some((idx, candidates));
        }
    }

    let mut candidates: Vec<GroundTerm> = best
        .expect("a non-empty anchor list always yields one complete candidate set")
        .1
        .into_iter()
        .collect();
    candidates.sort();
    candidates
}

/// Collect one anchor's complete candidate superset, or stop once `stop_at` distinct
/// candidates prove it cannot beat a previously completed anchor.
fn collect_anchor_candidates(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    members: &[GroundTerm],
    stop_at: Option<usize>,
) -> (HashSet<GroundTerm>, bool) {
    let mut candidates = HashSet::new();
    if extract_from_index_bounded(anchor, inner, &mut candidates, stop_at)
        || extract_rule_candidates_for_entailment_bounded(
            anchor,
            inner,
            members,
            &mut candidates,
            stop_at,
        )
    {
        return (candidates, false);
    }
    (candidates, true)
}

/// Rule-derivable candidates for an entailment anchor (see
/// `collect_entailment_candidates` for the completeness argument).
fn extract_rule_candidates_for_entailment_bounded(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    members: &[GroundTerm],
    candidates: &mut HashSet<GroundTerm>,
    stop_at: Option<usize>,
) -> bool {
    let rules = match inner.universal_rules.get(anchor.relation.as_str()) {
        Some(r) => r,
        None => return false,
    };
    for rule in rules {
        for conclusion in &rule.typed_conclusions {
            if conclusion.relation() != anchor.relation {
                continue;
            }
            let conc_args = &conclusion.inner().args;
            if conc_args.len() != anchor.args.len() {
                continue;
            }
            let Some(candidate) = specialize_conclusion_candidate(anchor, conc_args, inner) else {
                continue;
            };
            if !term_contains_pattern_var(&candidate) {
                if insert_bounded_candidate(candidates, candidate, stop_at) {
                    return true;
                }
                continue;
            }
            match candidate {
                GroundTerm::PatternVar(_) => {
                    // The rule's conditions can bind this position to any
                    // domain member, or (via chained rules) to another rule's
                    // dependent-Skolem witness — full superset, same as the
                    // old unconditional scan.
                    for member in members {
                        if insert_bounded_candidate(candidates, member.clone(), stop_at) {
                            return true;
                        }
                    }
                    for entry in &inner.skolem_fn_registry {
                        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
                            note_entailment_candidate_cartesian_step(&anchor.relation);
                            if insert_bounded_candidate(
                                candidates,
                                build_skolem_fn_term(entry.symbol, &combo),
                                stop_at,
                            ) {
                                return true;
                            }
                        }
                    }
                }
                structured => {
                    // Preserve every grounded dependency supplied by sibling
                    // arguments. Enumerate only the distinct variables that remain in
                    // this specialized term rather than rebuilding the Skolem family's
                    // original members^dep_count registry product.
                    let unresolved = unresolved_pattern_vars(&structured);
                    debug_assert!(!unresolved.is_empty());
                    for combo in GroundTermCartesianProduct::new(members, unresolved.len()) {
                        note_entailment_candidate_cartesian_step(&anchor.relation);
                        let bindings: HashMap<String, GroundTerm> =
                            unresolved.iter().cloned().zip(combo.into_iter()).collect();
                        if insert_bounded_candidate(
                            candidates,
                            substitute_term(&structured, &bindings).into_owned(),
                            stop_at,
                        ) {
                            return true;
                        }
                    }
                }
            }
        }
    }
    false
}

/// An anchor: a positive predicate in the body that mentions the target variable.
struct PredicateAnchor {
    relation: String,
    var_position: usize,
    args: Vec<LogicalTerm>,
    /// Partially grounded condition arguments. Positions other than `var_position`
    /// constrain index hits and may bind a rule head's dependent Skolem.
    ground_args: Option<Vec<GroundTerm>>,
    tense: Option<&'static str>,
}

/// Find the position of `var_name` in predicate args.
/// Returns Some(pos) if var_name appears exactly once and all other variables are bound.
fn find_var_position(
    args: &[LogicalTerm],
    var_name: &str,
    subs: &HashMap<String, GroundTerm>,
) -> Option<usize> {
    let mut var_pos = None;
    for (i, arg) in args.iter().enumerate() {
        if let LogicalTerm::Variable(v) = arg {
            if v == var_name {
                if var_pos.is_some() {
                    return None; // Appears more than once — can't extract cleanly
                }
                var_pos = Some(i);
            } else if !subs.contains_key(v) {
                // Another unbound variable — this anchor alone isn't sufficient,
                // but we still collect it. The candidate extraction will be
                // broader (all values at this position) but still narrower than
                // full domain scan.
            }
        }
    }
    var_pos
}

fn tense_to_static(tense: Option<&str>) -> Option<&'static str> {
    match tense {
        Some("Past") => Some("Past"),
        Some("Present") => Some("Present"),
        Some("Future") => Some("Future"),
        Some("Obligatory") => Some("Obligatory"),
        Some("Permitted") => Some("Permitted"),
        _ => None,
    }
}

fn anchor_other_arguments_match(
    anchor: &PredicateAnchor,
    fact_args: &[GroundTerm],
    inner: &KnowledgeBaseInner,
) -> bool {
    if !inner.equivalence_parent.is_empty() {
        return true;
    }
    let Some(expected_args) = &anchor.ground_args else {
        return true;
    };
    expected_args.len() == fact_args.len()
        && expected_args
            .iter()
            .zip(fact_args)
            .enumerate()
            .all(|(idx, (expected, actual))| {
                idx == anchor.var_position
                    || *expected == GroundTerm::Unspecified
                    || term_contains_pattern_var(expected)
                    || expected == actual
            })
}

/// Extract candidates from the typed fact index for a predicate anchor.
fn extract_from_index_bounded(
    anchor: &PredicateAnchor,
    inner: &KnowledgeBaseInner,
    candidates: &mut HashSet<GroundTerm>,
    stop_at: Option<usize>,
) -> bool {
    let facts = match inner.fact_store.lookup_predicate(anchor.relation.as_str()) {
        Some(f) => f,
        None => return false,
    };

    for stored_fact in facts {
        // Check tense matches
        let tense_matches = match (anchor.tense, stored_fact) {
            (None, StoredFact::Bare(_)) => true,
            (Some("Past"), StoredFact::Past(_)) => true,
            (Some("Present"), StoredFact::Present(_)) => true,
            (Some("Future"), StoredFact::Future(_)) => true,
            (Some("Obligatory"), StoredFact::Obligatory(_)) => true,
            (Some("Permitted"), StoredFact::Permitted(_)) => true,
            _ => false,
        };
        if !tense_matches {
            continue;
        }

        let fact_args = &stored_fact.inner().args;
        if fact_args.len() != anchor.args.len() {
            continue;
        }
        if !anchor_other_arguments_match(anchor, fact_args, inner) {
            continue;
        }

        // Extract the witness position after filtering only already-ground sibling
        // arguments. Unbound siblings remain wildcards, so this is still a complete
        // superset; the full body check decides each candidate later.
        let direct = fact_args[anchor.var_position].clone();
        if insert_bounded_candidate(candidates, direct.clone(), stop_at) {
            return true;
        }
        // Expand by equivalence class.
        if !inner.equivalence_parent.is_empty() {
            for equiv in get_equivalence_class_readonly(
                &inner.equivalence_parent,
                &inner.equivalence_classes,
                &direct,
            ) {
                if insert_bounded_candidate(candidates, equiv, stop_at) {
                    return true;
                }
            }
        }
    }
    false
}
