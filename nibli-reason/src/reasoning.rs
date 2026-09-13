use super::*;

pub(super) fn witness_origin(term: &GroundTerm) -> nibli_types::logic::WitnessOrigin {
    let origin = match term {
        GroundTerm::Skolem(symbol) | GroundTerm::SkolemFn(symbol, _) => Some(symbol.origin()),
        _ => None,
    };
    match origin {
        Some(SkolemOrigin::ExistentialImport) => {
            nibli_types::logic::WitnessOrigin::ExistentialImport
        }
        Some(SkolemOrigin::Generated) => nibli_types::logic::WitnessOrigin::GeneratedWitness,
        None => nibli_types::logic::WitnessOrigin::KnowledgeBase,
    }
}

/// Temporarily bind `key` to `value` in `subs`, run `f`, then restore the
/// previous binding (or remove if there was none). Avoids the repeated
/// save/restore boilerplate across quantifier evaluation.
fn with_sub<T>(
    subs: &mut HashMap<String, GroundTerm>,
    key: &str,
    value: GroundTerm,
    f: impl FnOnce(&mut HashMap<String, GroundTerm>) -> T,
) -> T {
    let prev = subs.insert(key.to_string(), value);
    let result = f(subs);
    match prev {
        Some(p) => {
            subs.insert(key.to_string(), p);
        }
        None => {
            subs.remove(key);
        }
    }
    result
}

// Test-only count of the registry-wide Cartesian fallback.
#[cfg(test)]
thread_local! {
    static GLOBAL_CANDIDATE_CARTESIAN_STEPS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
    static RULE_EVENT_SEARCH_LEAF_ATTEMPTS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn reset_global_candidate_cartesian_steps() {
    GLOBAL_CANDIDATE_CARTESIAN_STEPS.with(|steps| steps.set(0));
}

#[cfg(test)]
pub(super) fn global_candidate_cartesian_steps() -> usize {
    GLOBAL_CANDIDATE_CARTESIAN_STEPS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(super) fn reset_rule_event_search_leaf_attempts() {
    RULE_EVENT_SEARCH_LEAF_ATTEMPTS.with(|steps| steps.set(0));
}

#[cfg(test)]
pub(super) fn rule_event_search_leaf_attempts() -> usize {
    RULE_EVENT_SEARCH_LEAF_ATTEMPTS.with(std::cell::Cell::get)
}

#[inline]
fn note_global_candidate_cartesian_step() {
    #[cfg(test)]
    GLOBAL_CANDIDATE_CARTESIAN_STEPS.with(|steps| steps.set(steps.get() + 1));
}

#[inline]
fn note_rule_event_search_leaf_attempt() {
    #[cfg(test)]
    RULE_EVENT_SEARCH_LEAF_ATTEMPTS.with(|steps| steps.set(steps.get() + 1));
}

/// Build the full candidate vector for unbound event variable search:
/// all typed domain members + SkolemFn witness terms from the registry.
fn build_all_candidates(inner: &KnowledgeBaseInner) -> Vec<GroundTerm> {
    let members = inner.all_typed_domain_members();
    let mut candidates: Vec<GroundTerm> = members.to_vec();
    for entry in &inner.skolem_fn_registry {
        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
            note_global_candidate_cartesian_step();
            candidates.push(build_skolem_fn_term(entry.symbol, &combo));
        }
    }
    candidates
}

/// Lazily build (at most once per backward-chaining frame) the unbound-event
/// candidate vector. The full members^dep_count product is only needed when a
/// matched rule actually has unbound `ev__` pattern variables; most frames
/// never reach that point, so the eager build was pure waste.
fn ensure_candidates<'a>(
    slot: &'a mut Option<Vec<GroundTerm>>,
    inner: &KnowledgeBaseInner,
) -> &'a [GroundTerm] {
    if slot.is_none() {
        *slot = Some(build_all_candidates(inner));
    }
    slot.as_deref().expect("slot was just filled")
}

/// A condition relation is "index-decidable" when backward chaining can never
/// prove it beyond a direct fact-store lookup: no rule concludes the relation
/// at all (a conservative relation-level check across every flavor), it is not
/// the special-cased `du` equality predicate, and no du-equivalence classes exist
/// (equivalence substitution could otherwise rewrite the fact into a stored
/// variant via the recursive fallback).
///
/// For such relations `check_predicate_in_kb_typed` reduces to
/// `typed_fact_is_stored` at ANY depth, so the unbound-event-variable filter
/// can evaluate them definitively without recursion — crucially, even at the
/// depth horizon, where the recursive check returns ResourceExceeded for
/// every candidate and would otherwise pessimistically keep the entire
/// members^k cartesian product alive.
fn condition_is_index_decidable(relation: &str, inner: &KnowledgeBaseInner) -> bool {
    !nibli_types::relations::is_identity(relation)
        && inner.equivalence_parent.is_empty()
        && !inner.universal_rules.contains_key(relation)
}

/// True if the (substituted) fact still has any unbound pattern-var argument.
fn fact_has_unbound_pattern_var(fact: &StoredFact) -> bool {
    fact.inner()
        .args
        .iter()
        .any(|a| matches!(a, GroundTerm::PatternVar(_)))
}

/// A rule-backed decomposed role remains functional at a fixed event only when every
/// rule that can derive it mints the role's first argument as a fresh event witness.
/// A hand-built flat rule that reuses an arbitrary event variable is therefore never
/// eligible for the direct-index binding shortcut.
fn relation_rule_heads_mint_events(relation: &str, inner: &KnowledgeBaseInner) -> bool {
    let Some(rules) = inner.universal_rules.get(relation) else {
        return false;
    };
    let mut saw_conclusion = false;
    for conclusion in rules
        .iter()
        .flat_map(|rule| rule.typed_conclusions.iter())
        .filter(|conclusion| conclusion.relation() == relation)
    {
        saw_conclusion = true;
        if !conclusion
            .inner()
            .args
            .first()
            .is_some_and(is_event_skolem_term)
        {
            return false;
        }
    }
    saw_conclusion
}

/// Index-anchored join binding. After one or more rule event variables are bound,
/// a fully event-bound condition such as `fanta_x1(ev_f, x__v0)` has a GROUND
/// event anchor and an unbound individual pattern var. Look the matching asserted
/// fact up in `arg_position_index` and bind the individual var to it — instead of
/// enumerating those vars over a `members^k` domain cartesian. Conditions with an
/// unbound `ev__` stay untouched; binding from them would choose an individual
/// before the event that justifies it. Runs to a fixpoint so a var bound from one
/// role propagates into the next event's candidate anchors. Negated conditions are
/// never binding sources. An ordinary relation must be EDB-only; a decomposed role
/// relation may also be rule-backed because its paired base atom fixes the event
/// identity, and a rule-head event Skolem structurally determines all of that head's
/// roles. Equality disables the shortcut. Binds only on a UNIQUE exact index match,
/// so it never guesses; non-unique conditions are left for the downstream ground
/// check.
/// Returns the names of vars newly bound, so a failed search branch can restore
/// its parent bindings.
fn bind_join_vars_from_index(
    rule: &UniversalRuleRecord,
    bindings: &mut HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
) -> Vec<String> {
    let mut newly_bound: Vec<String> = Vec::new();
    loop {
        let mut changed = false;
        for (condition_idx, ct) in rule.typed_conditions.iter().enumerate() {
            if rule.negated_condition_indices.contains(&condition_idx) {
                continue;
            }
            let cs = substitute_fact(ct, bindings);
            let gf = cs.inner();
            let surface_relation = crate::materialize::surface_relation(&gf.relation);
            let paired_functional_role = inner.equivalence_parent.is_empty()
                && surface_relation != gf.relation
                && gf.args.len() == 2
                && gf.args.first().is_some_and(is_event_skolem_term)
                && relation_rule_heads_mint_events(&gf.relation, inner)
                && rule
                    .typed_conditions
                    .iter()
                    .enumerate()
                    .any(|(peer_idx, peer)| {
                        if rule.negated_condition_indices.contains(&peer_idx)
                            || peer.relation() != surface_relation
                        {
                            return false;
                        }
                        let peer = substitute_fact(peer, bindings);
                        std::mem::discriminant(&peer) == std::mem::discriminant(&cs)
                            && peer.inner().args.as_slice() == &gf.args[..1]
                    });
            if !condition_is_index_decidable(&gf.relation, inner) && !paired_functional_role {
                continue;
            }
            if gf
                .args
                .iter()
                .any(|a| matches!(a, GroundTerm::PatternVar(s) if s.starts_with("ev__")))
            {
                continue;
            }
            let Some(anchor_pos) = gf
                .args
                .iter()
                .position(|a| !matches!(a, GroundTerm::PatternVar(_)))
            else {
                continue;
            };
            let has_unbound_individual = gf
                .args
                .iter()
                .any(|a| matches!(a, GroundTerm::PatternVar(s) if s.starts_with("x__")));
            if !has_unbound_individual {
                continue;
            }
            let Some(by_val) = inner
                .arg_position_index
                .get(&(gf.relation.clone(), anchor_pos))
            else {
                continue;
            };
            let Some(facts) = by_val.get(&gf.args[anchor_pos]) else {
                continue;
            };
            // Facts that match ALL already-ground args of the (substituted) condition.
            let matching: Vec<&StoredFact> = facts
                .iter()
                .filter(|f| {
                    if std::mem::discriminant(*f) != std::mem::discriminant(&cs) {
                        return false;
                    }
                    let fa = &f.inner().args;
                    fa.len() == gf.args.len()
                        && gf
                            .args
                            .iter()
                            .zip(fa.iter())
                            .all(|(c, a)| matches!(c, GroundTerm::PatternVar(_)) || c == a)
                })
                .collect();
            if matching.len() == 1 {
                let fa = &matching[0].inner().args;
                for (i, a) in gf.args.iter().enumerate() {
                    if let GroundTerm::PatternVar(s) = a {
                        if s.starts_with("x__") && !bindings.contains_key(s) {
                            bindings.insert(s.clone(), fa[i].clone());
                            newly_bound.push(s.clone());
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    newly_bound
}

fn prefer_non_definitive(
    current: Option<QueryResult>,
    candidate: QueryResult,
) -> Option<QueryResult> {
    if candidate.is_definitive() {
        return current;
    }
    match (current, candidate) {
        (Some(QueryResult::ResourceExceeded(kind)), QueryResult::Unknown(_)) => {
            Some(QueryResult::ResourceExceeded(kind))
        }
        (Some(QueryResult::Unknown(_)), QueryResult::ResourceExceeded(kind)) => {
            Some(QueryResult::ResourceExceeded(kind))
        }
        (Some(existing), _) => Some(existing),
        (None, candidate) => Some(candidate),
    }
}

/// Resolve the non-definitive region of And/Or: the callers' `is_false()`/`is_true()`
/// guards have already decided every case where the verdict is definitive, so at least
/// one operand here is non-definitive and the result is too. `ResourceExceeded` outranks
/// `Unknown` (it is the more actionable reason); within the same rank the left operand
/// wins. This is the single source of truth shared with `KnowledgeBase::combine_root_results`
/// — keep them identical so the two cannot drift apart.
///
/// (Replaces a `prefer_non_definitive(None, left)`-seeded fold that wrongly collapsed to
/// `False` whenever the *left* operand was definitive — e.g. `True ∧ Unknown` → `False`.)
pub(crate) fn combine_indeterminate(left: QueryResult, right: QueryResult) -> QueryResult {
    match (left, right) {
        (QueryResult::ResourceExceeded(kind), _) => QueryResult::ResourceExceeded(kind),
        (_, QueryResult::ResourceExceeded(kind)) => QueryResult::ResourceExceeded(kind),
        (QueryResult::Unknown(reason), _) => QueryResult::Unknown(reason),
        (_, QueryResult::Unknown(reason)) => QueryResult::Unknown(reason),
        // Unreachable: both-definitive cases are decided by the callers before this runs.
        // Kept total to mirror the Lean model; the debug_assert turns a future caller
        // that violates the precondition into a loud failure instead of a silent
        // fabricated FALSE (the `True ∧ Unknown → False` class this fn replaced).
        (l, r) => {
            debug_assert!(
                false,
                "combine_indeterminate reached with two definitive operands: {l:?} / {r:?}"
            );
            QueryResult::False
        }
    }
}

fn combine_conjunction(left: QueryResult, right: QueryResult) -> QueryResult {
    if left.is_false() || right.is_false() {
        QueryResult::False
    } else if left.is_true() && right.is_true() {
        QueryResult::True
    } else {
        combine_indeterminate(left, right)
    }
}

fn combine_disjunction(left: QueryResult, right: QueryResult) -> QueryResult {
    if left.is_true() || right.is_true() {
        QueryResult::True
    } else if left.is_false() && right.is_false() {
        QueryResult::False
    } else {
        combine_indeterminate(left, right)
    }
}

/// Negate a sub-goal's result under negation-as-failure (every caller is a NAF
/// check: the surface `na` NotNode and the rule-antecedent negated conditions).
///
/// `¬True → False` and `¬False → True` are DEFINITIVE: `¬False → True` is a
/// successful NAF/closed-world conclusion, and the proof carries that note via
/// `ProofTrace::has_naf_dependency` (a `Negation` step with `holds:true`) — NOT
/// as an Unknown reason. But negating an UNDETERMINED sub-goal (`¬Unknown`)
/// originates `UnknownReason::NafDependent` — "the answer depends on a NAF check
/// that is itself undetermined" — the four-valued contract's promised reason
/// (defined + documented but previously never constructed). The original inner
/// reason (e.g. CycleCut) is the root cause and remains visible in the trace;
/// the verdict reason becomes the negation-specific `NafDependent`.
/// `ResourceExceeded` is polarity-independent and forwarded unchanged.
///
/// EVERY caller should be [`negate_result_tracked`], not this function directly: the
/// collapse is where the "was the inner CUT?" information is lost, and witness
/// enumeration needs it. The bare form stays for the Lean-parity test, which pins this
/// exact mapping.
fn negate_result(result: QueryResult) -> QueryResult {
    match result {
        QueryResult::True => QueryResult::False,
        QueryResult::False => QueryResult::True,
        QueryResult::Unknown(_) => QueryResult::Unknown(UnknownReason::NafDependent),
        QueryResult::ResourceExceeded(kind) => QueryResult::ResourceExceeded(kind),
    }
}

/// [`negate_result`], plus a monotone note in `naf_cut_epoch` whenever an `Unknown`
/// is collapsed to `Unknown(NafDependent)`.
///
/// The verdict is bit-identical to `negate_result`'s — the mapping is pinned by
/// `exhaustive_soundness_matches_lean_model` and by `proofs/Combiner.lean`, and
/// `NafDependent` remains the one verdict-level reason for a negated non-definitive.
/// Final `NafDependent` witness leaves now refuse by their own non-definitive verdict;
/// the epoch remains a separate record of collapse sites so abandoned internal rule
/// attempts can be regression-tested without changing the final-leaf gate. It never
/// changes entailment, proof construction, or the `True`/`False` collection controls.
///
/// The epoch RECORDS; it never decides. That separation is what makes this sound:
/// a collapse site sits upstream of every pending-discard point in rule firing, so a
/// rule attempt the engine deliberately abandons also bumps the counter. The leaf
/// guard in `find_witnesses` therefore consults the epoch ONLY when the leaf's own
/// verdict is non-definitive — a goal that ends `True`, or definitively `False` by
/// another rule, ignores the bump entirely. Modelled on `cycle_cut_epoch`, which
/// guards `depth_cut_table` inserts by exactly the same discipline.
///
/// A bump asserts nothing, so every negation site can call this unconditionally
/// without a per-site "is it safe here" argument — including the materialised fast
/// path (whose input is always definitive, so it never bumps) and the candidate
/// filter (whose verdict never escapes).
fn negate_result_tracked(result: QueryResult, inner: &KnowledgeBaseInner) -> QueryResult {
    if matches!(&result, QueryResult::Unknown(_)) && witness_enumeration_incomplete(&result) {
        inner
            .naf_cut_epoch
            .set(inner.naf_cut_epoch.get().wrapping_add(1));
    }
    negate_result(result)
}

/// Evaluate a negated event-decomposed restrictor (`poi na <predicate>`) by
/// negation-as-failure over an existential. The condition HOLDS (the rule fires)
/// iff NO binding of the group's `event_var` satisfies ALL inner conditions for the
/// already-bound universal — i.e. "no witness exists" (`la .adam.` has not
/// consented). Composes only the shared-`&inner` primitives, so it runs from the
/// SHARED-`&inner` firing path (unlike `check_formula_holds_core`, which owns
/// the full formula evaluator): enumerate the same complete candidate
/// pool the positive ExistsNode evaluator uses (`ensure_candidates`, incl. event
/// Skolems — so a consenting person's witness is always found), check each via
/// `check_predicate_in_kb_typed`, then `negate_result` the four-valued existential
/// verdict. Short-circuits on the first full witness (the common "consented" case
/// is fast). Returns True (no witness → obligation arises) / False (witness → no
/// obligation) / `Unknown(NafDependent)` (the existential is undetermined).
fn eval_negated_exists_group(
    group: &NegatedExistsGroup,
    bindings: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    // MATERIALISED FAST PATH — the whole point of `crate::materialize`.
    //
    // When the group's surface relation has a COMPLETE saturated extension, "does a
    // witness exist" is a set membership test, not a candidate sweep: absent from a
    // complete extension IS "not derivable", which is exactly what NAF asks. This is
    // what turns a rule like utopia's `teaches($t,$s) & ~false($t) -> reward($t)` from
    // a full re-derivation of the fifteen-conjunct void rule per candidate into a hash
    // lookup — measured 1037 ms → 11 ms on `utopia.nibli` (`just bench-naf`).
    //
    // Saturation only holds Bare tuples (eligibility refuses flavoured relations
    // outright). `probe_negated_group` returns `None` for anything it cannot
    // project or fully ground, and `is_complete_for` is false unless the extension
    // is both complete and arity-matched — so every case the shortcut does not
    // cover falls through to the search below, unchanged.
    if inner.materialization
        && let Some(m) = inner.materialized.borrow().as_ref()
        && let Some((rel, tuple)) = crate::materialize::probe_negated_group(group, bindings)
        && m.is_complete_for(&rel, tuple.len())
    {
        return negate_result_tracked(
            if m.contains(&rel, &tuple) {
                QueryResult::True
            } else {
                QueryResult::False
            },
            inner,
        );
    }

    // Flavor-exact NAF: the group's inner templates carry exactly the flavor
    // written on the restrictor (`past ~P` → Past templates, built at
    // construction). A bare `~P` remains Bare. Both candidate narrowing and the
    // witness check consume the same templates, so they cannot disagree about
    // flavor.
    // Narrow the event candidates to those that could actually satisfy the inner
    // existential (asserted-fact index hits ∪ rule-derivable witnesses), falling
    // back to the full pool only when no condition cleanly anchors the event var.
    // Without this, the group enumerates the whole members^k pool per firing —
    // the GDPR full-corpus erasure rule blows past its time budget.
    let candidates =
        match collect_group_event_candidates(&group.conditions, &group.event_var, inner) {
            Some(narrowed) => narrowed,
            None => ensure_candidates(candidates_slot, inner).to_vec(),
        };
    let mut best: Option<QueryResult> = None;
    let mut any_witness = false;
    for cand in &candidates {
        let mut b = bindings.clone();
        b.insert(group.event_var.clone(), cand.clone());
        let mut all_inner_true = true;
        let mut inner_pending: Option<QueryResult> = None;
        for tmpl in &group.conditions {
            let cs = substitute_fact(tmpl, &b);
            let r = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
            if r.is_false() {
                all_inner_true = false;
                inner_pending = None;
                break;
            }
            if !r.is_true() {
                all_inner_true = false;
                inner_pending = prefer_non_definitive(inner_pending, r);
            }
        }
        if all_inner_true {
            any_witness = true;
            break;
        }
        best = prefer_non_definitive(best, inner_pending.unwrap_or(QueryResult::False));
    }
    let exists_verdict = if any_witness {
        QueryResult::True
    } else {
        best.unwrap_or(QueryResult::False)
    };
    negate_result_tracked(exists_verdict, inner)
}

/// Fold each negated-exists group's NAF verdict into a rule's condition
/// accumulators (`hold` / `pending`), exactly as a positive condition would: a
/// definitively-false group kills the firing, a non-definitive one keeps it
/// pending. Called AFTER the positive condition loop (so the universal is bound);
/// skipped when the positive conditions already failed definitively.
#[allow(clippy::too_many_arguments)]
fn fold_negated_groups(
    rule: &UniversalRuleRecord,
    bindings: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    hold: &mut bool,
    pending: &mut Option<QueryResult>,
) {
    if rule.negated_exists_groups.is_empty() || (!*hold && pending.is_none()) {
        return;
    }
    for group in &rule.negated_exists_groups {
        let gv = eval_negated_exists_group(group, bindings, inner, candidates_slot, depth, visited);
        if gv.is_false() {
            *hold = false;
            *pending = None;
            break;
        }
        if !gv.is_true() {
            *hold = false;
            *pending = prefer_non_definitive(pending.take(), gv);
        }
    }
}

/// Cooperative cancellation checkpoint. Returns `Err` when an installed cancel
/// flag has been raised (by the native nibli-server request watchdog), aborting
/// the in-flight query through the existing `Result` error channel. A `None` flag
/// (nibli-host/nibli-pipeline/tests) makes this a single branch with no clock access.
#[inline]
pub(super) fn check_cancelled(inner: &KnowledgeBaseInner) -> Result<(), String> {
    if inner
        .cancel
        .as_ref()
        .is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed))
    {
        return Err("reasoning cancelled: deadline exceeded".to_string());
    }
    Ok(())
}

pub(super) fn check_formula_holds(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
    compute_memo: &mut QueryComputeMemo,
) -> Result<QueryResult, String> {
    // The bare (untraced) entry: delegate to the single evaluator with a no-op
    // sink (every recording branch is dead-code-eliminated for `NoOpSink`), and
    // drop the step index. The post-check converts a flag raised by the watchdog
    // DURING a long backward-chaining call into a clean `Err`; the core also
    // check_cancelled's at every node entry.
    check_cancelled(inner)?;
    let (result, _idx) = check_formula_holds_core::<NoOpSink>(
        buffer,
        node_id,
        subs,
        inner,
        tense,
        compute_memo,
        &mut NoOpSink,
    )?;
    check_cancelled(inner)?;
    Ok(result)
}

/// The proof-recording entry: evaluate the formula AND build its proof trace in
/// ONE walk, returning the authoritative four-valued verdict together with the
/// root proof-step index. Replaces the former separate `check_formula_holds`
/// (verdict) + `check_formula_holds_traced` (trace) double evaluation — the
/// trace's per-node `holds` is now natively the four-valued verdict's
/// `is_true()`, so no root reconciliation is needed.
pub(super) fn check_formula_holds_recording(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    tense: Option<&str>,
    memo: &mut HashMap<StoredFact, u32>,
    compute_memo: &mut QueryComputeMemo,
) -> Result<(QueryResult, u32), String> {
    check_cancelled(inner)?;
    let mut sink = RecordingSink { steps, memo };
    let result = check_formula_holds_core::<RecordingSink>(
        buffer,
        node_id,
        subs,
        inner,
        tense,
        compute_memo,
        &mut sink,
    )?;
    check_cancelled(inner)?;
    Ok(result)
}

/// The single four-valued formula evaluator, generic over a trace sink. The
/// verdict is computed identically to the former untraced evaluator (the
/// authoritative path); when `S::RECORDING`, each arm ALSO records its proof
/// step(s) via the sink and returns that step's index (the former
/// `check_formula_holds_traced`). For `NoOpSink` (`const RECORDING = false`)
/// every `if S::RECORDING { … }` block is dead-code-eliminated and the returned
/// index is 0.
///
/// And/Or short-circuit on a DEFINITIVELY decided left operand (False for And,
/// True for Or) — verdict-identical to `combine_conjunction`/`combine_disjunction`
/// (the only skipped operand is the one the left already decides). Enumerating
/// arms (Exists/ForAll/Count) probe candidates with `NoOpSink` for the verdict and
/// re-walk only the KEPT subtree (witness/counterexample/all-members) with `S`,
/// so discarded candidates never pollute the trace.
fn check_formula_holds_core<S: TraceSink>(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
    compute_memo: &mut QueryComputeMemo,
    sink: &mut S,
) -> Result<(QueryResult, u32), String> {
    let node = get_node(buffer, node_id)?;
    if matches!(node, LogicNode::CountNode(_))
        && let Some(pending) = inner.query_domain.incomplete.clone()
    {
        let idx = if S::RECORDING {
            sink.push(ProofStep {
                rule: ProofRule::PredicateCheck {
                    method: "indeterminate".into(),
                    detail: "individual witness domain incomplete".into(),
                },
                holds: false,
                children: vec![],
            })
        } else {
            0
        };
        return Ok((pending, idx));
    }
    let (verdict, idx) = check_formula_holds_core_impl::<S>(
        buffer,
        node_id,
        subs,
        inner,
        tense,
        compute_memo,
        sink,
    )?;
    let depends_on_complete_domain = matches!(node, LogicNode::ExistsNode(_)) && verdict.is_false()
        || matches!(node, LogicNode::ForAllNode(_)) && verdict.is_true();
    if depends_on_complete_domain && let Some(pending) = inner.query_domain.incomplete.clone() {
        let idx = if S::RECORDING {
            sink.push(ProofStep {
                rule: ProofRule::PredicateCheck {
                    method: "indeterminate".into(),
                    detail: "individual witness domain incomplete".into(),
                },
                holds: false,
                children: vec![idx],
            })
        } else {
            0
        };
        return Ok((pending, idx));
    }
    Ok((verdict, idx))
}

fn check_formula_holds_core_impl<S: TraceSink>(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
    compute_memo: &mut QueryComputeMemo,
    sink: &mut S,
) -> Result<(QueryResult, u32), String> {
    check_cancelled(inner)?;
    match get_node(buffer, node_id)? {
        LogicNode::AndNode((l, r)) => {
            // Abstraction opacity: `And(__abs_<id>(referent), body)`. The body is
            // OPAQUE to reasoning — the conjunction's verdict is just the marker's
            // (left). This is what keeps `believe P` from leaking or being satisfied by
            // bare P, while same-content abstractions still match via the marker.
            if is_abstraction_marker(buffer, *l) {
                return check_formula_holds_core::<S>(
                    buffer,
                    *l,
                    subs,
                    inner,
                    tense,
                    compute_memo,
                    sink,
                );
            }
            let (lv, li) =
                check_formula_holds_core::<S>(buffer, *l, subs, inner, tense, compute_memo, sink)?;
            // Short-circuit on a definitively-False left: `False ∧ x = False`
            // regardless of x (verdict-identical to combine_conjunction).
            if lv.is_false() {
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::Conjunction,
                        holds: false,
                        children: vec![li],
                    })
                } else {
                    0
                };
                return Ok((QueryResult::False, idx));
            }
            let (rv, ri) =
                check_formula_holds_core::<S>(buffer, *r, subs, inner, tense, compute_memo, sink)?;
            let verdict = combine_conjunction(lv, rv);
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::Conjunction,
                    holds: verdict.is_true(),
                    children: vec![li, ri],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::OrNode((l, r)) => {
            let (lv, li) =
                check_formula_holds_core::<S>(buffer, *l, subs, inner, tense, compute_memo, sink)?;
            // Short-circuit on a definitively-True left: `True ∨ x = True`.
            if lv.is_true() {
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::DisjunctionIntro {
                            side: "left".to_string(),
                        },
                        holds: true,
                        children: vec![li],
                    })
                } else {
                    0
                };
                return Ok((QueryResult::True, idx));
            }
            let (rv, ri) =
                check_formula_holds_core::<S>(buffer, *r, subs, inner, tense, compute_memo, sink)?;
            let rv_is_true = rv.is_true();
            let verdict = combine_disjunction(lv, rv);
            let idx = if S::RECORDING {
                if rv_is_true {
                    sink.push(ProofStep {
                        rule: ProofRule::DisjunctionIntro {
                            side: "right".to_string(),
                        },
                        holds: true,
                        children: vec![ri],
                    })
                } else {
                    sink.push(ProofStep {
                        rule: ProofRule::DisjunctionIntro {
                            side: "neither".to_string(),
                        },
                        holds: verdict.is_true(),
                        children: vec![li, ri],
                    })
                }
            } else {
                0
            };
            Ok((verdict, idx))
        }
        // Negation-as-failure (NAF): ¬P holds when P cannot be proved.
        // Sound because stratification is enforced at rule registration time —
        // register_rule() rejects any rule that would create a negative cycle
        // in the predicate dependency graph. The `holds` flag is true only when
        // the inner is DEFINITIVELY False (a merely Unknown/RE inner is preserved
        // by negate_result and must not display a decided NAF dependency) — the
        // four-valued sub-verdict `iv` is natively in hand, so no recheck re-walk.
        LogicNode::NotNode(inner_node) => {
            let (iv, ii) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                tense,
                compute_memo,
                sink,
            )?;
            let verdict = negate_result_tracked(iv.clone(), &*inner);
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::Negation,
                    holds: matches!(iv, QueryResult::False),
                    children: vec![ii],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::PastNode(inner_node) => {
            let (verdict, ci) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                Some("Past"),
                compute_memo,
                sink,
            )?;
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ModalPassthrough {
                        kind: "past".to_string(),
                    },
                    holds: verdict.is_true(),
                    children: vec![ci],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::PresentNode(inner_node) => {
            let (verdict, ci) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                Some("Present"),
                compute_memo,
                sink,
            )?;
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ModalPassthrough {
                        kind: "present".to_string(),
                    },
                    holds: verdict.is_true(),
                    children: vec![ci],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::FutureNode(inner_node) => {
            let (verdict, ci) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                Some("Future"),
                compute_memo,
                sink,
            )?;
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ModalPassthrough {
                        kind: "future".to_string(),
                    },
                    holds: verdict.is_true(),
                    children: vec![ci],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::ObligatoryNode(inner_node) => {
            // Thread the deontic context into the leaf (like PastNode → Some("Past")),
            // so the predicate is checked as `StoredFact::Obligatory` and matches ONLY a
            // stored obligation — never a bare actuality. Deriving "is" from "ought"
            // would be an over-claim.
            let (verdict, ci) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                Some("Obligatory"),
                compute_memo,
                sink,
            )?;
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ModalPassthrough {
                        kind: "obligatory".to_string(),
                    },
                    holds: verdict.is_true(),
                    children: vec![ci],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::PermittedNode(inner_node) => {
            // Mirror the Obligatory arm: check the predicate as `StoredFact::Permitted`
            // so a permission is never conflated with an actuality.
            let (verdict, ci) = check_formula_holds_core::<S>(
                buffer,
                *inner_node,
                subs,
                inner,
                Some("Permitted"),
                compute_memo,
                sink,
            )?;
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ModalPassthrough {
                        kind: "permitted".to_string(),
                    },
                    holds: verdict.is_true(),
                    children: vec![ci],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::ExistsNode((v, body)) => {
            // Try batch compute fast path first (uses slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members = if v.starts_with("_ev") {
                        inner.all_typed_domain_members()
                    } else {
                        inner.all_non_event_domain_members()
                    };
                    if let Some(batch) = batch_evaluate_compute_for_members_with_memo(
                        &*inner,
                        rel,
                        args,
                        v,
                        members,
                        subs,
                        compute_memo,
                    ) {
                        // Clone the winning member before releasing the slice borrow.
                        let winner = batch
                            .results
                            .iter()
                            .position(|r| *r)
                            .map(|i| members[i].clone());
                        if let Some(winning_member) = winner {
                            let idx = if S::RECORDING {
                                let body_idx = with_sub(subs, v, winning_member.clone(), |s| {
                                    check_formula_holds_core::<S>(
                                        buffer,
                                        *body,
                                        s,
                                        inner,
                                        tense,
                                        compute_memo,
                                        sink,
                                    )
                                })?
                                .1;
                                sink.push(ProofStep {
                                    rule: ProofRule::ExistsWitness {
                                        var: v.clone(),
                                        term: witness_term_to_logical_term(&winning_member),
                                        origin: witness_origin(&winning_member),
                                    },
                                    holds: true,
                                    children: vec![body_idx],
                                })
                            } else {
                                0
                            };
                            return Ok((QueryResult::True, idx));
                        }
                        // The batch decided every candidate false. Preserve that
                        // evidence in the trace instead of falling through to a
                        // second candidate walk and emitting an empty
                        // `ExistsFailed`, which would make a compute-decided
                        // failure look like a closed-world absence.
                        let idx = if S::RECORDING {
                            let children = batch
                                .methods
                                .iter()
                                .zip(&batch.results)
                                .map(|(method, holds)| {
                                    sink.push(ProofStep {
                                        rule: ProofRule::ComputeCheck {
                                            method: (*method).to_string(),
                                            detail: rel.clone(),
                                        },
                                        holds: *holds,
                                        children: vec![],
                                    })
                                })
                                .collect();
                            sink.push(ProofStep {
                                rule: ProofRule::ExistsFailed,
                                holds: false,
                                children,
                            })
                        } else {
                            0
                        };
                        return Ok((QueryResult::False, idx));
                    }
                }
            }
            // Decomposed numeric/compute group: gather the surface operands
            // from role predicates, then evaluate locally or dispatch using the
            // same public-term contract as the flat ComputeNode arm.
            if let Some(group) =
                try_evaluate_numeric_group(&*inner, buffer, v, *body, subs, compute_memo)
            {
                let res = group.verdict.clone();
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::ComputeCheck {
                            method: group.method.to_string(),
                            detail: group.relation,
                        },
                        holds: res.is_true(),
                        children: vec![],
                    })
                } else {
                    0
                };
                return Ok((res, idx));
            }
            // MATERIALISED FAST PATH (positive twin of the one in
            // `eval_negated_exists_group`). "Does a witness exist" over a COMPLETE
            // saturated extension is a set membership test — no candidate sweep, no
            // per-candidate body re-walk, no depth bound.
            //
            // Placed HERE deliberately: after the batch-compute and numeric-group segments
            // above, which must keep precedence; and before
            // `collect_entailment_candidates`, which is the cost this exists to skip.
            //
            // Two guards the negated twin does not need. `tense.is_none()` — the
            // saturation only ever holds Bare tuples. And the `materialized` borrow is
            // read into a local and DROPPED before anything else runs. Later probes may
            // borrow the same `RefCell`; keeping this guard alive across them would turn
            // an implementation detail into a runtime `BorrowMutError`.
            //
            // NOT taken during a proof-traced query (`positive_lookup` is lowered for its
            // whole duration): a lookup has no derivation to record, and the trace contract
            // is built on there being one — `ProofRule::ExistsWitness` names the witness
            // term, which the projection eliminated, and `proofs/Trace.lean`'s certificates
            // assume a rule-local blocking premise. DECIDED 2026-08-16 as permanent, not
            // pending (GUARANTEES records the reasons and the re-open trigger — a
            // mechanized saturation proof joining Track B): traced queries keep the
            // backward-chaining path and stay exactly as sound, just slower.
            if inner.positive_lookup.get() && tense.is_none() && inner.materialization {
                let hit = crate::materialize::probe_positive_group(buffer, *body, v, subs)
                    .and_then(|(rel, tuple)| {
                        let m = inner.materialized.borrow();
                        let m = m.as_ref()?;
                        m.is_complete_for(&rel, tuple.len())
                            .then(|| m.contains(&rel, &tuple))
                    });
                if let Some(found) = hit {
                    return Ok((
                        if found {
                            QueryResult::True
                        } else {
                            QueryResult::False
                        },
                        0,
                    ));
                }
            }
            // Slow path: need owned Vec because the body eval takes &mut inner.
            // Candidate narrowing (∃-heavy query blowup fix): when the body has
            // a mandatory positive anchor, enumerate only index/rule-derivable
            // candidates instead of the full domain × SkolemFn-registry
            // cartesian — completeness argument at collect_entailment_candidates.
            let mut candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(entry.symbol, &combo));
                            }
                        }
                        all
                    }
                };
            restrict_to_activated_individuals(&mut candidates, v, inner);
            let mut best_result = None;
            for candidate in &candidates {
                // Probe the verdict with a no-op sink (no recording of discarded
                // candidates); record only the winning witness's subtree below.
                let result = with_sub(subs, v, candidate.clone(), |s| {
                    check_formula_holds_core::<NoOpSink>(
                        buffer,
                        *body,
                        s,
                        inner,
                        tense,
                        compute_memo,
                        &mut NoOpSink,
                    )
                })?
                .0;
                if result.is_true() {
                    let idx = if S::RECORDING {
                        let body_idx = with_sub(subs, v, candidate.clone(), |s| {
                            check_formula_holds_core::<S>(
                                buffer,
                                *body,
                                s,
                                inner,
                                tense,
                                compute_memo,
                                sink,
                            )
                        })?
                        .1;
                        sink.push(ProofStep {
                            rule: ProofRule::ExistsWitness {
                                var: v.clone(),
                                term: witness_term_to_logical_term(candidate),
                                origin: witness_origin(candidate),
                            },
                            holds: true,
                            children: vec![body_idx],
                        })
                    } else {
                        0
                    };
                    return Ok((QueryResult::True, idx));
                }
                best_result = prefer_non_definitive(best_result, result);
            }
            // No witness. `best_result` is Some iff some candidate was
            // non-definitive (prefer_non_definitive drops definitive ones), so it
            // distinguishes a genuine ExistsFailed (all definitively False) from a
            // non-committal indeterminate.
            let saw_non_definitive = best_result.is_some();
            let verdict = best_result.unwrap_or(QueryResult::False);
            let idx = if S::RECORDING {
                if saw_non_definitive {
                    sink.push(ProofStep {
                        rule: ProofRule::PredicateCheck {
                            method: "indeterminate".to_string(),
                            detail: "exists".to_string(),
                        },
                        holds: false,
                        children: vec![],
                    })
                } else {
                    let mut children = Vec::with_capacity(candidates.len());
                    for candidate in &candidates {
                        let body_idx = with_sub(subs, v, candidate.clone(), |s| {
                            check_formula_holds_core::<S>(
                                buffer,
                                *body,
                                s,
                                inner,
                                tense,
                                compute_memo,
                                sink,
                            )
                        })?
                        .1;
                        children.push(body_idx);
                    }
                    sink.push(ProofStep {
                        rule: ProofRule::ExistsFailed,
                        holds: false,
                        children,
                    })
                }
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::ForAllNode((v, body)) => {
            // A ForAll variable is always an INDIVIDUAL (event vars are
            // existentials inside the body), so range over the non-event domain —
            // an event Skolem must never be a spurious counterexample for a bare
            // body. Verdict-preserving for the guarded `Or(Not(P),Q)` form (events
            // vacuously satisfy it) and keeps them out of the ForallVerified list.
            let members: Vec<GroundTerm> = inner.all_non_event_domain_members().to_vec();
            if members.is_empty() {
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::ForallVacuous,
                        holds: true,
                        children: vec![],
                    })
                } else {
                    0
                };
                return Ok((QueryResult::True, idx));
            }
            // Batch compute fast path (slice, no .to_vec()).
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    let members_slice = inner.all_non_event_domain_members();
                    if let Some(batch) = batch_evaluate_compute_for_members_with_memo(
                        &*inner,
                        rel,
                        args,
                        v,
                        members_slice,
                        subs,
                        compute_memo,
                    ) {
                        let fail_member = batch
                            .results
                            .iter()
                            .position(|r| !*r)
                            .map(|i| members_slice[i].clone());
                        if let Some(counter) = fail_member {
                            let idx = if S::RECORDING {
                                let body_idx = with_sub(subs, v, counter.clone(), |s| {
                                    check_formula_holds_core::<S>(
                                        buffer,
                                        *body,
                                        s,
                                        inner,
                                        tense,
                                        compute_memo,
                                        sink,
                                    )
                                })?
                                .1;
                                sink.push(ProofStep {
                                    rule: ProofRule::ForallCounterexample {
                                        entity: WitnessBinding {
                                            variable: v.clone(),
                                            term: witness_term_to_logical_term(&counter),
                                            origin: witness_origin(&counter),
                                        },
                                    },
                                    holds: false,
                                    children: vec![body_idx],
                                })
                            } else {
                                0
                            };
                            return Ok((QueryResult::False, idx));
                        }
                        let idx = if S::RECORDING {
                            let (child_indices, entity_terms) = forall_record_all_members::<S>(
                                buffer,
                                *body,
                                v,
                                &members,
                                subs,
                                inner,
                                tense,
                                compute_memo,
                                sink,
                            )?;
                            sink.push(ProofStep {
                                rule: ProofRule::ForallVerified {
                                    entities: entity_terms,
                                },
                                holds: true,
                                children: child_indices,
                            })
                        } else {
                            0
                        };
                        return Ok((QueryResult::True, idx));
                    }
                }
            }
            // Slow path: untraced verdict semantics (short-circuit on a
            // definitively-False member; accumulate non-definitive ones), then
            // record the step matching the four-valued verdict.
            let mut best_result = None;
            let mut false_member: Option<GroundTerm> = None;
            let mut nondef_member: Option<GroundTerm> = None;
            for member in &members {
                let result = with_sub(subs, v, member.clone(), |s| {
                    check_formula_holds_core::<NoOpSink>(
                        buffer,
                        *body,
                        s,
                        inner,
                        tense,
                        compute_memo,
                        &mut NoOpSink,
                    )
                })?
                .0;
                if result.is_false() {
                    false_member = Some(member.clone());
                    break;
                }
                if !result.is_true() {
                    if nondef_member.is_none() {
                        nondef_member = Some(member.clone());
                    }
                    best_result = prefer_non_definitive(best_result, result);
                }
            }
            if let Some(counter) = false_member {
                let idx = if S::RECORDING {
                    let body_idx = with_sub(subs, v, counter.clone(), |s| {
                        check_formula_holds_core::<S>(
                            buffer,
                            *body,
                            s,
                            inner,
                            tense,
                            compute_memo,
                            sink,
                        )
                    })?
                    .1;
                    sink.push(ProofStep {
                        rule: ProofRule::ForallCounterexample {
                            entity: WitnessBinding {
                                variable: v.clone(),
                                term: witness_term_to_logical_term(&counter),
                                origin: witness_origin(&counter),
                            },
                        },
                        holds: false,
                        children: vec![body_idx],
                    })
                } else {
                    0
                };
                return Ok((QueryResult::False, idx));
            }
            if let Some(nd) = nondef_member {
                let verdict =
                    best_result.unwrap_or(QueryResult::Unknown(UnknownReason::IncompleteKnowledge));
                let idx = if S::RECORDING {
                    let body_idx = with_sub(subs, v, nd.clone(), |s| {
                        check_formula_holds_core::<S>(
                            buffer,
                            *body,
                            s,
                            inner,
                            tense,
                            compute_memo,
                            sink,
                        )
                    })?
                    .1;
                    sink.push(ProofStep {
                        rule: ProofRule::PredicateCheck {
                            method: "indeterminate".to_string(),
                            detail: "forall".to_string(),
                        },
                        holds: false,
                        children: vec![body_idx],
                    })
                } else {
                    0
                };
                return Ok((verdict, idx));
            }
            // All members hold.
            let idx = if S::RECORDING {
                let (child_indices, entity_terms) = forall_record_all_members::<S>(
                    buffer,
                    *body,
                    v,
                    &members,
                    subs,
                    inner,
                    tense,
                    compute_memo,
                    sink,
                )?;
                sink.push(ProofStep {
                    rule: ProofRule::ForallVerified {
                        entities: entity_terms,
                    },
                    holds: true,
                    children: child_indices,
                })
            } else {
                0
            };
            Ok((QueryResult::True, idx))
        }
        LogicNode::CountNode((v, count, body)) => {
            // ENTITY-LEVEL counting (GUARANTEES §Aggregation): enumerate one
            // representative per du-equivalence class (two names for one
            // entity count once — equivalence transfers the body facts, so
            // any member of a class answers for it). Under the explicit legacy
            // import profile, imported witnesses are ordinary logical domain
            // members here just as they are for ∃, ∀, and find.
            let members: Vec<GroundTerm> = {
                let mut seen = HashSet::new();
                let mut out = Vec::new();
                let mut candidates = inner.all_non_event_domain_members().to_vec();
                // If an imported name is `du`-equivalent to a KB name, expose
                // the KB representative for their one shared entity.
                candidates.sort_by_cached_key(|m| {
                    (
                        canonical_witness_term(&inner.equivalence_parent, m),
                        witness_origin(m) == nibli_types::logic::WitnessOrigin::ExistentialImport,
                        m.clone(),
                    )
                });
                for m in &candidates {
                    let canon = canonical_witness_term(&inner.equivalence_parent, m);
                    if seen.insert(canon) {
                        out.push(m.clone());
                    }
                }
                out
            };

            // Batch compute fast path.
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    if let Some(batch) = batch_evaluate_compute_for_members_with_memo(
                        &*inner,
                        rel,
                        args,
                        v,
                        &members,
                        subs,
                        compute_memo,
                    ) {
                        let satisfying = batch.results.iter().filter(|r| **r).count() as u32;
                        let existential_imported = members
                            .iter()
                            .zip(&batch.results)
                            .filter(|(member, holds)| {
                                **holds
                                    && witness_origin(member)
                                        == nibli_types::logic::WitnessOrigin::ExistentialImport
                            })
                            .count() as u32;
                        let verdict = if satisfying == *count {
                            QueryResult::True
                        } else {
                            QueryResult::False
                        };
                        let idx = if S::RECORDING {
                            let children = batch
                                .methods
                                .iter()
                                .zip(&batch.results)
                                .map(|(method, holds)| {
                                    sink.push(ProofStep {
                                        rule: ProofRule::ComputeCheck {
                                            method: (*method).to_string(),
                                            detail: rel.clone(),
                                        },
                                        holds: *holds,
                                        children: vec![],
                                    })
                                })
                                .collect();
                            sink.push(ProofStep {
                                rule: ProofRule::CountResult {
                                    expected: *count,
                                    actual: satisfying,
                                    existential_imported,
                                },
                                holds: verdict.is_true(),
                                children,
                            })
                        } else {
                            0
                        };
                        return Ok((verdict, idx));
                    }
                }
            }
            let mut satisfying = 0u32;
            let mut existential_imported = 0u32;
            let mut unresolved = 0u32;
            let mut best_result = None;
            for member in &members {
                let result = with_sub(subs, v, member.clone(), |s| {
                    check_formula_holds_core::<NoOpSink>(
                        buffer,
                        *body,
                        s,
                        inner,
                        tense,
                        compute_memo,
                        &mut NoOpSink,
                    )
                })?
                .0;
                match result {
                    QueryResult::True => {
                        satisfying += 1;
                        if witness_origin(member)
                            == nibli_types::logic::WitnessOrigin::ExistentialImport
                        {
                            existential_imported += 1;
                        }
                    }
                    QueryResult::False => {}
                    other => {
                        unresolved += 1;
                        best_result = prefer_non_definitive(best_result, other);
                    }
                }
            }
            let verdict = if unresolved == 0 {
                if satisfying == *count {
                    QueryResult::True
                } else {
                    QueryResult::False
                }
            } else if satisfying > *count || satisfying + unresolved < *count {
                QueryResult::False
            } else {
                best_result.unwrap_or(QueryResult::Unknown(UnknownReason::IncompleteKnowledge))
            };
            let idx = if S::RECORDING {
                let mut children = Vec::with_capacity(members.len());
                for member in &members {
                    let body_idx = with_sub(subs, v, member.clone(), |s| {
                        check_formula_holds_core::<S>(
                            buffer,
                            *body,
                            s,
                            inner,
                            tense,
                            compute_memo,
                            sink,
                        )
                    })?
                    .1;
                    children.push(body_idx);
                }
                sink.push(ProofStep {
                    rule: ProofRule::CountResult {
                        expected: *count,
                        actual: satisfying,
                        existential_imported,
                    },
                    holds: verdict.is_true(),
                    children,
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
        LogicNode::Predicate((rel, args)) => {
            if let Some(verdict) = try_numeric_comparison(rel, args, subs) {
                // Non-finite operands surface Unknown(NonFinite) — mirror the
                // event-decomposed path's proof-step method for them.
                let non_finite = matches!(verdict, QueryResult::Unknown(_));
                let idx = if S::RECORDING {
                    let detail = format!(
                        "{}({}) = {}",
                        rel,
                        args.iter()
                            .map(|a| match a {
                                LogicalTerm::Number(n) => format!("{}", *n as i64),
                                LogicalTerm::Variable(var) => subs
                                    .get(var.as_str())
                                    .map(|gt| gt.to_display_string())
                                    .unwrap_or_else(|| var.clone()),
                                _ => "?".to_string(),
                            })
                            .collect::<Vec<_>>()
                            .join(", "),
                        if non_finite {
                            "non-finite".to_string()
                        } else {
                            verdict.is_true().to_string()
                        }
                    );
                    sink.push(ProofStep {
                        rule: ProofRule::PredicateCheck {
                            method: if non_finite { "non_finite" } else { "numeric" }.to_string(),
                            detail,
                        },
                        holds: verdict.is_true(),
                        children: vec![],
                    })
                } else {
                    0
                };
                return Ok((verdict, idx));
            }
            // Build typed fact and query typed store for the authoritative verdict.
            if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                let mut visited = HashSet::new();
                let verdict = check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited);
                let idx = if S::RECORDING {
                    if verdict.is_true() {
                        // Record the derivation tree (asserted / derived / equality).
                        sink.trace_child(&fact, &*inner, 0, &mut visited)
                    } else if !matches!(verdict, QueryResult::False) {
                        // Non-definitive (Unknown/ResourceExceeded): neither proven
                        // nor refuted — emit a non-committal step, never a decided
                        // "not found".
                        let reason = match &verdict {
                            QueryResult::Unknown(r) => format!("unknown:{r:?}"),
                            QueryResult::ResourceExceeded(k) => format!("resource-exceeded:{k:?}"),
                            _ => "indeterminate".to_string(),
                        };
                        sink.push(ProofStep {
                            rule: ProofRule::PredicateCheck {
                                method: "indeterminate".to_string(),
                                detail: reason,
                            },
                            holds: false,
                            children: vec![],
                        })
                    } else {
                        // Definitively False — record which rules were tried and
                        // which condition failed. This is the `Neg` certificate of
                        // `proofs/Trace.lean:91`: every candidate rule must be blocked by a
                        // definitively-refuted positive premise or a definitively-holding
                        // NEGATED premise (`∃ p ∈ f.pos, Neg p  ∨  ∃ n ∈ f.neg, Pos n`).
                        // Two fidelity rules, both enforced by `trace_soundness_conformance`:
                        // the re-check runs at depth 0 — the SAME regime as the verdict above,
                        // so a blocking premise always exists when the verdict is False — and
                        // a condition under negation blocks when it HOLDS
                        // (`negated_condition_indices`), not when it fails.
                        let mut failed_children = Vec::new();
                        let rules = matching_rules_typed(&fact, &inner.universal_rules);
                        for rule in rules {
                            for concl in &rule.typed_conclusions {
                                if let Some(bindings) = unify_facts(concl, &fact) {
                                    for (ci, ct) in rule.typed_conditions.iter().enumerate() {
                                        let cond_fact = substitute_fact(ct, &bindings);
                                        let cond_result = check_predicate_in_kb_typed(
                                            &cond_fact,
                                            &*inner,
                                            0,
                                            &mut HashSet::new(),
                                        );
                                        let negated = rule.negated_condition_indices.contains(&ci);
                                        let blocked = if negated {
                                            cond_result.is_true()
                                        } else {
                                            !cond_result.is_true()
                                        };
                                        if blocked {
                                            let child_idx = sink.push(ProofStep {
                                                rule: ProofRule::RuleAttemptFailed {
                                                    rule_label: rule.label.clone(),
                                                    failed_condition: cond_fact.to_display_string(),
                                                },
                                                holds: false,
                                                children: vec![],
                                            });
                                            failed_children.push(child_idx);
                                            break; // First blocking premise is enough.
                                        }
                                    }
                                }
                            }
                        }
                        sink.push(ProofStep {
                            rule: ProofRule::PredicateNotFound {
                                predicate: fact.to_display_string(),
                            },
                            holds: false,
                            children: failed_children,
                        })
                    }
                } else {
                    0
                };
                Ok((verdict, idx))
            } else {
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::PredicateCheck {
                            method: "build_failed".to_string(),
                            detail: String::new(),
                        },
                        holds: false,
                        children: vec![],
                    })
                } else {
                    0
                };
                Ok((QueryResult::False, idx))
            }
        }
        LogicNode::ComputeNode((rel, args)) => {
            // Built-in arithmetic FIRST, then external dispatch — the
            // documented Layer-2 ordering (matches nibli-host's evaluate() and the
            // batch path; the backend is only consulted for what the engine
            // cannot compute itself).
            if let Some(result) = try_arithmetic_evaluation(rel, args, subs) {
                let verdict = if result {
                    QueryResult::True
                } else {
                    QueryResult::False
                };
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::ComputeCheck {
                            method: "arithmetic".to_string(),
                            detail: rel.clone(),
                        },
                        holds: result,
                        children: vec![],
                    })
                } else {
                    0
                };
                return Ok((verdict, idx));
            }
            if let Ok(resolved) = resolve_args_for_dispatch(args, subs) {
                let evaluation = evaluate_external_compute(&*inner, rel, &resolved, compute_memo);
                let verdict = evaluation.verdict;
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::ComputeCheck {
                            method: evaluation.method.to_string(),
                            detail: rel.clone(),
                        },
                        holds: verdict.is_true(),
                        children: vec![],
                    })
                } else {
                    0
                };
                return Ok((verdict, idx));
            }
            // Dispatch errors (including an unregistered backend or an argument
            // that cannot cross the protocol) are uniformly non-definitive.
            // Compute replies are query-local: no fact-store or prior-result
            // fallback may turn an outage into TRUE.
            let verdict = QueryResult::Unknown(UnknownReason::BackendUnavailable);
            let idx = if S::RECORDING {
                sink.push(ProofStep {
                    rule: ProofRule::ComputeCheck {
                        method: "backend_unavailable".to_string(),
                        detail: rel.clone(),
                    },
                    holds: verdict.is_true(),
                    children: vec![],
                })
            } else {
                0
            };
            Ok((verdict, idx))
        }
    }
}

/// Record the proof subtree for EVERY member of a fully-verified universal
/// (`ForallVerified`), returning the per-member child step indices and their
/// rendered entity terms. Only invoked on the recording path.
#[allow(clippy::too_many_arguments)]
fn forall_record_all_members<S: TraceSink>(
    buffer: &LogicBuffer,
    body: u32,
    v: &str,
    members: &[GroundTerm],
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
    compute_memo: &mut QueryComputeMemo,
    sink: &mut S,
) -> Result<(Vec<u32>, Vec<WitnessBinding>), String> {
    let mut child_indices = Vec::new();
    let mut entity_terms = Vec::new();
    for member in members {
        let body_idx = with_sub(subs, v, member.clone(), |s| {
            check_formula_holds_core::<S>(buffer, body, s, inner, tense, compute_memo, sink)
        })?
        .1;
        child_indices.push(body_idx);
        entity_terms.push(WitnessBinding {
            variable: v.to_string(),
            term: witness_term_to_logical_term(member),
            origin: witness_origin(member),
        });
    }
    Ok((child_indices, entity_terms))
}

pub(super) fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
    compute_memo: &mut QueryComputeMemo,
) -> Result<Vec<Vec<(String, GroundTerm)>>, String> {
    // Once any final leaf is non-definitive the enumeration is known incomplete and
    // `query_find_inner` will refuse with `Err` regardless of what the
    // remaining candidates yield — so stop the (potentially huge) candidate sweep
    // immediately instead of exploring it to the end. Without this, a cyclic
    // event-decomposed find terminates but only after enumerating the full
    // member×Skolem cartesian (seconds), even though the verdict is already decided.
    if inner.find_enumeration_incomplete {
        return Ok(Vec::new());
    }
    match get_node(buffer, node_id)? {
        LogicNode::ExistsNode((v, body)) => {
            // Decomposed numeric/compute group — the SAME recogniser and the SAME
            // routing the verdict path uses at its own `ExistsNode` arm. Sharing one
            // evaluator is the whole point: the two halves disagreed precisely because
            // enumeration had its own idea of what a group was.
            //
            // Without this, enumeration peels the group's `∃_ev` and sweeps domain
            // candidates, degrading every conjunct to a store lookup that finds nothing
            // (neither a computed comparison nor a compute result is ever stored). The
            // query then answered TRUE as a boolean and reported ZERO rows here — and
            // on an empty domain the sweep had no candidates at all, so not even the
            // accidental refusal fired.
            //
            // Enumeration does NOT dispatch: `find_enumeration` makes any group whose
            // routing would call out refuse at `dispatch_to_backend`, so the verdict
            // comes back non-definitive, the shared classifier latches incompleteness, and
            // the caller reports an incomplete enumeration instead of an undercount.
            // Anything definitively decidable locally — a finite comparison, or finite
            // arithmetic over resolved operands — is decided here and filters rows.
            //
            // Nothing else changes shape: the group binds no user-visible variable, so
            // a satisfied one yields the same empty binding set the satisfied-leaf arm
            // below returns, and a group whose operands are non-numeric CONSTANTS
            // (`greater(Alis, Bob)`) still returns None and falls through to the store.
            let epoch_before = inner.naf_cut_epoch.get();
            if let Some(group) =
                try_evaluate_numeric_group(&*inner, buffer, v, *body, subs, compute_memo)
            {
                if group.verdict.is_true() {
                    return Ok(vec![vec![]]);
                }
                if leaf_search_incomplete(&group.verdict, &*inner, epoch_before) {
                    inner.find_enumeration_incomplete = true;
                }
                return Ok(Vec::new());
            }

            let mut results = Vec::new();

            // Candidate enumeration MUST match the verdict path's ExistsNode arm
            // (`collect_entailment_candidates`, below): the anchored collector
            // binds a dependent-Skolem conclusion position over real domain
            // members (→ `sk_1(adam)`) and strips `Unspecified`. The old
            // find-only path (`collect_candidates` + a generic, non-anchored
            // registry cartesian) leaked the raw conclusion template
            // `SkolemFn("sk_1", PatternVar)` as an *unbound* witness (`sk_1(_)`)
            // and double-counted bound witnesses — nondeterministically, since
            // it merged two HashSet-derived sources without dedup. Find still
            // body-checks every candidate below, so sharing the verdict path's
            // superset is sound and complete (any satisfying witness meets every
            // mandatory anchor). Falls back to the full domain + registry
            // cartesian only when no mandatory positive anchor exists
            // (pure-negation / pure-Or body).
            let mut candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(entry.symbol, &combo));
                            }
                        }
                        all
                    }
                };

            restrict_to_activated_individuals(&mut candidates, v, inner);
            for candidate in candidates {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), candidate.clone());
                let sub_results =
                    find_witnesses(buffer, *body, &mut new_subs, inner, tense, compute_memo)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), candidate.clone()));
                    results.push(bindings);
                }
            }

            Ok(results)
        }
        LogicNode::PastNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Past"), compute_memo)
        }
        LogicNode::PresentNode(inner_node) => find_witnesses(
            buffer,
            *inner_node,
            subs,
            inner,
            Some("Present"),
            compute_memo,
        ),
        LogicNode::FutureNode(inner_node) => find_witnesses(
            buffer,
            *inner_node,
            subs,
            inner,
            Some("Future"),
            compute_memo,
        ),
        LogicNode::AndNode((l, r)) => {
            let incomplete_before = inner.find_enumeration_incomplete;
            let left_results = find_witnesses(buffer, *l, subs, inner, tense, compute_memo)?;
            // An incomplete left subtree is not itself the final candidate formula:
            // a definitively-False right conjunct absorbs it, making this candidate
            // definitively absent. Re-evaluate the whole conjunction in that narrow
            // case so collection success cannot depend on grouping or operand order.
            //
            // A definitive True here deliberately does NOT clear the latch. That shape
            // arises when the left child is an Or with both a non-definitive branch and
            // a True branch; the selected collection policy refuses because that
            // branch may contribute additional bindings even though entailment is True.
            if !incomplete_before && inner.find_enumeration_incomplete {
                inner.find_enumeration_incomplete = false;
                let verdict =
                    check_formula_holds(buffer, node_id, subs, inner, tense, compute_memo)?;
                inner.find_enumeration_incomplete = !verdict.is_false();
                return Ok(Vec::new());
            }
            let mut results = Vec::new();
            for left_bindings in left_results {
                let mut merged_subs = subs.clone();
                for (k, v) in &left_bindings {
                    merged_subs.insert(k.clone(), v.clone());
                }
                let right_results =
                    find_witnesses(buffer, *r, &mut merged_subs, inner, tense, compute_memo)?;
                for right_bindings in right_results {
                    let mut combined = left_bindings.clone();
                    combined.extend(right_bindings);
                    results.push(combined);
                }
            }
            Ok(results)
        }
        LogicNode::OrNode((l, r)) => {
            let mut results = find_witnesses(buffer, *l, subs, inner, tense, compute_memo)?;
            results.extend(find_witnesses(
                buffer,
                *r,
                subs,
                inner,
                tense,
                compute_memo,
            )?);
            Ok(results)
        }
        _ => {
            // Snapshot BEFORE evaluating: `leaf_search_incomplete` compares against it
            // to retain a diagnostic record of any negation collapse in this leaf's
            // subtree. Nothing on the find path evaluates before this point —
            // `collect_entailment_candidates` narrows from MANDATORY POSITIVE anchors
            // and skips `NotNode`, so it cannot negate. If a future collector ever
            // evaluates NAF, this snapshot has to move ahead of candidate collection.
            let epoch_before = inner.naf_cut_epoch.get();
            let verdict = check_formula_holds(buffer, node_id, subs, inner, tense, compute_memo)?;
            if verdict.is_true() {
                Ok(vec![vec![]])
            } else {
                // Not a witness. A definitive False is a genuine absence; any Unknown
                // or ResourceExceeded leaves membership undecided. Flag the latter so
                // `query_find_inner` refuses a partial count/aggregate rather than
                // silently undercounting.
                if leaf_search_incomplete(&verdict, &*inner, epoch_before) {
                    inner.find_enumeration_incomplete = true;
                }
                Ok(vec![])
            }
        }
    }
}

/// True when a final witness-leaf verdict leaves membership undecided.
///
/// Collections may emit rows only from definitive `True` leaves and discard only
/// definitive `False` leaves. Every `Unknown(_)` and `ResourceExceeded(_)`, across
/// either polarity, therefore latches the existing query-global incomplete-enumeration
/// refusal. This is deliberately reason-agnostic so a future non-definitive reason
/// fails closed without another allowlist edit.
fn witness_enumeration_incomplete(v: &QueryResult) -> bool {
    !v.is_definitive()
}

#[cfg(test)]
mod witness_enumeration_incomplete_tests {
    use super::*;

    #[test]
    fn every_non_definitive_verdict_refuses_witness_enumeration() {
        let non_definitive = [
            QueryResult::Unknown(UnknownReason::CycleCut),
            QueryResult::Unknown(UnknownReason::IncompleteKnowledge),
            QueryResult::Unknown(UnknownReason::NafDependent),
            QueryResult::Unknown(UnknownReason::BackendUnavailable),
            QueryResult::Unknown(UnknownReason::NonFinite),
            QueryResult::ResourceExceeded(ResourceKind::Depth),
            QueryResult::ResourceExceeded(ResourceKind::Fuel),
            QueryResult::ResourceExceeded(ResourceKind::Memory),
        ];
        for verdict in non_definitive {
            assert!(
                witness_enumeration_incomplete(&verdict),
                "non-definitive witness leaf must refuse: {verdict:?}"
            );
        }

        assert!(!witness_enumeration_incomplete(&QueryResult::True));
        assert!(!witness_enumeration_incomplete(&QueryResult::False));
    }
}

/// Whether a non-`True` witness leaf leaves the witness set incomplete.
///
/// `epoch_before` is `naf_cut_epoch` sampled immediately before the leaf was
/// evaluated. The epoch term is retained as a defensive record of a collapse inside
/// the leaf; the reason-agnostic classifier already covers every current
/// non-definitive final verdict.
///
/// Final-leaf gating is the safety boundary. Rule firing tries every matching rule and
/// candidate binding, and may encounter a non-definitive internal attempt before a
/// later rule proves the leaf `True` or a sibling makes it definitively `False`.
/// Consulting incompleteness only after the leaf's own verdict is known prevents those
/// abandoned attempts from turning definitive rows or absences into errors.
///
/// If the final verdict is non-definitive for any reason, refusal is deliberate even
/// when another OR branch produced a row: the evaluated candidate's full membership
/// set was not decided, so returning a partial collection would overstate completeness.
fn leaf_search_incomplete(
    verdict: &QueryResult,
    inner: &KnowledgeBaseInner,
    epoch_before: u64,
) -> bool {
    witness_enumeration_incomplete(verdict)
        || (!verdict.is_definitive() && inner.naf_cut_epoch.get() != epoch_before)
}

// ─── Typed Backward-Chaining (Phase 4-5b) ────────────────────────
//
// These functions mirror the fact_repr-based backward-chaining above but
// operate on StoredFact/GroundTerm directly, avoiding all string ops.

pub(super) fn clear_typed_pred_cache(inner: &KnowledgeBaseInner) {
    inner.pred_cache.borrow_mut().clear();
    // The depth-cut table shares the pred_cache lifecycle exactly (query
    // start clear + every-mutation invalidation route through here).
    inner.depth_cut_table.borrow_mut().clear();
}

/// Drop the stratum-ordered saturation ([`crate::materialize`]).
///
/// DELIBERATELY NOT part of `clear_typed_pred_cache`. That funnel runs at query START
/// as well as at mutation, and the saturation is a claim about the KB's CONTENT, not
/// about one query — re-deriving it per query would throw away the whole point on the
/// second query against an unchanged KB. So it is dropped at exactly the mutation
/// points instead: the two structural ones (`assert_typed_fact` / `unassert_typed_fact`,
/// which cover forward chaining and strict rollback), the
/// `invalidate_pred_cache` wrapper every assert/retract/reset already calls, and
/// `rebuild_inner` / `reset` directly.
///
/// Getting this wrong is not a performance bug: a stale extension answers `~p(x)` TRUE
/// for a `p` the new fact just made derivable.
/// Invalidation for a STORE INSERT, filtered by relevance.
///
/// The saturated extensions are a claim about a dependency CONE — the closure of
/// the query roots they were requested for. A stored fact whose surface relation
/// lies outside that cone cannot change any extension in it: no completed
/// relation reads it, positively or under negation (the cone is closed over
/// both), and `complete` is a subset of the cone, so the relation carries no
/// completeness claim of its own either. Such an insert therefore leaves the
/// saturation standing instead of paying for a full recompute at the next query
/// — the case that dominates a large KB, where each query cone is a small slice
/// and most assertions land elsewhere.
///
/// Anything inside the cone, and every non-insert mutation (removal, rule
/// registration, retraction, reset, profile switch), keeps the unconditional
/// drop via [`invalidate_materialization`].
pub(super) fn invalidate_materialization_for_insert(inner: &KnowledgeBaseInner, fact: &StoredFact) {
    // Domain membership is global, even when this fact is outside the currently
    // saturated query cone. Never reuse witness closure across any insertion.
    inner.query_domain.completed_at.set(None);
    let surface = crate::materialize::surface_relation(fact.relation()).to_string();
    // DECIDE under a shared borrow, ACT after releasing it: the two mutating
    // arms below each re-borrow, and a `RefMut` held across them panics.
    enum Fate {
        /// Outside the cone — nothing here can depend on it.
        Untouched,
        /// Growth through a negated condition SHRINKS the model, so the
        /// extensions cannot be repaired incrementally.
        Drop,
        /// In-cone and monotone: fold it in at the next query.
        Grow,
    }
    let fate = match inner.materialized.borrow().as_ref() {
        None => return,
        Some(m) if !m.cone.contains(&surface) => Fate::Untouched,
        Some(m) if m.negatively_read.contains(&surface) => Fate::Drop,
        Some(_) => Fate::Grow,
    };
    match fate {
        Fate::Untouched => {}
        Fate::Drop => *inner.materialized.borrow_mut() = None,
        Fate::Grow => {
            if let Some(m) = inner.materialized.borrow_mut().as_mut() {
                m.grew.insert(surface);
            }
        }
    }
}

pub(super) fn invalidate_materialization(inner: &KnowledgeBaseInner) {
    inner.query_domain.completed_at.set(None);
    *inner.materialized.borrow_mut() = None;
}

/// Check whether a typed fact is present in the content-only truth store.
pub(super) fn typed_fact_is_stored(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    // Fast path: exact match.
    if inner.fact_store.contains(fact) {
        return true;
    }
    // Equivalence path: try substitutions of equivalent terms in args.
    if inner.equivalence_parent.is_empty() {
        return false;
    }
    typed_fact_is_stored_with_equivalence(fact, inner).is_some()
}

/// If `fact` holds under some du-equivalence substitution of its arguments,
/// return the exact equivalent variant present in the truth store. Its origin
/// sidecar, not this membership check, decides how a trace labels the child.
fn typed_fact_is_stored_with_equivalence(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
) -> Option<StoredFact> {
    let gf = fact.inner();
    if gf
        .args
        .iter()
        .any(|term| matches!(term, GroundTerm::SkolemFn(_, _) | GroundTerm::DepPair(_, _)))
    {
        let canonical = |value: &StoredFact| {
            StoredFact::with_tense_from(
                GroundFact::new(
                    value.relation(),
                    value
                        .inner()
                        .args
                        .iter()
                        .map(|term| canonical_witness_term(&inner.equivalence_parent, term))
                        .collect(),
                ),
                value,
            )
        };
        let wanted = canonical(fact);
        if let Some(found) = inner
            .fact_store
            .lookup_predicate(fact.relation())
            .into_iter()
            .flatten()
            .filter(|stored| canonical(stored) == wanted)
            .min_by(|a, b| a.inner().args.cmp(&b.inner().args))
        {
            return Some(found.clone());
        }
    }
    // For each arg position, get the equivalence class.
    let equiv_args: Vec<Vec<GroundTerm>> = gf
        .args
        .iter()
        .map(|arg| {
            get_equivalence_class_readonly(
                &inner.equivalence_parent,
                &inner.equivalence_classes,
                arg,
            )
        })
        .collect();

    // If no argument has equivalents beyond itself, nothing to try.
    if equiv_args.iter().all(|cls| cls.len() <= 1) {
        return None;
    }

    // Enumerate cartesian product of equivalence classes (skip original combo).
    for combo in CartesianProduct::new(&equiv_args) {
        let variant_gf = GroundFact::new(gf.relation.clone(), combo);
        let variant = StoredFact::with_tense_from(variant_gf, fact);
        if variant != *fact && inner.fact_store.contains(&variant) {
            return Some(variant);
        }
    }
    None
}

/// Format the equality substitution note for a proof step: the argument pairs
/// where `orig` and `variant` differ, rendered as `"a = b, x = y"` — `=` is the
/// nibli KR surface identity operator, and this note is reader-facing (it lands
/// in the rendered proof trace). Shared by the asserted-via-equivalence and
/// rule-derived-via-equivalence trace paths.
fn equals_substitution_note(orig: &StoredFact, variant: &StoredFact) -> String {
    orig.inner()
        .args
        .iter()
        .zip(variant.inner().args.iter())
        .filter(|(o, v)| o != v)
        .map(|(o, v)| format!("{} = {}", o.to_display_string(), v.to_display_string()))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Recover the real equality assertions that license every changed argument.
/// The union-find index proves that two terms share a representative but cannot
/// explain why after path compression; the evidence graph preserves those
/// edges. Missing evidence is treated fail-closed by the trace path.
fn equality_support_facts(
    orig: &StoredFact,
    variant: &StoredFact,
    inner: &KnowledgeBaseInner,
) -> Option<Vec<StoredFact>> {
    let mut facts = Vec::new();
    let mut seen = HashSet::new();
    for (original, substituted) in orig
        .inner()
        .args
        .iter()
        .zip(variant.inner().args.iter())
        .filter(|(original, substituted)| original != substituted)
    {
        for equality in equality_path_facts(inner, original, substituted)? {
            if seen.insert(equality.clone()) {
                facts.push(equality);
            }
        }
    }
    Some(facts)
}

/// Bound on the du-equivalence VARIANT DERIVATION fan-out: the fallback in
/// `check_predicate_in_kb_typed` (and its recording twin) runs a FULL
/// recursive derivation per Cartesian combination of the arguments'
/// equivalence classes — Π|class_i| derivations per goal. Real corpora merge
/// a handful of terms; only adversarial du-merges exceed this. Past the
/// bound the verdict fallback DOWNGRADES a would-be `False` to
/// `ResourceExceeded(Depth)` (sound-but-incomplete, like a cycle cut —
/// never a wrong definitive verdict; disclosed in GUARANTEES
/// §Completeness). The cheap stored-variant CONTAINS scan
/// (`typed_fact_is_stored_with_equivalence`) is deliberately unbounded:
/// O(1) per combo, and truncating it could return a wrong `false`.
const DU_VARIANT_BOUND: usize = 256;

/// Simple cartesian product iterator over Vec<Vec<T>>.
struct CartesianProduct<'a> {
    sets: &'a [Vec<GroundTerm>],
    indices: Vec<usize>,
    done: bool,
}

impl<'a> CartesianProduct<'a> {
    fn new(sets: &'a [Vec<GroundTerm>]) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
        }
    }
}

impl Iterator for CartesianProduct<'_> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Vec<GroundTerm>> {
        if self.done {
            return None;
        }
        let result: Vec<GroundTerm> = self
            .indices
            .iter()
            .enumerate()
            .map(|(i, &idx)| self.sets[i][idx].clone())
            .collect();

        // Advance indices (rightmost first).
        let mut carry = true;
        for i in (0..self.sets.len()).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] < self.sets[i].len() {
                    carry = false;
                } else {
                    self.indices[i] = 0;
                }
            }
        }
        if carry {
            self.done = true;
        }
        Some(result)
    }
}

/// Re-establish the descending-priority order of a single `universal_rules`
/// bucket. Call after any mutation that pushes a rule or changes a priority
/// (`register_rule`, `set_rule_priority`). `sort_by_key` is stable, so
/// equal-priority rules keep insertion order. This is the cold-path counterpart
/// to `matching_rules_typed`'s hot-path borrow: the sort lives here, at mutation
/// time, instead of on every backward-chaining node visit.
pub(super) fn sort_rule_bucket(bucket: &mut [Arc<UniversalRuleRecord>]) {
    bucket.sort_by_key(|r| std::cmp::Reverse(r.priority));
}

/// Borrow the rules whose conclusion templates match the given fact's relation
/// name, as a pre-sorted (descending priority) slice. Buckets are kept sorted at
/// mutation time (see `sort_rule_bucket`), so this is a zero-cost borrow — no
/// clone, no per-call sort — on the backward-chaining hot path.
pub(super) fn matching_rules_typed<'a>(
    fact: &StoredFact,
    universal_rules: &'a HashMap<String, Vec<Arc<UniversalRuleRecord>>>,
) -> &'a [Arc<UniversalRuleRecord>] {
    let rules = universal_rules
        .get(fact.relation())
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    debug_assert!(
        rules.is_sorted_by_key(|r| std::cmp::Reverse(r.priority)),
        "universal_rules bucket must be kept descending-sorted by priority"
    );
    rules
}

/// Check if a typed fact holds in the KB (direct assertion or backward-chaining).
pub(super) fn check_predicate_in_kb_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    // Cooperative cancellation: once the watchdog raises the flag, collapse every
    // predicate sub-check to False immediately so a candidates² backward-chaining
    // blowup unwinds in bounded time. Returns before any cache write, so no
    // cancelled verdict is memoized. The Result-returning callers (check_formula_
    // holds / _traced) convert the raised flag into the final `Err`.
    if check_cancelled(inner).is_err() {
        return QueryResult::False;
    }
    // Interactive trace: print when a traced predicate is encountered.
    let is_traced = inner.traced_predicates.contains(fact.relation());
    if is_traced {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} check: {}",
            indent,
            depth,
            fact.to_display_string()
        );
    }

    // du reflexivity + transitivity: du(x,x) always holds; du(a,b) holds
    // if a and b are in the same equivalence class.
    if fact.relation() == nibli_types::relations::IDENTITY {
        let args = &fact.inner().args;
        if args.len() == 2 {
            if args[0] == args[1] {
                return QueryResult::True; // Reflexivity
            }
            if !inner.equivalence_parent.is_empty() {
                let canon_a = canonical_witness_term(&inner.equivalence_parent, &args[0]);
                let canon_b = canonical_witness_term(&inner.equivalence_parent, &args[1]);
                if canon_a == canon_b {
                    return QueryResult::True; // Symmetry + transitivity
                }
            }
        }
    }

    if typed_fact_is_stored(fact, inner) {
        return QueryResult::True;
    }
    if activation_is_being_traced(fact, inner) {
        inner
            .cycle_cut_epoch
            .set(inner.cycle_cut_epoch.get().wrapping_add(1));
        return QueryResult::Unknown(UnknownReason::CycleCut);
    }
    if witness_activation_evidence(fact, inner).is_some() {
        return QueryResult::True;
    }
    let cached = if inner.pred_cache_enabled.get() {
        inner.pred_cache.borrow().get(fact).cloned()
    } else {
        None
    };
    if let Some(result) = cached {
        return result;
    }
    // SOUND DEPTH-CUT TABLE lookup (budget monotonicity): if this goal is
    // KNOWN to exhaust a remaining budget of at least `remaining` without
    // deciding, re-deriving it here cannot do better — less (or equal)
    // budget can never prove more, and a definitive False would need an
    // exhaustive search a smaller budget cuts even earlier. This is what
    // stops iterative deepening re-deriving every horizon-cut subgoal on
    // every occurrence and every pass (the deep-chain cliff).
    //
    // The lookup must NOT preempt the cycle guard: a goal already on the
    // `visited` stack has to yield `Unknown(CycleCut)` (which TERMINATES
    // deepening) — replaying a Depth entry there would flip the final
    // verdict class of recursive programs to `ResourceExceeded`.
    let remaining = inner.max_chain_depth.saturating_sub(depth);
    if inner.pred_cache_enabled.get()
        && !visited.contains(&cycle_key(fact))
        && inner
            .depth_cut_table
            .borrow()
            .get(fact)
            .is_some_and(|&r| r >= remaining)
    {
        return QueryResult::ResourceExceeded(ResourceKind::Depth);
    }
    let epoch_before = inner.cycle_cut_epoch.get();
    let mut result = try_backward_chain_typed(fact, inner, depth, visited);

    // If backward chaining failed, try equivalence variants.
    //
    // This fallback recurses through `check_predicate_in_kb_typed`. Without a
    // cycle guard it loops forever: `try_backward_chain_typed` removes its own
    // `visited` entry before returning, so by the time we get here `fact` is no
    // longer in `visited`, and checking an equivalence variant can regenerate
    // `fact` (du(a,b) makes `a` and `b` mutually substitutable). Asserting du(a,b)
    // then querying an unprovable predicate about `b` would otherwise stack-
    // overflow: `P(b)` → variant `P(a)` → variant `P(b)` → … .
    //
    // Cut the cycle with the shared `visited` set: re-insert `fact` for the
    // duration of the variant search and skip any variant already on the stack.
    // The recursion keeps the SAME `depth` (the variant is a lateral equality
    // rewrite, not a deeper proof step) so iterative deepening is unaffected —
    // gating this on `depth + 1 < max_chain_depth` would wrongly let a shallow
    // pass return a definitive (and cacheable) False before the fallback ever
    // runs. `visited` is removed by the inner backward chainer for the variant's
    // own derivation, but `fact` itself stays guarded until the loop ends.
    if !result.is_true()
        && !inner.equivalence_parent.is_empty()
        && fact.relation() != nibli_types::relations::IDENTITY
        && !visited.contains(&cycle_key(fact))
    {
        let gf = fact.inner();
        let equiv_args: Vec<Vec<GroundTerm>> = gf
            .args
            .iter()
            .map(|arg| {
                get_equivalence_class_readonly(
                    &inner.equivalence_parent,
                    &inner.equivalence_classes,
                    arg,
                )
            })
            .collect();
        if equiv_args.iter().any(|cls| cls.len() > 1) {
            // Guard against re-deriving `fact` itself while exploring its
            // equivalence variants. Inserted here (not by the inner backward
            // chainer, which removes its own entry on return).
            let reinserted = visited.insert(cycle_key(fact));
            // Each variant costs a FULL recursive derivation, so the total
            // fan-out over big du-merged classes is bounded by a SHARED
            // budget: the outermost fallback owns it; probes' own nested
            // fallbacks (whose class product is the SAME as ours — variants
            // are combos of the same classes) drain it rather than
            // re-enumerating multiplicatively. The truncation downgrade
            // below keeps the cut sound (GUARANTEES §Completeness).
            let owns_budget = inner.du_variant_budget.get().is_none();
            if owns_budget {
                inner.du_variant_budget.set(Some(DU_VARIANT_BOUND));
            }
            let mut truncated = false;
            for combo in CartesianProduct::new(&equiv_args) {
                match inner.du_variant_budget.get() {
                    Some(0) | None => {
                        truncated = true;
                        break;
                    }
                    Some(b) => inner.du_variant_budget.set(Some(b - 1)),
                }
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact && !visited.contains(&cycle_key(&variant)) {
                    let variant_result =
                        check_predicate_in_kb_typed(&variant, inner, depth, visited);
                    result = combine_disjunction(result, variant_result);
                    if result.is_true() {
                        break;
                    }
                }
            }
            if owns_budget {
                inner.du_variant_budget.set(None);
            }
            // Only remove `fact` if WE inserted it (don't clobber an entry an
            // outer frame is relying on for its own cycle guard).
            if reinserted {
                visited.remove(&cycle_key(fact));
            }
            // SOUND TRUNCATION: an unexplored variant could still prove the
            // goal, so a `False` past the bound would be a WRONG definitive
            // verdict (and would poison the pred_cache). Downgrade to the
            // sound-but-incomplete resource verdict instead — the same class
            // as a cycle cut.
            if truncated && !result.is_true() {
                result =
                    combine_disjunction(result, QueryResult::ResourceExceeded(ResourceKind::Depth));
            }
        }
    }

    if is_traced {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} result: {} → {}",
            indent,
            depth,
            fact.to_display_string(),
            result.status_label()
        );
    }

    // Only cache definitive (True/False) results in the verdict cache.
    // Non-definitive results (Unknown(CycleCut), ResourceExceeded(Depth)) are
    // context-dependent — they depend on the current `visited` stack and
    // `max_chain_depth` — so caching them keyed by fact alone would poison
    // sibling branches and later, deeper iterative-deepening passes.
    // True/False are context-independent for a fixed KB.
    //
    // A Depth cut, however, IS soundly tabulable when keyed by the REMAINING
    // BUDGET it exhausted (budget monotonicity — see the lookup above),
    // provided its subtree saw no cycle cut (epoch unchanged ⇒ the verdict is
    // path-independent). CycleCut itself stays untabled.
    if inner.pred_cache_enabled.get() {
        if result.is_definitive() {
            inner
                .pred_cache
                .borrow_mut()
                .insert(fact.clone(), result.clone());
        } else if matches!(result, QueryResult::ResourceExceeded(ResourceKind::Depth))
            && inner.cycle_cut_epoch.get() == epoch_before
        {
            let mut table = inner.depth_cut_table.borrow_mut();
            let entry = table.entry(fact.clone()).or_insert(0);
            if remaining > *entry {
                *entry = remaining;
            }
        }
    }
    result
}

/// Check if a StoredFact contains a specific pattern variable.
fn stored_fact_contains_var(fact: &StoredFact, var: &str) -> bool {
    fn term_contains_var(term: &GroundTerm, var: &str) -> bool {
        match term {
            GroundTerm::PatternVar(name) => name == var,
            GroundTerm::SkolemFn(_, dep) => term_contains_var(dep, var),
            GroundTerm::DepPair(a, b) => term_contains_var(a, var) || term_contains_var(b, var),
            _ => false,
        }
    }
    fact.inner().args.iter().any(|a| term_contains_var(a, var))
}

/// Sound one-step provability lookahead used at the depth horizon: a goal can
/// only be proved by (a) direct assertion (the caller checks that before
/// backward chaining) or (b) firing a rule whose conclusion template unifies
/// with it in the same exact flavor. If no conclusion unifies, no amount of
/// extra depth can ever prove the goal.
fn any_rule_conclusion_unifies(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    inner
        .universal_rules
        .get(fact.relation())
        .is_some_and(|rules| {
            rules.iter().any(|r| {
                r.typed_conclusions
                    .iter()
                    .any(|c| unify_facts_with_witness_congruence(c, fact, inner).is_some())
            })
        })
}

/// Typed backward-chaining — structural matching instead of fact_repr tokenization.
/// Narrow the candidate set for one unbound event variable by its single-event-var
/// conditions, BEFORE the full combo enumeration. Unifies the candidate filter that
/// was duplicated (and divergent) across the traced and untraced paths:
/// index-decidable conditions are checked first
/// and definitively (`typed_fact_is_stored`, no depth penalty); rule-backed
/// conditions fall through to a recursive check kept unless DEFINITIVELY false
/// (a non-definitive verdict near the depth horizon conservatively keeps the
/// candidate). Negated conditions are inverted (NAF). A condition still carrying
/// an unbound individual `x__` var is NOT pruned on — it is bound later by the
/// index-anchored join. Every condition keeps the exact flavor stored in the rule.
#[allow(clippy::too_many_arguments)]
fn filter_event_candidates(
    rule: &UniversalRuleRecord,
    ev_var: &str,
    bindings: &HashMap<String, GroundTerm>,
    single_var_cond_indices: &[usize],
    candidates: &[GroundTerm],
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> Vec<GroundTerm> {
    let (decidable_indices, recursive_indices): (Vec<usize>, Vec<usize>) =
        single_var_cond_indices.iter().copied().partition(|&idx| {
            condition_is_index_decidable(rule.typed_conditions[idx].relation(), inner)
        });
    candidates
        .iter()
        .filter(|candidate| {
            let mut tb = bindings.clone();
            tb.insert(ev_var.to_string(), (*candidate).clone());
            decidable_indices.iter().all(|&idx| {
                let cs = substitute_fact(&rule.typed_conditions[idx], &tb);
                if fact_has_unbound_pattern_var(&cs) {
                    return true;
                }
                let stored = typed_fact_is_stored(&cs, inner);
                if rule.negated_condition_indices.contains(&idx) {
                    !stored
                } else {
                    stored
                }
            }) && recursive_indices.iter().all(|&idx| {
                let cs = substitute_fact(&rule.typed_conditions[idx], &tb);
                if fact_has_unbound_pattern_var(&cs) {
                    return true;
                }
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                let verdict = if rule.negated_condition_indices.contains(&idx) {
                    negate_result_tracked(result, inner)
                } else {
                    result
                };
                !verdict.is_false()
            })
        })
        .cloned()
        .collect()
}

enum EventBindingSearch {
    Found,
    Exhausted(Option<QueryResult>),
}

/// Complete candidate set for one still-unbound rule event under the bindings
/// established by earlier join steps. Positive single-event conditions are
/// mandatory anchors; conditions containing another still-unbound event cannot
/// constrain this step yet. Recursive predicates conservatively keep every
/// non-definitive candidate, exactly like the former pre-Cartesian filter.
#[allow(clippy::too_many_arguments)]
fn event_candidates_under_bindings(
    rule: &UniversalRuleRecord,
    ev_var: &str,
    event_vars: &[String],
    bindings: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
) -> Vec<GroundTerm> {
    let single_var_cond_indices: Vec<usize> = rule
        .typed_conditions
        .iter()
        .enumerate()
        .filter(|(_, condition)| {
            stored_fact_contains_var(condition, ev_var)
                && event_vars.iter().all(|other| {
                    other == ev_var
                        || bindings.contains_key(other.as_str())
                        || !stored_fact_contains_var(condition, other)
                })
        })
        .map(|(idx, _)| idx)
        .collect();

    if single_var_cond_indices.is_empty() {
        return ensure_candidates(candidates_slot, inner).to_vec();
    }

    // Negated conditions cannot anchor: a witness for `~P(ev)` need not occur in
    // P's extension. Every positive condition is substituted with the individual
    // and earlier-event bindings accumulated by the left-deep join.
    let positive_conditions: Vec<StoredFact> = single_var_cond_indices
        .iter()
        .copied()
        .filter(|idx| !rule.negated_condition_indices.contains(idx))
        .map(|idx| substitute_fact(&rule.typed_conditions[idx], bindings))
        .collect();
    let candidates = collect_group_event_candidates(&positive_conditions, ev_var, inner)
        .unwrap_or_else(|| ensure_candidates(candidates_slot, inner).to_vec());
    filter_event_candidates(
        rule,
        ev_var,
        bindings,
        &single_var_cond_indices,
        &candidates,
        inner,
        depth,
        visited,
    )
}

/// Cheap, semantics-neutral priority for the next event in a left-deep rule join.
///
/// Candidate generation can include rule-derived Skolem families, so doing it for
/// *every* remaining event merely to discover the narrowest vector recreates the
/// eager-product cost this join is meant to avoid. Rank instead from already-ground
/// sibling arguments and their direct index buckets, then generate candidates only
/// for the selected event. The rank changes search order, never the candidate set.
fn event_join_priority(
    rule: &UniversalRuleRecord,
    ev_var: &str,
    event_vars: &[String],
    bindings: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
) -> (bool, usize, usize) {
    fn is_selective_ground(term: &GroundTerm) -> bool {
        match term {
            GroundTerm::PatternVar(_)
            | GroundTerm::SkolemPlaceholder(_)
            | GroundTerm::Unspecified => false,
            GroundTerm::SkolemFn(_, dependency) => is_selective_ground(dependency),
            GroundTerm::DepPair(left, right) => {
                is_selective_ground(left) && is_selective_ground(right)
            }
            _ => true,
        }
    }

    // Equality expansion deliberately disables sibling filtering in the exact
    // candidate collector. Do not pretend those siblings are selective here.
    if !inner.equivalence_parent.is_empty() {
        return (false, 0, usize::MAX);
    }

    let mut impossible = false;
    let mut best_grounded = 0usize;
    let mut best_indexed = usize::MAX;

    for (idx, condition) in rule.typed_conditions.iter().enumerate() {
        if rule.negated_condition_indices.contains(&idx)
            || !stored_fact_contains_var(condition, ev_var)
            || event_vars.iter().any(|other| {
                other != ev_var
                    && !bindings.contains_key(other.as_str())
                    && stored_fact_contains_var(condition, other)
            })
        {
            continue;
        }

        let substituted = substitute_fact(condition, bindings);
        let fact = substituted.inner();
        if is_non_indexable_relation(&fact.relation) {
            continue;
        }
        let event_positions: Vec<usize> = fact
            .args
            .iter()
            .enumerate()
            .filter(|(_, arg)| matches!(arg, GroundTerm::PatternVar(name) if name == ev_var))
            .map(|(position, _)| position)
            .collect();
        if event_positions.len() != 1 {
            continue;
        }
        let event_position = event_positions[0];
        let grounded_positions: Vec<usize> = fact
            .args
            .iter()
            .enumerate()
            .filter(|(position, arg)| *position != event_position && is_selective_ground(arg))
            .map(|(position, _)| position)
            .collect();
        if grounded_positions.is_empty() {
            continue;
        }

        let smallest_bucket = grounded_positions
            .iter()
            .map(|position| {
                inner
                    .arg_position_index
                    .get(&(fact.relation.clone(), *position))
                    .and_then(|by_value| by_value.get(&fact.args[*position]))
                    .map_or(0, Vec::len)
            })
            .min()
            .unwrap_or(0);
        if smallest_bucket == 0 && condition_is_index_decidable(&fact.relation, inner) {
            impossible = true;
        }

        // A rule can add witnesses absent from the direct index, so zero is not
        // an emptiness proof for a rule-derived relation. Keep it as an unknown
        // (worst) estimate; the exact collector remains authoritative.
        let indexed_estimate =
            if smallest_bucket == 0 && inner.universal_rules.contains_key(fact.relation.as_str()) {
                usize::MAX
            } else {
                smallest_bucket
            };
        if grounded_positions.len() > best_grounded
            || (grounded_positions.len() == best_grounded && indexed_estimate < best_indexed)
        {
            best_grounded = grounded_positions.len();
            best_indexed = indexed_estimate;
        }
    }

    (impossible, best_grounded, best_indexed)
}

fn event_priority_is_better(
    candidate: (bool, usize, usize),
    current: (bool, usize, usize),
) -> bool {
    candidate.0 && !current.0
        || candidate.0 == current.0
            && (candidate.1 > current.1 || candidate.1 == current.1 && candidate.2 < current.2)
}

/// Lazy positive fallback for a rule antecedent that is exactly one projectable
/// event-decomposed atom. It is attempted only after ordinary event search was
/// non-definitive, so cheap indexed proofs stay on the backward-chaining path.
/// A complete materialised extension is an exact verdict; refusal or an
/// unprojectable/flavoured/multi-atom antecedent returns `None` and preserves the
/// original search result.
fn materialized_positive_rule_conditions(
    rule: &UniversalRuleRecord,
    bindings: &HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
) -> Option<bool> {
    if !inner.materialization
        || !inner.positive_lookup.get()
        || !rule.negated_condition_indices.is_empty()
        || !rule.negated_exists_groups.is_empty()
    {
        return None;
    }
    let (relation, tuple) =
        crate::materialize::probe_positive_rule_conditions(&rule.typed_conditions, bindings)?;
    let targets = HashSet::from([relation.clone()]);
    crate::materialize::ensure_materialized_targets(inner, &targets);
    let materialized = inner.materialized.borrow();
    let materialized = materialized.as_ref()?;
    materialized
        .is_complete_for(&relation, tuple.len())
        .then(|| materialized.contains(&relation, &tuple))
}

/// Deterministic left-deep event join for one rule firing. The former path built
/// every event's candidates independently, crossed the vectors, and only then
/// propagated shared role variables. Here each chosen event binds its indexed
/// roles before the next candidate set is computed. A cheap index estimate chooses
/// one remaining event before its complete candidate set is generated; original
/// pattern-variable order breaks ties.
///
/// A successful branch deliberately leaves its event and join bindings installed
/// for the caller's final flavor-exact condition check and proof emission. Every
/// failed branch restores exactly what it introduced.
#[allow(clippy::too_many_arguments)]
fn search_event_bindings(
    rule: &UniversalRuleRecord,
    event_vars: &[String],
    bindings: &mut HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
) -> EventBindingSearch {
    let remaining: Vec<&String> = event_vars
        .iter()
        .filter(|event_var| !bindings.contains_key(event_var.as_str()))
        .collect();
    if remaining.is_empty() {
        note_rule_event_search_leaf_attempt();
        let mut all_hold = true;
        let mut pending = None;
        for (idx, condition) in rule.typed_conditions.iter().enumerate() {
            let substituted = substitute_fact(condition, bindings);
            let result = check_predicate_in_kb_typed(&substituted, inner, depth + 1, visited);
            let verdict = if rule.negated_condition_indices.contains(&idx) {
                negate_result_tracked(result, inner)
            } else {
                result
            };
            if verdict.is_false() {
                all_hold = false;
                pending = None;
                break;
            }
            if !verdict.is_true() {
                all_hold = false;
                pending = prefer_non_definitive(pending, verdict);
            }
        }
        fold_negated_groups(
            rule,
            bindings,
            inner,
            candidates_slot,
            depth,
            visited,
            &mut all_hold,
            &mut pending,
        );
        return if all_hold {
            EventBindingSearch::Found
        } else {
            EventBindingSearch::Exhausted(pending)
        };
    }

    let mut selected = remaining[0];
    let mut selected_priority = event_join_priority(rule, selected, event_vars, bindings, inner);
    for event_var in remaining.into_iter().skip(1) {
        let priority = event_join_priority(rule, event_var, event_vars, bindings, inner);
        if event_priority_is_better(priority, selected_priority) {
            selected = event_var;
            selected_priority = priority;
        }
    }
    let event_var = selected;
    let candidates = event_candidates_under_bindings(
        rule,
        event_var,
        event_vars,
        bindings,
        inner,
        depth,
        visited,
        candidates_slot,
    );
    if candidates.is_empty() {
        return EventBindingSearch::Exhausted(None);
    }

    let mut pending = None;
    for candidate in candidates {
        if inner
            .cancel
            .as_ref()
            .is_some_and(|cancel| cancel.load(std::sync::atomic::Ordering::Relaxed))
        {
            break;
        }
        bindings.insert(event_var.clone(), candidate);
        let joined_vars = bind_join_vars_from_index(rule, bindings, inner);
        match search_event_bindings(
            rule,
            event_vars,
            bindings,
            inner,
            depth,
            visited,
            candidates_slot,
        ) {
            EventBindingSearch::Found => return EventBindingSearch::Found,
            EventBindingSearch::Exhausted(branch_pending) => {
                if let Some(result) = branch_pending {
                    pending = prefer_non_definitive(pending, result);
                }
            }
        }
        bindings.remove(event_var.as_str());
        for joined_var in joined_vars {
            bindings.remove(joined_var.as_str());
        }
    }
    EventBindingSearch::Exhausted(pending)
}

/// Activate a generated individual only after its own rule body succeeds.
/// Candidate construction is not existence evidence. Reuse the ordinary
/// flavor-aware join and NAF evaluator, with the same depth/cancellation limits.
pub(super) fn witness_activation_holds(
    rule: &UniversalRuleRecord,
    bindings: &mut HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
) -> QueryResult {
    // A missing tuple in an already-complete condition needs no event search.
    // Positive matches still bind event witnesses through the ordinary path.
    // Do not request new saturation here: recursive/unsupported conditions keep
    // the ordinary evaluator, and proof tracing keeps its derivation path.
    if inner.positive_lookup.get()
        && inner.materialization
        && rule.negated_condition_indices.is_empty()
        && rule.negated_exists_groups.is_empty()
    {
        if let Some((relation, tuple)) =
            crate::materialize::probe_positive_rule_conditions(&rule.typed_conditions, bindings)
        {
            let materialized = inner.materialized.borrow();
            if let Some(complete) = materialized.as_ref() {
                if complete.is_complete_for(&relation, tuple.len())
                    && !complete.contains(&relation, &tuple)
                {
                    return QueryResult::False;
                }
            }
        }
    }
    let event_vars: Vec<String> = rule
        .pattern_var_names
        .iter()
        .filter(|name| name.starts_with("ev__") && !bindings.contains_key(*name))
        .cloned()
        .collect();
    match search_event_bindings(
        rule,
        &event_vars,
        bindings,
        inner,
        0,
        &mut HashSet::new(),
        &mut None,
    ) {
        EventBindingSearch::Found => QueryResult::True,
        EventBindingSearch::Exhausted(Some(QueryResult::ResourceExceeded(ResourceKind::Depth)))
            if inner.positive_lookup.get() =>
        {
            match materialized_positive_rule_conditions(rule, bindings, inner) {
                Some(true) => QueryResult::True,
                Some(false) => QueryResult::False,
                None => QueryResult::ResourceExceeded(ResourceKind::Depth),
            }
        }
        EventBindingSearch::Exhausted(pending) => pending.unwrap_or(QueryResult::False),
    }
}

/// Poisoned index returned by [`push_proof_step`] past the cap. Reserved:
/// legal indices stop at `u32::MAX - 1`, so the sentinel can never collide
/// with a real step.
pub(super) const PROOF_STEP_SENTINEL: u32 = u32::MAX;

#[cfg(test)]
thread_local! {
    /// Test-only cap override, so a unit test can exercise the overflow
    /// contract without allocating 2^32 steps (reasoning tests run
    /// single-threaded; tests use an RAII reset so a panic cannot leak the cap).
    pub(super) static TEST_MAX_PROOF_STEPS: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

pub(super) fn max_proof_steps() -> usize {
    #[cfg(test)]
    if let Some(cap) = TEST_MAX_PROOF_STEPS.with(|c| c.get()) {
        return cap;
    }
    u32::MAX as usize
}

/// The ONE place a proof step gains its index — every sink and tracer push
/// routes here. `ProofStep.children` crosses the WIT boundary as `list<u32>`,
/// so an index must fit in `u32`, and the former bare `as` cast on a larger
/// length would WRAP into a valid-looking back-reference: a silently corrupt
/// certificate, the worst failure a proof surface can have. Past the cap
/// nothing is recorded and the sentinel returns; the single trace assembly
/// site checks [`proof_steps_overflowed`] and refuses the WHOLE trace, so a
/// poisoned index can never escape. In production the cap is unreachable (a
/// four-billion-step trace exhausts memory first) — the guard exists so the
/// CONTRACT fails closed rather than by accident of OOM.
pub(super) fn push_proof_step(steps: &mut Vec<ProofStep>, step: ProofStep) -> u32 {
    if steps.len() >= max_proof_steps() {
        return PROOF_STEP_SENTINEL;
    }
    let idx = steps.len() as u32;
    steps.push(step);
    idx
}

/// Assembly-time overflow check: poisoned pushes never grow the vec, so a
/// steps vec AT the cap either overflowed or filled it exactly — both refuse
/// (one index of slack, since the sentinel reserves `u32::MAX`).
pub(super) fn proof_steps_overflowed(steps: &[ProofStep]) -> bool {
    steps.len() >= max_proof_steps()
}

/// Trace sink: a compile-time switch between the untraced verdict path
/// (`NoOpSink`) and the proof-recording path (`RecordingSink`), so the single
/// backward-chain core serves both. `RECORDING` MUST stay an associated `const`
/// (never a method): each `if S::RECORDING { … }` is then constant-folded per
/// monomorphization and the dead arm eliminated, so the untraced hot path takes
/// no indirect call and records nothing. Turning it into a method would
/// reintroduce indirect-call overhead on the reasoning hot path.
trait TraceSink {
    const RECORDING: bool;
    /// Push a proof step, returning its index. `NoOpSink` returns 0 (never read).
    fn push(&mut self, step: ProofStep) -> u32;
    /// Record a proven positive condition's provenance, returning its step
    /// index. Re-enters `trace_predicate_provenance_typed` on the recording
    /// path; the shared `visited` keeps its cycle guard consistent with the
    /// verdict walk. `NoOpSink` returns 0.
    fn trace_child(
        &mut self,
        fact: &StoredFact,
        inner: &KnowledgeBaseInner,
        depth: usize,
        visited: &mut HashSet<StoredFact>,
    ) -> u32;
}

/// Zero-sized untraced sink. Both methods inline to nothing; every recording
/// branch guarded by `S::RECORDING` is dead-code-eliminated for this type.
struct NoOpSink;
impl TraceSink for NoOpSink {
    const RECORDING: bool = false;
    #[inline(always)]
    fn push(&mut self, _step: ProofStep) -> u32 {
        0
    }
    #[inline(always)]
    fn trace_child(
        &mut self,
        _fact: &StoredFact,
        _inner: &KnowledgeBaseInner,
        _depth: usize,
        _visited: &mut HashSet<StoredFact>,
    ) -> u32 {
        0
    }
}

/// Recording sink: borrows the proof-step vec + memo, re-entering the typed
/// provenance tracer for each proven child derivation.
struct RecordingSink<'a> {
    steps: &'a mut Vec<ProofStep>,
    memo: &'a mut HashMap<StoredFact, u32>,
}
impl TraceSink for RecordingSink<'_> {
    const RECORDING: bool = true;
    fn push(&mut self, step: ProofStep) -> u32 {
        push_proof_step(self.steps, step)
    }
    fn trace_child(
        &mut self,
        fact: &StoredFact,
        inner: &KnowledgeBaseInner,
        depth: usize,
        visited: &mut HashSet<StoredFact>,
    ) -> u32 {
        trace_predicate_provenance_typed(fact, inner, self.steps, depth, self.memo, visited)
    }
}

/// Resolve one active assertion record into the public, stable citation shape.
/// Rebuild keeps retracted records for ID stability, so provenance must filter
/// them rather than assuming every registry entry is live.
fn assertion_citation(inner: &KnowledgeBaseInner, assertion_id: u64) -> Option<AssertionCitation> {
    let record = inner.fact_registry.get(&assertion_id)?;
    (!record.retracted).then(|| AssertionCitation {
        id: record.id,
        label: record.label.clone(),
    })
}

fn assertion_citations(
    inner: &KnowledgeBaseInner,
    assertion_ids: impl IntoIterator<Item = u64>,
) -> Vec<AssertionCitation> {
    let mut citations: Vec<_> = assertion_ids
        .into_iter()
        .filter_map(|id| assertion_citation(inner, id))
        .collect();
    citations.sort_by_key(|citation| citation.id);
    citations.dedup_by_key(|citation| citation.id);
    citations
}

fn rule_citation(inner: &KnowledgeBaseInner, source: RuleSourceId) -> Option<RuleCitation> {
    let assertion = assertion_citation(inner, source.assertion_id)?;
    Some(RuleCitation {
        assertion_id: assertion.id,
        rule_ordinal: source.local_ordinal,
        assertion_label: assertion.label,
    })
}

fn rule_citations(inner: &KnowledgeBaseInner, identity: &RuleIdentity) -> Vec<RuleCitation> {
    inner
        .known_rules
        .source_ids(identity)
        .unwrap_or_default()
        .iter()
        .copied()
        .filter_map(|source| rule_citation(inner, source))
        .collect()
}

fn rule_label(inner: &KnowledgeBaseInner, identity: &RuleIdentity) -> Option<String> {
    inner
        .universal_rules
        .values()
        .flat_map(|rules| rules.iter())
        .find(|rule| rule.identity.as_ref() == identity)
        .map(|rule| rule.label.clone())
}

fn rule_label_for_source(inner: &KnowledgeBaseInner, source: RuleSourceId) -> Option<String> {
    inner
        .universal_rules
        .values()
        .flat_map(|rules| rules.iter())
        .find(|rule| {
            inner
                .known_rules
                .source_ids(rule.identity.as_ref())
                .is_some_and(|sources| sources.contains(&source))
        })
        .map(|rule| rule.label.clone())
}

/// Build the `Derived` proof step for a rule that fired, recording each
/// condition's provenance as a child (a `Negation` leaf for a NAF-negated
/// condition, otherwise the positive atom's full derivation via the sink).
/// Called ONLY on the recording path (`S::RECORDING`). All conditions are known
/// to hold (the four-valued verdict loop just confirmed it), so no re-check/break
/// is needed here.
#[allow(clippy::too_many_arguments)]
fn emit_derived<S: TraceSink>(
    sink: &mut S,
    rule: &UniversalRuleRecord,
    bindings: &HashMap<String, GroundTerm>,
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> u32 {
    let display = fact.to_display_string();
    let mut child_indices = Vec::new();
    for (idx, cond_template) in rule.typed_conditions.iter().enumerate() {
        let cond_fact = substitute_fact(cond_template, bindings);
        if rule.negated_condition_indices.contains(&idx) {
            let leaf = sink.push(ProofStep {
                rule: ProofRule::Negation,
                holds: true,
                children: vec![],
            });
            child_indices.push(leaf);
        } else {
            let child = sink.trace_child(&cond_fact, inner, depth + 1, visited);
            child_indices.push(child);
        }
    }
    // A satisfied negated-exists group (`poi na <predicate>`) held by negation-as-
    // failure (no witness), so the conclusion rests on a NAF dependency — emit one
    // `Negation` leaf per group, mirroring the flat-negated-condition leaf above.
    for _group in &rule.negated_exists_groups {
        let leaf = sink.push(ProofStep {
            rule: ProofRule::Negation,
            holds: true,
            children: vec![],
        });
        child_indices.push(leaf);
    }
    let instantiated = rule
        .typed_conclusions
        .iter()
        .map(|template| substitute_fact(template, bindings))
        .find(|head| {
            head == fact || unify_facts_with_witness_congruence(head, fact, inner).is_some()
        })
        .unwrap_or_else(|| fact.clone());
    let root = sink.push(ProofStep {
        rule: ProofRule::Derived {
            label: rule.label.clone(),
            fact: instantiated.to_display_string(),
            sources: rule_citations(inner, rule.identity.as_ref()),
        },
        holds: true,
        children: child_indices,
    });
    if instantiated == *fact {
        return root;
    }
    let Some(equalities) = equality_support_facts(fact, &instantiated, inner) else {
        return root;
    };
    let mut children = vec![root];
    for equality in equalities {
        children.push(sink.trace_child(&equality, inner, depth, visited));
    }
    sink.push(ProofStep {
        rule: ProofRule::EqualitySubstitution {
            original: display,
            equality_facts: equals_substitution_note(fact, &instantiated),
            substituted: instantiated.to_display_string(),
        },
        holds: true,
        children,
    })
}

/// Typed backward-chaining core — the single rule-firing enumeration shared by
/// the untraced verdict path (`S = NoOpSink`) and the proof-recording path
/// (`S = RecordingSink`). The four-valued accumulation and the shared `visited`
/// cycle-cut run UNCONDITIONALLY, so the returned `QueryResult` is authoritative
/// and identical to the former `try_backward_chain_typed`; proof steps are
/// emitted only when `S::RECORDING`, and the second tuple field is the index of
/// the `Derived` step proving the goal (`Some` only when recording AND a rule
/// fired). Sharing `visited` with the recording path closes the old traced-path
/// per-condition cycle asymmetry (LP-L2).
///
/// Run the per-rule firing loop for `match_fact`. Rule conclusions and conditions
/// retain their exact Bare/Past/Present/Future flavors; there is no implicit
/// cross-flavor phase.
///
/// Returns `Some(root)` if a rule fired definitively True (the caller returns
/// `(True, root)`); `None` if no rule fired, accumulating any non-definitive
/// verdict into `*best_result`. The caller owns `visited.remove(fact)`.
fn process_phase<S: TraceSink>(
    match_fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    sink: &mut S,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
    best_result: &mut Option<QueryResult>,
) -> Option<Option<u32>> {
    let rules = matching_rules_typed(match_fact, &inner.universal_rules);
    for rule in rules {
        for typed_concl in &rule.typed_conclusions {
            let Some(mut bindings) =
                unify_facts_with_witness_congruence(typed_concl, match_fact, inner)
            else {
                continue;
            };

            // Handle unbound event variables (same logic as fact_repr version).
            let unbound_event_vars: Vec<String> = rule
                .pattern_var_names
                .iter()
                .filter(|pv| pv.starts_with("ev__") && !bindings.contains_key(pv.as_str()))
                .cloned()
                .collect();

            if !unbound_event_vars.is_empty() {
                if let EventBindingSearch::Exhausted(pending) = search_event_bindings(
                    rule,
                    &unbound_event_vars,
                    &mut bindings,
                    inner,
                    depth,
                    visited,
                    candidates_slot,
                ) {
                    if matches!(
                        pending,
                        Some(QueryResult::ResourceExceeded(ResourceKind::Depth))
                    ) && !S::RECORDING
                        && let Some(conditions_hold) =
                            materialized_positive_rule_conditions(rule, &bindings, inner)
                    {
                        if conditions_hold {
                            return Some(None);
                        }
                        continue;
                    }
                    // Merge any pending non-definitive result WITHOUT wiping an
                    // already-pending one: if every branch failed definitively,
                    // keep best_result intact.
                    if let Some(r) = pending {
                        *best_result = prefer_non_definitive(best_result.take(), r);
                    }
                    continue;
                }
            }

            let mut all_conditions_hold = true;
            let mut rule_pending = None;
            for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                let cs = substitute_fact(ct, &bindings);
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                // Negated antecedent conditions hold via negation-as-failure: invert
                // the verdict so ¬P holds iff P is unprovable (False), not iff P is True.
                let verdict = if rule.negated_condition_indices.contains(&idx) {
                    negate_result_tracked(result, inner)
                } else {
                    result
                };
                if verdict.is_false() {
                    all_conditions_hold = false;
                    rule_pending = None;
                    break;
                }
                if !verdict.is_true() {
                    all_conditions_hold = false;
                    rule_pending = prefer_non_definitive(rule_pending, verdict);
                }
            }
            fold_negated_groups(
                rule,
                &bindings,
                inner,
                candidates_slot,
                depth,
                visited,
                &mut all_conditions_hold,
                &mut rule_pending,
            );

            if all_conditions_hold {
                let root = if S::RECORDING {
                    Some(emit_derived(
                        sink, rule, &bindings, match_fact, inner, depth, visited,
                    ))
                } else {
                    None
                };
                return Some(root);
            }
            // Never wipe an already-pending non-definitive result: when
            // rule_pending is None (this rule failed definitively), leave
            // best_result intact rather than erasing it via `and_then`.
            if let Some(r) = rule_pending {
                *best_result = prefer_non_definitive(best_result.take(), r);
            }
        }
    }
    None
}

/// An engine-minted event Skolem term: a dependent `SkolemFn` (`sk_5(rex)`) or an
/// independent Skolem constant (`sk_<n>`, from [`KnowledgeBaseInner::fresh_skolem`]
/// / `rules.rs`). These vary per derivation step; collapsing them is what lets the
/// cycle guard recognize a relation-level cycle (see [`cycle_key`]).
fn is_event_skolem_term(t: &GroundTerm) -> bool {
    match t {
        GroundTerm::Skolem(symbol) | GroundTerm::SkolemFn(symbol, _) => {
            symbol.sort() == SkolemSort::Event
        }
        _ => false,
    }
}

/// Canonicalize a fact for the `visited` cycle guard. Event-decomposed reasoning
/// mints a FRESH event Skolem every time an unbound event variable is searched, so a
/// relation-level cycle through event rules
/// (`gerku(sk_5(rex)) ⟸ danlu(sk_1(rex)) ⟸ gerku(sk_5(sk_2)) ⟸ …`) never repeats an
/// exact `StoredFact`: the raw guard never fires and the search re-derives the same
/// relation exponentially out to the depth horizon (a query-level hang / DoS).
/// Collapsing every event-Skolem argument ([`is_event_skolem_term`]) to a single
/// typed sentinel makes a re-entered relation+individual goal hash-equal, so the second
/// visit on the SAME PATH is cut (`CycleCut`). Constant/individual args are preserved,
/// so distinct individuals—including equal-looking user `sk_N` text—stay distinct
/// (no over-cut of legitimate per-individual recursion). Facts with no event-Skolem
/// arg are returned unchanged (fast path) —
/// behavior is identical to the old raw key for the overwhelming majority of goals.
fn cycle_key(fact: &StoredFact) -> StoredFact {
    let gf = fact.inner();
    if !gf.args.iter().any(is_event_skolem_term) {
        return fact.clone();
    }
    let args = gf
        .args
        .iter()
        .map(|a| {
            if is_event_skolem_term(a) {
                GroundTerm::Skolem(SkolemSymbol::cycle_sentinel())
            } else {
                a.clone()
            }
        })
        .collect();
    StoredFact::with_tense_from(GroundFact::new(gf.relation.clone(), args), fact)
}

fn try_backward_chain_core<S: TraceSink>(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    sink: &mut S,
) -> (QueryResult, Option<u32>) {
    // Cancellation fast-path: unwind the recursion immediately (see
    // check_predicate_in_kb_typed). The Result-returning formula entry surfaces
    // the raised flag as the final `Err`.
    if check_cancelled(inner).is_err() {
        return (QueryResult::False, None);
    }
    if depth >= inner.max_chain_depth {
        // A goal that is not asserted (the caller already checked) and that no
        // rule conclusion can unify with is unprovable at ANY depth: return the
        // exact definitive False instead of ResourceExceeded, so the depth
        // horizon does not pessimistically keep dead candidates alive in the
        // unbound-event-variable search (the members^k cartesian blowup) — and
        // so the result becomes cacheable. Gated off for the special-cased `du`
        // relation and when du-equivalence classes exist (the equivalence
        // fallback could rewrite the goal into a provable variant). Every
        // registered rule is relation-indexed by conclusion — register_rule
        // fails closed on empty conclusions, so no unindexed bucket exists.
        if fact.relation() != nibli_types::relations::IDENTITY
            && inner.equivalence_parent.is_empty()
            && !any_rule_conclusion_unifies(fact, inner)
        {
            return (QueryResult::False, None);
        }
        return (QueryResult::ResourceExceeded(ResourceKind::Depth), None);
    }
    if !visited.insert(cycle_key(fact)) {
        // Contamination signal for the depth-cut table: a Depth verdict whose
        // subtree saw ANY cycle cut is path-dependent (an ancestor on the
        // visited stack suppressed a branch that could prove the goal
        // elsewhere) and must not be tabled — the epoch snapshot in
        // `check_predicate_in_kb_typed` detects this bump.
        inner.cycle_cut_epoch.set(inner.cycle_cut_epoch.get() + 1);
        return (QueryResult::Unknown(UnknownReason::CycleCut), None);
    }

    // Candidate terms for unbound event variable search, built lazily: only a
    // matched rule with unbound `ev__` pattern variables needs them, and most
    // frames never reach that point. Shared across all rules in this frame.
    let mut candidates_slot: Option<Vec<GroundTerm>> = None;

    let rules = matching_rules_typed(fact, &inner.universal_rules);
    let is_traced = inner.traced_predicates.contains(fact.relation());
    if is_traced && !rules.is_empty() {
        let indent = "  ".repeat(depth);
        eprintln!(
            "[Trace] {}depth={} backward-chain: {} ({} rule(s) to try)",
            indent,
            depth,
            fact.to_display_string(),
            rules.len()
        );
    }
    let mut best_result = None;

    // Rule facts are flavor-exact. A temporal or deontic goal can only match a
    // conclusion carrying that same explicit flavor; a bare rule is bare-only.
    if let Some(root) = process_phase(
        fact,
        inner,
        depth,
        visited,
        sink,
        &mut candidates_slot,
        &mut best_result,
    ) {
        visited.remove(&cycle_key(fact));
        return (QueryResult::True, root);
    }

    visited.remove(&cycle_key(fact));
    (best_result.unwrap_or(QueryResult::False), None)
}

/// Untraced backward-chaining: the verdict-only entry. Delegates to the shared
/// core with a no-op sink, so the hot path records nothing — every
/// `if S::RECORDING` branch is dead-code-eliminated for `NoOpSink`.
pub(super) fn try_backward_chain_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
) -> QueryResult {
    try_backward_chain_core(fact, inner, depth, visited, &mut NoOpSink).0
}

// ─── Typed Traced Backward-Chaining ──────────────────────────────
//
// Typed equivalents of trace_predicate_provenance() and try_backward_chain_traced()
// that use StoredFact and unify_facts() using structural unification.

/// Typed trace_predicate_provenance: check if fact holds and build proof step.
pub(super) fn trace_predicate_provenance_typed(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    steps: &mut Vec<ProofStep>,
    depth: usize,
    memo: &mut HashMap<StoredFact, u32>,
    visited: &mut HashSet<StoredFact>,
) -> u32 {
    let display = fact.to_display_string();

    if let Some(&cached_idx) = memo.get(fact) {
        // Memo hit — emit a lightweight ProofRef leaf instead of
        // re-deriving the full proof sub-tree. The original derivation
        // lives at steps[cached_idx]. We store cached_idx in children
        // so consumers can follow the back-reference if needed.
        let holds = steps[cached_idx as usize].holds;
        let idx = push_proof_step(
            steps,
            ProofStep {
                rule: ProofRule::ProofRef { fact: display },
                holds,
                children: vec![cached_idx],
            },
        );
        return idx;
    }

    // Exact store hit. Truth membership is content-only; the sidecar records
    // whether that tuple was directly asserted, eagerly derived, admitted as
    // an existential-import presupposition, or inserted only by internal test
    // support. Never infer provenance from set membership.
    if inner.fact_store.contains(fact) {
        let origins = inner.fact_origins_for(fact);
        let direct_sources = assertion_citations(
            inner,
            origins.iter().filter_map(|origin| match origin {
                StoredFactOrigin::Assertion { assertion_id } => Some(*assertion_id),
                _ => None,
            }),
        );

        if !direct_sources.is_empty() {
            let idx = push_proof_step(
                steps,
                ProofStep {
                    rule: ProofRule::Asserted {
                        fact: display.clone(),
                        sources: direct_sources,
                    },
                    holds: true,
                    children: vec![],
                },
            );
            memo.insert(fact.clone(), idx);
            return idx;
        }

        // Among non-direct supports, choose the earliest one. Every forward
        // support is appended only after its captured premises already exist;
        // following insertion order therefore strictly decreases support time
        // and cannot walk a later P↔Q support cycle. A presupposition/internal
        // leaf that predates a later forward derivation remains the primary
        // explanation. Direct assertions above are terminal and deliberately
        // take precedence regardless of insertion time.
        match origins
            .iter()
            .find(|origin| !matches!(origin, StoredFactOrigin::Assertion { .. }))
            .cloned()
        {
            Some(StoredFactOrigin::ForwardDerived {
                rule_identity: identity,
                premises,
            }) => {
                let children = premises
                    .iter()
                    .map(|premise| {
                        trace_predicate_provenance_typed(
                            premise,
                            inner,
                            steps,
                            depth + 1,
                            memo,
                            visited,
                        )
                    })
                    .collect();
                let sources = rule_citations(inner, identity.as_ref());
                let label = rule_label(inner, identity.as_ref())
                    .or_else(|| sources.first().map(|source| source.assertion_label.clone()))
                    .unwrap_or_else(|| "forward derivation".to_string());
                let idx = push_proof_step(
                    steps,
                    ProofStep {
                        rule: ProofRule::Derived {
                            label,
                            fact: display.clone(),
                            sources,
                        },
                        holds: true,
                        children,
                    },
                );
                memo.insert(fact.clone(), idx);
                return idx;
            }
            Some(StoredFactOrigin::Presupposition { rule_source }) => {
                let sources: Vec<_> = rule_citation(inner, rule_source).into_iter().collect();
                let label = rule_label_for_source(inner, rule_source)
                    .or_else(|| {
                        sources
                            .first()
                            .map(|citation| citation.assertion_label.clone())
                    })
                    .unwrap_or_else(|| "existential import".to_string());
                let idx = push_proof_step(
                    steps,
                    ProofStep {
                        rule: ProofRule::Presupposed {
                            label,
                            fact: display.clone(),
                            sources,
                        },
                        holds: true,
                        children: vec![],
                    },
                );
                memo.insert(fact.clone(), idx);
                return idx;
            }
            Some(StoredFactOrigin::Internal) | Some(StoredFactOrigin::Assertion { .. }) | None => {}
        }

        // Defensive/internal fallback. A content fact with no attributable
        // active origin may still occur in in-crate support code, but it is not
        // a user assertion and must never be serialized as one.
        let idx = push_proof_step(
            steps,
            ProofStep {
                rule: ProofRule::PredicateCheck {
                    method: "internal-store".to_string(),
                    detail: display.clone(),
                },
                holds: true,
                children: vec![],
            },
        );
        memo.insert(fact.clone(), idx);
        return idx;
    }

    if !activation_is_being_traced(fact, inner)
        && let Some(evidence) = witness_activation_evidence(fact, inner)
    {
        mark_activation_trace(fact, inner, true);
        let child = emit_derived(
            &mut RecordingSink { steps, memo },
            &evidence.rule,
            &evidence.bindings,
            &evidence.conclusion,
            inner,
            0,
            visited,
        );
        mark_activation_trace(fact, inner, false);
        let idx = if &evidence.conclusion == fact {
            child
        } else if let Some(equalities) = equality_support_facts(fact, &evidence.conclusion, inner) {
            let mut children = vec![child];
            for equality in equalities {
                children.push(trace_predicate_provenance_typed(
                    &equality,
                    inner,
                    steps,
                    depth,
                    memo,
                    &mut HashSet::new(),
                ));
            }
            push_proof_step(
                steps,
                ProofStep {
                    rule: ProofRule::EqualitySubstitution {
                        original: display.clone(),
                        equality_facts: equals_substitution_note(fact, &evidence.conclusion),
                        substituted: evidence.conclusion.to_display_string(),
                    },
                    holds: true,
                    children,
                },
            )
        } else {
            push_proof_step(
                steps,
                ProofStep {
                    rule: ProofRule::PredicateCheck {
                        method: "indeterminate".into(),
                        detail: "missing witness-congruence evidence".into(),
                    },
                    holds: false,
                    children: vec![],
                },
            )
        };
        memo.insert(fact.clone(), idx);
        return idx;
    }

    // Holds via a du-equivalent variant already in the content store → render
    // the substitution as EqualitySubstitution and let the child's origin
    // sidecar decide whether that variant is Asserted, Derived, Presupposed, or
    // Internal. A purely backward-derived equivalent variant is not in the store
    // and therefore flows to the derivation fallback further down.
    if !inner.equivalence_parent.is_empty() {
        if let Some(variant) = typed_fact_is_stored_with_equivalence(fact, inner) {
            if let Some(equality_facts) = equality_support_facts(fact, &variant, inner) {
                let equals_note = equals_substitution_note(fact, &variant);
                let substituted = variant.to_display_string();
                let child = trace_predicate_provenance_typed(
                    &variant,
                    inner,
                    steps,
                    depth,
                    memo,
                    &mut HashSet::new(),
                );
                let mut children = vec![child];
                children.extend(equality_facts.iter().map(|equality| {
                    trace_predicate_provenance_typed(
                        equality,
                        inner,
                        steps,
                        depth,
                        memo,
                        &mut HashSet::new(),
                    )
                }));
                let idx = push_proof_step(
                    steps,
                    ProofStep {
                        rule: ProofRule::EqualitySubstitution {
                            original: display.clone(),
                            equality_facts: equals_note,
                            substituted,
                        },
                        holds: true,
                        children,
                    },
                );
                memo.insert(fact.clone(), idx);
                return idx;
            }
        }
    }

    if depth < inner.max_chain_depth {
        // Fire rules via the shared core with a recording sink. `root` is `Some`
        // iff a rule fired (verdict True); a non-firing verdict (False / Unknown
        // / ResourceExceeded) returns `None` and falls through to the equality
        // fallback below — the same trigger as the former `Option<u32>` path.
        // The shared `visited` keeps the recording walk's cycle guard consistent
        // with the untraced verdict (closes LP-L2).
        let (_verdict, root) = try_backward_chain_core::<RecordingSink>(
            fact,
            inner,
            depth,
            visited,
            &mut RecordingSink { steps, memo },
        );
        if let Some(idx) = root {
            memo.insert(fact.clone(), idx);
            return idx;
        }
    }

    // Equality substitution: the fact may hold only after replacing arguments with
    // du-equivalent terms (mirrors the untraced fallback in check_predicate_in_kb_typed).
    // Find a satisfying equivalent variant and record an EqualitySubstitution step whose
    // child is the variant's real derivation — never a holds:true leaf with no support.
    // The variant probe below recurses only into `check_predicate_in_kb_typed`,
    // whose own equivalence fallback now carries a `visited` cycle guard, so the
    // probe terminates (returns a definitive verdict) for every variant. A du-
    // cycle therefore yields `satisfying = None` rather than overflowing the
    // stack, and the recursive `trace_predicate_provenance_typed` below only fires
    // for a genuinely-provable variant (which bottoms out at a sourced stored
    // fact or rule), so it terminates as well. No extra depth gate is needed here, and
    // adding one would wrongly suppress the fallback on shallow iterative-
    // deepening passes.
    if !inner.equivalence_parent.is_empty() && fact.relation() != nibli_types::relations::IDENTITY {
        let gf = fact.inner();
        let equiv_args: Vec<Vec<GroundTerm>> = gf
            .args
            .iter()
            .map(|arg| {
                get_equivalence_class_readonly(
                    &inner.equivalence_parent,
                    &inner.equivalence_classes,
                    arg,
                )
            })
            .collect();
        if equiv_args.iter().any(|cls| cls.len() > 1) {
            let mut satisfying: Option<StoredFact> = None;
            // Same shared DU_VARIANT_BOUND budget as the verdict fallback
            // (parity): a TRUE verdict's satisfying variant was found within
            // the budget of the same deterministic iteration, and its True
            // is pred_cache'd — this scan re-finds it via cache hits before
            // the budget can run out.
            let owns_budget = inner.du_variant_budget.get().is_none();
            if owns_budget {
                inner.du_variant_budget.set(Some(DU_VARIANT_BOUND));
            }
            for combo in CartesianProduct::new(&equiv_args) {
                match inner.du_variant_budget.get() {
                    Some(0) | None => break,
                    Some(b) => inner.du_variant_budget.set(Some(b - 1)),
                }
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact
                    && check_predicate_in_kb_typed(&variant, inner, depth, &mut HashSet::new())
                        .is_true()
                {
                    satisfying = Some(variant);
                    break;
                }
            }
            if owns_budget {
                inner.du_variant_budget.set(None);
            }
            if let Some(variant) = satisfying {
                if let Some(equality_facts) = equality_support_facts(fact, &variant, inner) {
                    let equals_note = equals_substitution_note(fact, &variant);
                    let substituted = variant.to_display_string();
                    let child = trace_predicate_provenance_typed(
                        &variant,
                        inner,
                        steps,
                        depth,
                        memo,
                        &mut HashSet::new(),
                    );
                    let mut children = vec![child];
                    children.extend(equality_facts.iter().map(|equality| {
                        trace_predicate_provenance_typed(
                            equality,
                            inner,
                            steps,
                            depth,
                            memo,
                            &mut HashSet::new(),
                        )
                    }));
                    let idx = push_proof_step(
                        steps,
                        ProofStep {
                            rule: ProofRule::EqualitySubstitution {
                                original: display.clone(),
                                equality_facts: equals_note,
                                substituted,
                            },
                            holds: true,
                            children,
                        },
                    );
                    memo.insert(fact.clone(), idx);
                    return idx;
                }
            }
        }
    }

    // Final fallback: the traced path could not derive the fact. Report it honestly as
    // not-found (holds:false) rather than claiming truth with no supporting derivation.
    //
    // This result is DEPTH-RELATIVE: a True-verdict fact reaches here only because the
    // recording walk hit the depth horizon (`depth >= max_chain_depth` gated out the
    // backward-chain above) before deriving it. Do NOT memoize it — mirroring the verdict
    // cache's definitive-only policy. Caching a not-found keyed by display alone would let a
    // SHALLOWER occurrence (where the fact DOES derive within budget) reuse this stale
    // `holds:false` step via a `ProofRef` — "not found (see above)" for a derivable fact.
    // Re-emitting a fresh leaf each time is strictly honest; the only cost is a few extra
    // leaves in pathological traces. With this omitted, every memo entry — and therefore
    // every `ProofRef` — points at a `holds:true` derivation.
    let idx = push_proof_step(
        steps,
        ProofStep {
            rule: ProofRule::PredicateNotFound { predicate: display },
            holds: false,
            children: vec![],
        },
    );
    idx
}

// ─── End Typed Backward-Chaining ─────────────────────────────────

#[cfg(test)]
mod combiner_tests {
    use super::*;
    use QueryResult::{False as F, True as T};

    fn unk_a() -> QueryResult {
        QueryResult::Unknown(UnknownReason::CycleCut)
    }
    fn unk_b() -> QueryResult {
        QueryResult::Unknown(UnknownReason::IncompleteKnowledge)
    }
    fn re_a() -> QueryResult {
        QueryResult::ResourceExceeded(ResourceKind::Fuel)
    }
    fn re_b() -> QueryResult {
        QueryResult::ResourceExceeded(ResourceKind::Depth)
    }

    #[test]
    fn conjunction_truth_table() {
        // Definitive / short-circuit region.
        assert_eq!(combine_conjunction(T, T), T);
        assert_eq!(combine_conjunction(F, T), F);
        assert_eq!(combine_conjunction(T, F), F);
        assert_eq!(combine_conjunction(F, unk_a()), F);
        assert_eq!(combine_conjunction(unk_a(), F), F);
        // The bug: a definitive-True operand must NOT swallow a non-definitive sibling.
        assert_eq!(combine_conjunction(T, unk_a()), unk_a());
        assert_eq!(combine_conjunction(unk_a(), T), unk_a());
        assert_eq!(combine_conjunction(T, re_a()), re_a());
        assert_eq!(combine_conjunction(re_a(), T), re_a());
        // Non-definitive precedence: RE outranks Unknown (either side); left wins ties.
        assert_eq!(combine_conjunction(unk_a(), unk_b()), unk_a());
        assert_eq!(combine_conjunction(unk_a(), re_a()), re_a());
        assert_eq!(combine_conjunction(re_a(), unk_a()), re_a());
        assert_eq!(combine_conjunction(re_a(), re_b()), re_a());
    }

    #[test]
    fn disjunction_truth_table() {
        // Definitive / short-circuit region.
        assert_eq!(combine_disjunction(F, F), F);
        assert_eq!(combine_disjunction(T, F), T);
        assert_eq!(combine_disjunction(F, T), T);
        assert_eq!(combine_disjunction(T, unk_a()), T);
        assert_eq!(combine_disjunction(unk_a(), T), T);
        // The bug: a definitive-False operand must NOT swallow a non-definitive sibling.
        assert_eq!(combine_disjunction(F, unk_a()), unk_a());
        assert_eq!(combine_disjunction(unk_a(), F), unk_a());
        assert_eq!(combine_disjunction(F, re_a()), re_a());
        assert_eq!(combine_disjunction(re_a(), F), re_a());
        // Non-definitive precedence: RE outranks Unknown (either side); left wins ties.
        assert_eq!(combine_disjunction(unk_a(), unk_b()), unk_a());
        assert_eq!(combine_disjunction(unk_a(), re_a()), re_a());
        assert_eq!(combine_disjunction(re_a(), unk_a()), re_a());
        assert_eq!(combine_disjunction(re_a(), re_b()), re_a());
    }

    /// Every one of the 10 distinct `QueryResult` values (the finite combiner domain).
    fn all_results() -> Vec<QueryResult> {
        use ResourceKind::*;
        use UnknownReason::*;
        vec![
            T,
            F,
            QueryResult::Unknown(CycleCut),
            QueryResult::Unknown(IncompleteKnowledge),
            QueryResult::Unknown(NafDependent),
            QueryResult::Unknown(BackendUnavailable),
            QueryResult::Unknown(NonFinite),
            QueryResult::ResourceExceeded(Depth),
            QueryResult::ResourceExceeded(Fuel),
            QueryResult::ResourceExceeded(Memory),
        ]
    }

    /// EXHAUSTIVE model↔code bridge for the mechanized proof in `proofs/Combiner.lean`.
    ///
    /// The Lean file PROVES these soundness properties of the four-valued combiner; here we
    /// check that the real Rust `combine_conjunction` / `combine_disjunction` / `negate_result`
    /// satisfy the SAME properties over every one of the 10×10 inputs. The combiner's domain
    /// is finite, so an exhaustive check is a complete proof of conformance — a regression that
    /// reintroduced the historical `True ∧ Unknown → False` bug would fail here immediately.
    /// Keep the asserted properties in lock-step with the theorems in `proofs/Combiner.lean`.
    #[test]
    fn exhaustive_soundness_matches_lean_model() {
        let all = all_results();
        for a in &all {
            // Negation: the four laws (neg_*) + non-fabrication (neg_preserves_indefinite).
            let na = negate_result(a.clone());
            let expected_neg = match a {
                QueryResult::True => QueryResult::False,
                QueryResult::False => QueryResult::True,
                QueryResult::Unknown(_) => QueryResult::Unknown(UnknownReason::NafDependent),
                QueryResult::ResourceExceeded(k) => QueryResult::ResourceExceeded(k.clone()),
            };
            assert_eq!(na, expected_neg, "negate_result({a:?})");
            assert_eq!(
                na.is_definitive(),
                a.is_definitive(),
                "negation must preserve definiteness for {a:?}"
            );

            for b in &all {
                let conj = combine_conjunction(a.clone(), b.clone());
                let disj = combine_disjunction(a.clone(), b.clone());

                // Soundness characterization (conj_true_iff / conj_false_iff / disj_*):
                // a definitive verdict appears in EXACTLY the classically-correct case.
                assert_eq!(
                    conj.is_true(),
                    a.is_true() && b.is_true(),
                    "conj TRUE iff both TRUE: {a:?} ∧ {b:?}"
                );
                assert_eq!(
                    conj.is_false(),
                    a.is_false() || b.is_false(),
                    "conj FALSE iff some FALSE: {a:?} ∧ {b:?}"
                );
                assert_eq!(
                    disj.is_true(),
                    a.is_true() || b.is_true(),
                    "disj TRUE iff some TRUE: {a:?} ∨ {b:?}"
                );
                assert_eq!(
                    disj.is_false(),
                    a.is_false() && b.is_false(),
                    "disj FALSE iff both FALSE: {a:?} ∨ {b:?}"
                );

                // ResourceExceeded outranks Unknown in the indeterminate region (indet_re_*).
                if !a.is_definitive() && !b.is_definitive() {
                    let re_present = matches!(a, QueryResult::ResourceExceeded(_))
                        || matches!(b, QueryResult::ResourceExceeded(_));
                    assert_eq!(
                        matches!(conj, QueryResult::ResourceExceeded(_)),
                        re_present,
                        "conj RE-precedence: {a:?} ∧ {b:?}"
                    );
                    assert_eq!(
                        matches!(disj, QueryResult::ResourceExceeded(_)),
                        re_present,
                        "disj RE-precedence: {a:?} ∨ {b:?}"
                    );
                }
            }
        }
    }
}
