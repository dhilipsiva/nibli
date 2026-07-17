use super::*;

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

/// Build the full candidate vector for unbound event variable search:
/// all typed domain members + SkolemFn witness terms from the registry.
fn build_all_candidates(inner: &KnowledgeBaseInner) -> Vec<GroundTerm> {
    let members = inner.all_typed_domain_members();
    let mut candidates: Vec<GroundTerm> = members.to_vec();
    for entry in &inner.skolem_fn_registry {
        for combo in GroundTermCartesianProduct::new(members, entry.dep_count) {
            candidates.push(build_skolem_fn_term(&entry.base_name, &combo));
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
/// (temporal lifting consults the same relation-keyed bucket, so this covers
/// tensed goals too), it is not the special-cased `du` equality predicate, and
/// no du-equivalence classes exist (equivalence substitution could otherwise
/// rewrite the fact into an asserted variant via the recursive fallback).
///
/// For such relations `check_predicate_in_kb_typed` reduces to
/// `typed_fact_is_asserted` at ANY depth, so the unbound-event-variable filter
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

/// Index-anchored join binding. After a rule's event variables are bound, a
/// condition like `fanta_x1(ev_f, x__v0)` has a GROUND anchor arg (the bound
/// event) and an unbound individual pattern var. Look the matching asserted fact
/// up in `arg_position_index` and bind the individual var to it — instead of
/// enumerating those vars over a `members^k` domain cartesian. Runs to a
/// fixpoint so a var bound from one condition (the shared `di`) propagates to the
/// next (`se-katna(di, de)` becomes ground). Binds only on a UNIQUE index match
/// (deterministic — event role atoms have one fact per event), so it never
/// guesses; non-unique conditions are left for the downstream ground check.
/// Returns the names of vars newly bound, so the caller removes them per combo.
fn bind_join_vars_from_index(
    rule: &UniversalRuleRecord,
    bindings: &mut HashMap<String, GroundTerm>,
    inner: &KnowledgeBaseInner,
) -> Vec<String> {
    let mut newly_bound: Vec<String> = Vec::new();
    loop {
        let mut changed = false;
        for ct in &rule.typed_conditions {
            let cs = substitute_fact(ct, bindings);
            let gf = cs.inner();
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
fn negate_result(result: QueryResult) -> QueryResult {
    match result {
        QueryResult::True => QueryResult::False,
        QueryResult::False => QueryResult::True,
        QueryResult::Unknown(_) => QueryResult::Unknown(UnknownReason::NafDependent),
        QueryResult::ResourceExceeded(kind) => QueryResult::ResourceExceeded(kind),
    }
}

/// Evaluate a negated event-decomposed restrictor (`poi na <predicate>`) by
/// negation-as-failure over an existential. The condition HOLDS (the rule fires)
/// iff NO binding of the group's `event_var` satisfies ALL inner conditions for the
/// already-bound universal — i.e. "no witness exists" (`la .adam.` has not
/// consented). Composes only the shared-`&inner` primitives, so it runs from the
/// SHARED-`&inner` firing path (unlike `check_formula_holds_core`, which needs
/// `&mut inner` for compute auto-assert): enumerate the same complete candidate
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
    negate_result(exists_verdict)
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
) -> Result<QueryResult, String> {
    // The bare (untraced) entry: delegate to the single evaluator with a no-op
    // sink (every recording branch is dead-code-eliminated for `NoOpSink`), and
    // drop the step index. The post-check converts a flag raised by the watchdog
    // DURING a long backward-chaining call into a clean `Err`; the core also
    // check_cancelled's at every node entry.
    check_cancelled(inner)?;
    let (result, _idx) =
        check_formula_holds_core::<NoOpSink>(buffer, node_id, subs, inner, tense, &mut NoOpSink)?;
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
    memo: &mut HashMap<String, u32>,
) -> Result<(QueryResult, u32), String> {
    check_cancelled(inner)?;
    let mut sink = RecordingSink { steps, memo };
    let result =
        check_formula_holds_core::<RecordingSink>(buffer, node_id, subs, inner, tense, &mut sink)?;
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
    sink: &mut S,
) -> Result<(QueryResult, u32), String> {
    check_cancelled(inner)?;
    match get_node(buffer, node_id)? {
        LogicNode::AndNode((l, r)) => {
            // Abstraction opacity: `And(__abs_<hash>(referent), body)`. The body is
            // OPAQUE to reasoning — the conjunction's verdict is just the marker's
            // (left). This is what keeps `believe P` from leaking or being satisfied by
            // bare P, while same-content abstractions still match via the marker.
            if is_abstraction_marker(buffer, *l) {
                return check_formula_holds_core::<S>(buffer, *l, subs, inner, tense, sink);
            }
            let (lv, li) = check_formula_holds_core::<S>(buffer, *l, subs, inner, tense, sink)?;
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
            let (rv, ri) = check_formula_holds_core::<S>(buffer, *r, subs, inner, tense, sink)?;
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
            let (lv, li) = check_formula_holds_core::<S>(buffer, *l, subs, inner, tense, sink)?;
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
            let (rv, ri) = check_formula_holds_core::<S>(buffer, *r, subs, inner, tense, sink)?;
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
            let (iv, ii) =
                check_formula_holds_core::<S>(buffer, *inner_node, subs, inner, tense, sink)?;
            let verdict = negate_result(iv.clone());
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
                    let members = inner.all_typed_domain_members();
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(&*inner, rel, args, v, members, subs)
                    {
                        // Clone the winning member before releasing the slice borrow.
                        let winner = batch
                            .results
                            .iter()
                            .position(|r| *r)
                            .map(|i| members[i].clone());
                        // Ingest deferred facts now that the slice borrow is released.
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        if let Some(winning_member) = winner {
                            let idx = if S::RECORDING {
                                let body_idx = with_sub(subs, v, winning_member.clone(), |s| {
                                    check_formula_holds_core::<S>(
                                        buffer, *body, s, inner, tense, sink,
                                    )
                                })?
                                .1;
                                sink.push(ProofStep {
                                    rule: ProofRule::ExistsWitness {
                                        var: v.clone(),
                                        term: witness_term_to_logical_term(&winning_member),
                                    },
                                    holds: true,
                                    children: vec![body_idx],
                                })
                            } else {
                                0
                            };
                            return Ok((QueryResult::True, idx));
                        }
                    }
                }
            }
            // Decomposed numeric group (surface arithmetic/comparison): evaluate
            // the operands gathered from the role predicates directly — the
            // verdict is definitive, matching the flat ComputeNode arm.
            if let Some(group) = try_evaluate_numeric_group(&*inner, buffer, v, *body, subs) {
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
            // Slow path: need owned Vec because the body eval takes &mut inner.
            // Candidate narrowing (∃-heavy query blowup fix): when the body has
            // a mandatory positive anchor, enumerate only index/rule-derivable
            // candidates instead of the full domain × SkolemFn-registry
            // cartesian — completeness argument at collect_entailment_candidates.
            let candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(&entry.base_name, &combo));
                            }
                        }
                        all
                    }
                };
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
                        &mut NoOpSink,
                    )
                })?
                .0;
                if result.is_true() {
                    let idx = if S::RECORDING {
                        let body_idx = with_sub(subs, v, candidate.clone(), |s| {
                            check_formula_holds_core::<S>(buffer, *body, s, inner, tense, sink)
                        })?
                        .1;
                        sink.push(ProofStep {
                            rule: ProofRule::ExistsWitness {
                                var: v.clone(),
                                term: witness_term_to_logical_term(candidate),
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
                    sink.push(ProofStep {
                        rule: ProofRule::ExistsFailed,
                        holds: false,
                        children: vec![],
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
                    if let Some(batch) = batch_evaluate_compute_for_members(
                        &*inner,
                        rel,
                        args,
                        v,
                        members_slice,
                        subs,
                    ) {
                        let fail_member = batch
                            .results
                            .iter()
                            .position(|r| !*r)
                            .map(|i| members_slice[i].clone());
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        if let Some(counter) = fail_member {
                            let idx = if S::RECORDING {
                                let body_idx = with_sub(subs, v, counter.clone(), |s| {
                                    check_formula_holds_core::<S>(
                                        buffer, *body, s, inner, tense, sink,
                                    )
                                })?
                                .1;
                                sink.push(ProofStep {
                                    rule: ProofRule::ForallCounterexample {
                                        entity: ground_term_to_logical_term(&counter),
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
                                buffer, *body, v, &members, subs, inner, tense, sink,
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
                        check_formula_holds_core::<S>(buffer, *body, s, inner, tense, sink)
                    })?
                    .1;
                    sink.push(ProofStep {
                        rule: ProofRule::ForallCounterexample {
                            entity: ground_term_to_logical_term(&counter),
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
                        check_formula_holds_core::<S>(buffer, *body, s, inner, tense, sink)
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
                    buffer, *body, v, &members, subs, inner, tense, sink,
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
            // any member of a class answers for it), and skip existential-import
            // PRESUPPOSITION witnesses (a phantom entity a rule presupposed
            // must not change "how many"; it still satisfies ∃/∀).
            let members: Vec<GroundTerm> = {
                let mut seen = HashSet::new();
                let mut out = Vec::new();
                for m in inner.all_typed_domain_members() {
                    if let GroundTerm::Constant(name) = m
                        && inner.presupposition_witnesses.contains(name.as_str())
                    {
                        continue;
                    }
                    let canon = find_canonical_readonly(&inner.equivalence_parent, m);
                    if seen.insert(canon) {
                        out.push(m.clone());
                    }
                }
                out
            };

            // Batch compute fast path.
            if let Ok(body_node) = get_node(buffer, *body) {
                if let LogicNode::ComputeNode((rel, args)) = body_node {
                    if let Some(batch) =
                        batch_evaluate_compute_for_members(&*inner, rel, args, v, &members, subs)
                    {
                        for fact in batch.deferred_facts {
                            assert_typed_fact(fact, inner);
                        }
                        let satisfying = batch.results.iter().filter(|r| **r).count() as u32;
                        let verdict = if satisfying == *count {
                            QueryResult::True
                        } else {
                            QueryResult::False
                        };
                        let idx = if S::RECORDING {
                            sink.push(ProofStep {
                                rule: ProofRule::CountResult {
                                    expected: *count,
                                    actual: satisfying,
                                },
                                holds: verdict.is_true(),
                                children: vec![],
                            })
                        } else {
                            0
                        };
                        return Ok((verdict, idx));
                    }
                }
            }
            let mut satisfying = 0u32;
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
                        &mut NoOpSink,
                    )
                })?
                .0;
                match result {
                    QueryResult::True => satisfying += 1,
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
                sink.push(ProofStep {
                    rule: ProofRule::CountResult {
                        expected: *count,
                        actual: satisfying,
                    },
                    holds: verdict.is_true(),
                    children: vec![],
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
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
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
            let resolved = resolve_args_for_dispatch(args, subs);
            if let Ok(result) = dispatch_to_backend(&*inner, rel, &resolved) {
                if result {
                    if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                        assert_typed_fact(fact, inner);
                    }
                }
                let verdict = if result {
                    QueryResult::True
                } else {
                    QueryResult::False
                };
                let idx = if S::RECORDING {
                    sink.push(ProofStep {
                        rule: ProofRule::ComputeCheck {
                            method: "backend".to_string(),
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
            // This fallback is reached ONLY when `dispatch_to_backend` returned `Err`
            // (the arithmetic fast path and the `Ok(_)` branch both returned early).
            // A backend outage / unregistered backend must NOT read as a derived
            // falsehood: honor a prior successful computation that auto-asserted this
            // exact fact (so a cached result survives a transient outage), but
            // otherwise surface `Unknown(BackendUnavailable)` — we genuinely could not
            // determine the result — never a definitive `False`.
            let verdict =
                if let Some(fact) = build_stored_fact_from_node(buffer, node_id, subs, tense) {
                    let mut visited = HashSet::new();
                    match check_predicate_in_kb_typed(&fact, &*inner, 0, &mut visited) {
                        QueryResult::True => QueryResult::True,
                        _ => QueryResult::Unknown(UnknownReason::BackendUnavailable),
                    }
                } else {
                    QueryResult::Unknown(UnknownReason::BackendUnavailable)
                };
            let idx = if S::RECORDING {
                let method = match &verdict {
                    QueryResult::Unknown(UnknownReason::CycleCut) => "cycle_cut",
                    QueryResult::Unknown(UnknownReason::IncompleteKnowledge) => {
                        "incomplete_knowledge"
                    }
                    QueryResult::Unknown(UnknownReason::NafDependent) => "naf_dependent",
                    QueryResult::Unknown(UnknownReason::BackendUnavailable) => {
                        "backend_unavailable"
                    }
                    QueryResult::Unknown(UnknownReason::NonFinite) => "non_finite",
                    QueryResult::ResourceExceeded(ResourceKind::Depth) => "depth_limit",
                    QueryResult::ResourceExceeded(ResourceKind::Fuel) => "fuel_limit",
                    QueryResult::ResourceExceeded(ResourceKind::Memory) => "memory_limit",
                    QueryResult::False | QueryResult::True => "kb",
                };
                sink.push(ProofStep {
                    rule: ProofRule::ComputeCheck {
                        method: method.to_string(),
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
    sink: &mut S,
) -> Result<(Vec<u32>, Vec<LogicalTerm>), String> {
    let mut child_indices = Vec::new();
    let mut entity_terms = Vec::new();
    for member in members {
        let body_idx = with_sub(subs, v, member.clone(), |s| {
            check_formula_holds_core::<S>(buffer, body, s, inner, tense, sink)
        })?
        .1;
        child_indices.push(body_idx);
        entity_terms.push(ground_term_to_logical_term(member));
    }
    Ok((child_indices, entity_terms))
}

pub(super) fn find_witnesses(
    buffer: &LogicBuffer,
    node_id: u32,
    subs: &mut HashMap<String, GroundTerm>,
    inner: &mut KnowledgeBaseInner,
    tense: Option<&str>,
) -> Result<Vec<Vec<(String, GroundTerm)>>, String> {
    // Once any leaf has been CUT at the depth/cycle horizon the enumeration is known
    // incomplete and `query_find_inner` will refuse with `Err` regardless of what the
    // remaining candidates yield — so stop the (potentially huge) candidate sweep
    // immediately instead of exploring it to the end. Without this, a cyclic
    // event-decomposed find terminates but only after enumerating the full
    // member×Skolem cartesian (seconds), even though the verdict is already decided.
    if inner.find_horizon_hit {
        return Ok(Vec::new());
    }
    match get_node(buffer, node_id)? {
        LogicNode::ExistsNode((v, body)) => {
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
            let candidates: Vec<GroundTerm> =
                match collect_entailment_candidates(buffer, *body, v, subs, inner, tense) {
                    Some(narrowed) => narrowed,
                    None => {
                        let members: Vec<GroundTerm> = inner.all_typed_domain_members().to_vec();
                        let mut all = members.clone();
                        for entry in &inner.skolem_fn_registry {
                            for combo in GroundTermCartesianProduct::new(&members, entry.dep_count)
                            {
                                all.push(build_skolem_fn_term(&entry.base_name, &combo));
                            }
                        }
                        all
                    }
                };

            for candidate in candidates {
                let mut new_subs = subs.clone();
                new_subs.insert(v.clone(), candidate.clone());
                let sub_results = find_witnesses(buffer, *body, &mut new_subs, inner, tense)?;
                for mut bindings in sub_results {
                    bindings.push((v.clone(), candidate.clone()));
                    results.push(bindings);
                }
            }

            Ok(results)
        }
        LogicNode::PastNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Past"))
        }
        LogicNode::PresentNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Present"))
        }
        LogicNode::FutureNode(inner_node) => {
            find_witnesses(buffer, *inner_node, subs, inner, Some("Future"))
        }
        LogicNode::AndNode((l, r)) => {
            let left_results = find_witnesses(buffer, *l, subs, inner, tense)?;
            let mut results = Vec::new();
            for left_bindings in left_results {
                let mut merged_subs = subs.clone();
                for (k, v) in &left_bindings {
                    merged_subs.insert(k.clone(), v.clone());
                }
                let right_results = find_witnesses(buffer, *r, &mut merged_subs, inner, tense)?;
                for right_bindings in right_results {
                    let mut combined = left_bindings.clone();
                    combined.extend(right_bindings);
                    results.push(combined);
                }
            }
            Ok(results)
        }
        LogicNode::OrNode((l, r)) => {
            let mut results = find_witnesses(buffer, *l, subs, inner, tense)?;
            results.extend(find_witnesses(buffer, *r, subs, inner, tense)?);
            Ok(results)
        }
        _ => {
            let verdict = check_formula_holds(buffer, node_id, subs, inner, tense)?;
            if verdict.is_true() {
                Ok(vec![vec![]])
            } else {
                // Not a witness. Distinguish a genuine "no" (`False` /
                // `Unknown(NafDependent)`) from the search being CUT at the
                // depth/cycle horizon — the latter means a witness may exist beyond
                // the budget, so flag the enumeration incomplete. `query_find_inner`
                // then refuses a definitive count/aggregate rather than silently
                // undercounting.
                if witness_search_cut(&verdict) {
                    inner.find_horizon_hit = true;
                }
                Ok(vec![])
            }
        }
    }
}

/// True when a non-`True` witness-leaf verdict means the search was CUT (a witness
/// may exist beyond the depth budget or behind a cut cycle), as opposed to a
/// genuine/defensible absence. `False` is a real no; `Unknown(NafDependent)` is a
/// defensibly-excluded NAF-dependent existential. Everything else
/// (`ResourceExceeded(_)`, `CycleCut`, `IncompleteKnowledge`, `BackendUnavailable`)
/// marks the witness set INCOMPLETE.
fn witness_search_cut(v: &QueryResult) -> bool {
    matches!(
        v,
        QueryResult::ResourceExceeded(_)
            | QueryResult::Unknown(UnknownReason::CycleCut)
            | QueryResult::Unknown(UnknownReason::IncompleteKnowledge)
            | QueryResult::Unknown(UnknownReason::BackendUnavailable)
    )
}

// ─── Typed Backward-Chaining (Phase 4-5b) ────────────────────────
//
// These functions mirror the fact_repr-based backward-chaining above but
// operate on StoredFact/GroundTerm directly, avoiding all string ops.

pub(super) fn clear_typed_pred_cache(inner: &KnowledgeBaseInner) {
    inner.pred_cache.borrow_mut().clear();
}

/// Check if a typed fact is asserted in the typed fact store.
pub(super) fn typed_fact_is_asserted(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    // Fast path: exact match.
    if inner.fact_store.contains(fact) {
        return true;
    }
    // Equivalence path: try substitutions of equivalent terms in args.
    if inner.equivalence_parent.is_empty() {
        return false;
    }
    typed_fact_is_asserted_with_equivalence(fact, inner).is_some()
}

/// If `fact` holds under some du-equivalence substitution of its arguments,
/// return the directly-asserted equivalent variant (so a traced proof can render
/// the substitution honestly as `EqualitySubstitution` rather than `Asserted`);
/// `None` if no equivalent variant is directly asserted.
fn typed_fact_is_asserted_with_equivalence(
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
) -> Option<StoredFact> {
    let gf = fact.inner();
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

/// Format the du-equality substitution note for a proof step: the argument pairs
/// where `orig` and `variant` differ, rendered as `"a du b, x du y"`. Shared by
/// the asserted-via-equivalence and rule-derived-via-equivalence trace paths.
fn equals_substitution_note(orig: &StoredFact, variant: &StoredFact) -> String {
    orig.inner()
        .args
        .iter()
        .zip(variant.inner().args.iter())
        .filter(|(o, v)| o != v)
        .map(|(o, v)| format!("{} du {}", o.to_display_string(), v.to_display_string()))
        .collect::<Vec<_>>()
        .join(", ")
}

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
                let canon_a = find_canonical_readonly(&inner.equivalence_parent, &args[0]);
                let canon_b = find_canonical_readonly(&inner.equivalence_parent, &args[1]);
                if canon_a == canon_b {
                    return QueryResult::True; // Symmetry + transitivity
                }
            }
        }
    }

    if typed_fact_is_asserted(fact, inner) {
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
    if result.is_false()
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
            for combo in CartesianProduct::new(&equiv_args) {
                let variant_gf = GroundFact::new(gf.relation.clone(), combo);
                let variant = StoredFact::with_tense_from(variant_gf, fact);
                if variant != *fact && !visited.contains(&cycle_key(&variant)) {
                    let variant_result =
                        check_predicate_in_kb_typed(&variant, inner, depth, visited);
                    if variant_result.is_true() {
                        result = QueryResult::True;
                        break;
                    }
                }
            }
            // Only remove `fact` if WE inserted it (don't clobber an entry an
            // outer frame is relying on for its own cycle guard).
            if reinserted {
                visited.remove(&cycle_key(fact));
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

    // Only cache definitive (True/False) results. Non-definitive results
    // (Unknown(CycleCut), ResourceExceeded(Depth)) are context-dependent — they
    // depend on the current `visited` stack and `max_chain_depth` — so caching
    // them keyed by fact alone would poison sibling branches and later, deeper
    // iterative-deepening passes. True/False are context-independent for a fixed KB.
    if inner.pred_cache_enabled.get() && result.is_definitive() {
        inner
            .pred_cache
            .borrow_mut()
            .insert(fact.clone(), result.clone());
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
/// with it — for a tensed goal, temporal lifting strips the tense first, so
/// the tense-stripped goal is also tried against the (always-Bare) templates.
/// If no conclusion unifies, no amount of extra depth can ever prove the goal.
fn any_rule_conclusion_unifies(fact: &StoredFact, inner: &KnowledgeBaseInner) -> bool {
    let try_goal = |goal: &StoredFact| {
        inner
            .universal_rules
            .get(goal.relation())
            .is_some_and(|rules| {
                rules.iter().any(|r| {
                    r.typed_conclusions
                        .iter()
                        .any(|c| unify_facts(c, goal).is_some())
                })
            })
    };
    try_goal(fact) || strip_tense_from_fact(fact).as_ref().is_some_and(try_goal)
}

/// Typed backward-chaining — structural matching instead of fact_repr tokenization.
/// Narrow the candidate set for one unbound event variable by its single-event-var
/// conditions, BEFORE the full combo enumeration. Unifies the candidate filter that
/// was duplicated (and divergent) across all four backward-chain blocks
/// (untraced/traced × normal/temporal): index-decidable conditions are checked first
/// and definitively (`typed_fact_is_asserted`, no depth penalty); rule-backed
/// conditions fall through to a recursive check kept unless DEFINITIVELY false
/// (a non-definitive verdict near the depth horizon conservatively keeps the
/// candidate). Negated conditions are inverted in both phases (NAF). A condition
/// still carrying an unbound individual `x__` var is NOT pruned on — it is bound
/// later by the index-anchored join. `tense_fact = Some(f)` applies f's tense to
/// each condition (temporal lifting); `None` keeps them bare.
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
    tense_fact: Option<&StoredFact>,
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
                let bare = substitute_fact(&rule.typed_conditions[idx], &tb);
                let cs = match tense_fact {
                    Some(f) => apply_tense_to_fact(&bare, f),
                    None => bare,
                };
                if fact_has_unbound_pattern_var(&cs) {
                    return true;
                }
                let asserted = typed_fact_is_asserted(&cs, inner);
                if rule.negated_condition_indices.contains(&idx) {
                    !asserted
                } else {
                    asserted
                }
            }) && recursive_indices.iter().all(|&idx| {
                let bare = substitute_fact(&rule.typed_conditions[idx], &tb);
                let cs = match tense_fact {
                    Some(f) => apply_tense_to_fact(&bare, f),
                    None => bare,
                };
                if fact_has_unbound_pattern_var(&cs) {
                    return true;
                }
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                let verdict = if rule.negated_condition_indices.contains(&idx) {
                    negate_result(result)
                } else {
                    result
                };
                !verdict.is_false()
            })
        })
        .cloned()
        .collect()
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
    memo: &'a mut HashMap<String, u32>,
}
impl TraceSink for RecordingSink<'_> {
    const RECORDING: bool = true;
    fn push(&mut self, step: ProofStep) -> u32 {
        let idx = self.steps.len() as u32;
        self.steps.push(step);
        idx
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

/// Build the `Derived` proof step for a rule that fired, recording each
/// condition's provenance as a child (a `Negation` leaf for a NAF-negated
/// condition, otherwise the positive atom's full derivation via the sink).
/// Called ONLY on the recording path (`S::RECORDING`); `tense_source`/
/// `tense_label` carry the temporal-lifting context (both `None` for a normal
/// rule). All conditions are known to hold (the four-valued verdict loop just
/// confirmed it), so no re-check/break is needed here.
#[allow(clippy::too_many_arguments)]
fn emit_derived<S: TraceSink>(
    sink: &mut S,
    rule: &UniversalRuleRecord,
    bindings: &HashMap<String, GroundTerm>,
    fact: &StoredFact,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    tense_source: Option<&StoredFact>,
    tense_label: Option<&str>,
) -> u32 {
    let display = fact.to_display_string();
    let mut child_indices = Vec::new();
    for (idx, cond_template) in rule.typed_conditions.iter().enumerate() {
        let bare = substitute_fact(cond_template, bindings);
        let cond_fact = match tense_source {
            Some(src) => apply_tense_to_fact(&bare, src),
            None => bare,
        };
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
    let label = match tense_label {
        Some(t) => format!("{} [{}]", rule.label, t),
        None => rule.label.clone(),
    };
    sink.push(ProofStep {
        rule: ProofRule::Derived {
            label,
            fact: display,
        },
        holds: true,
        children: child_indices,
    })
}

/// Typed backward-chaining core — the single rule-firing enumeration shared by
/// the untraced verdict path (`S = NoOpSink`) and the proof-recording path
/// (`S = RecordingSink`). The four-valued accumulation and the shared `visited`
/// cycle-cut run UNCONDITIONALLY, so the returned `QueryResult` is authoritative
/// and identical to the former `try_backward_chain_typed`; proof steps are
/// emitted only when `S::RECORDING`, and the second tuple field is the index of
/// the `Derived` step proving the goal (`Some` only when recording AND a rule
/// fired). This replaces the former untraced/traced × normal/temporal block
/// duplication; sharing `visited` with the recording path closes the old
/// traced-path per-condition cycle asymmetry (LP-L2).
/// Map a tensed `StoredFact` to its proof-trace tense label.
fn tense_label_of(f: &StoredFact) -> &'static str {
    match f {
        StoredFact::Past(_) => "past",
        StoredFact::Present(_) => "present",
        StoredFact::Future(_) => "future",
        _ => "?",
    }
}

/// Run one backward-chain phase (the per-rule firing loop) for `match_fact`.
///
/// `tense_fact` is `None` for the NORMAL phase (rules matching the goal
/// directly, conditions checked bare) and `Some(tensed_goal)` for the
/// TEMPORAL-LIFTING phase (timeless rules fired against the bare goal, each
/// condition re-tensed with the goal's tense). It is the SOLE difference
/// between the two phases — it drives the candidate-filter tense, the
/// per-condition re-tensing, and the proof-step tense label.
///
/// Returns `Some(root)` if a rule fired definitively True (the caller returns
/// `(True, root)`); `None` if no rule fired, accumulating any non-definitive
/// verdict into `*best_result`. The caller owns `visited.remove(fact)`.
fn process_phase<S: TraceSink>(
    match_fact: &StoredFact,
    tense_fact: Option<&StoredFact>,
    inner: &KnowledgeBaseInner,
    depth: usize,
    visited: &mut HashSet<StoredFact>,
    sink: &mut S,
    candidates_slot: &mut Option<Vec<GroundTerm>>,
    best_result: &mut Option<QueryResult>,
) -> Option<Option<u32>> {
    // The original goal carries the proof emission + (when lifting) the tense
    // source; in the normal phase it is just `match_fact`.
    let orig_fact = tense_fact.unwrap_or(match_fact);
    let tense_label = tense_fact.map(tense_label_of);

    let rules = matching_rules_typed(match_fact, &inner.universal_rules);
    for rule in rules {
        for typed_concl in &rule.typed_conclusions {
            let Some(mut bindings) = unify_facts(typed_concl, match_fact) else {
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
                let mut per_var_candidates: Vec<Vec<GroundTerm>> = Vec::new();
                for ev_var in &unbound_event_vars {
                    let single_var_cond_indices: Vec<usize> = rule
                        .typed_conditions
                        .iter()
                        .enumerate()
                        .filter(|(_, ct)| {
                            stored_fact_contains_var(ct, ev_var)
                                && unbound_event_vars.iter().all(|other| {
                                    other == ev_var || !stored_fact_contains_var(ct, other)
                                })
                        })
                        .map(|(i, _)| i)
                        .collect();

                    if single_var_cond_indices.is_empty() {
                        per_var_candidates.push(ensure_candidates(candidates_slot, inner).to_vec());
                    } else {
                        // Temporal lifting (tense_fact = Some): the candidate filter
                        // applies the queried fact's tense to each condition (the
                        // shared helper handles the decidable/recursive split + NAF).
                        let cand = ensure_candidates(candidates_slot, inner).to_vec();
                        let filtered = filter_event_candidates(
                            rule,
                            ev_var,
                            &bindings,
                            &single_var_cond_indices,
                            &cand,
                            inner,
                            depth,
                            visited,
                            tense_fact,
                        );
                        per_var_candidates.push(filtered);
                    }
                }

                if per_var_candidates.iter().any(|pvc| pvc.is_empty()) {
                    continue;
                }

                let mut found = false;
                let mut combo_pending = None;
                for combo in TypedMultiCartesian::new(&per_var_candidates, inner.cancel.clone()) {
                    for (i, ev_var) in unbound_event_vars.iter().enumerate() {
                        bindings.insert(ev_var.clone(), combo[i].clone());
                    }
                    // Index-anchored join: bind condition-only individual vars
                    // (e.g. the inhibitor/enzyme of a multi-variable prenex rule)
                    // from the bound events' role facts, instead of enumerating
                    // them over a members^k domain cartesian.
                    let joined_vars = bind_join_vars_from_index(rule, &mut bindings, inner);
                    let mut all_hold = true;
                    let mut pending_here = None;
                    for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                        // Temporal lifting re-tenses each condition with the goal's
                        // tense; the normal phase checks it bare.
                        let cs = match tense_fact {
                            Some(src) => apply_tense_to_fact(&substitute_fact(ct, &bindings), src),
                            None => substitute_fact(ct, &bindings),
                        };
                        let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                        let verdict = if rule.negated_condition_indices.contains(&idx) {
                            negate_result(result)
                        } else {
                            result
                        };
                        if verdict.is_false() {
                            all_hold = false;
                            pending_here = None;
                            break;
                        }
                        if !verdict.is_true() {
                            all_hold = false;
                            pending_here = prefer_non_definitive(pending_here, verdict);
                        }
                    }
                    // Negated-exists groups are intrinsically tenseless: checked
                    // bare, not lifted, in both phases.
                    fold_negated_groups(
                        rule,
                        &bindings,
                        inner,
                        candidates_slot,
                        depth,
                        visited,
                        &mut all_hold,
                        &mut pending_here,
                    );
                    if all_hold {
                        found = true;
                        break;
                    }
                    combo_pending = pending_here.or(combo_pending);
                    for ev_var in &unbound_event_vars {
                        bindings.remove(ev_var.as_str());
                    }
                    for v in &joined_vars {
                        bindings.remove(v.as_str());
                    }
                }
                if !found {
                    // Merge any pending non-definitive result WITHOUT wiping an
                    // already-pending one: if combo_pending is None (every combo
                    // failed definitively), keep best_result intact. Using
                    // `and_then` here would erase a pending ResourceExceeded into
                    // None and cache a wrong definitive False.
                    if let Some(r) = combo_pending {
                        *best_result = prefer_non_definitive(best_result.take(), r);
                    }
                    continue;
                }
            }

            let mut all_conditions_hold = true;
            let mut rule_pending = None;
            for (idx, ct) in rule.typed_conditions.iter().enumerate() {
                let cs = match tense_fact {
                    Some(src) => apply_tense_to_fact(&substitute_fact(ct, &bindings), src),
                    None => substitute_fact(ct, &bindings),
                };
                let result = check_predicate_in_kb_typed(&cs, inner, depth + 1, visited);
                // Negated antecedent conditions hold via negation-as-failure: invert
                // the verdict so ¬P holds iff P is unprovable (False), not iff P is True.
                let verdict = if rule.negated_condition_indices.contains(&idx) {
                    negate_result(result)
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
                        sink,
                        rule,
                        &bindings,
                        orig_fact,
                        inner,
                        depth,
                        visited,
                        tense_fact,
                        tense_label,
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

/// Reserved sentinel that collapses every event Skolem term when keying the
/// `visited` cycle guard. Prefixed with a control char so it cannot collide with a
/// real constant/entity name.
const CYCLE_SKOLEM_SENTINEL: &str = "\u{1}__cyc_skolem__";

/// An engine-minted event Skolem term: a dependent `SkolemFn` (`sk_5(rex)`) or an
/// independent Skolem constant (`sk_<n>`, from [`KnowledgeBaseInner::fresh_skolem`]
/// / `rules.rs`). These vary per derivation step; collapsing them is what lets the
/// cycle guard recognize a relation-level cycle (see [`cycle_key`]).
fn is_event_skolem_term(t: &GroundTerm) -> bool {
    match t {
        GroundTerm::SkolemFn(_, _) => true,
        // Skolem constants are `sk_<digits>`; a real entity is never numeric-suffixed
        // this way, so the naming match cannot collapse a user individual.
        GroundTerm::Constant(s) => s
            .strip_prefix("sk_")
            .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit())),
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
/// sentinel makes a re-entered relation+individual goal hash-equal, so the second
/// visit on the SAME PATH is cut (`CycleCut`). Constant/individual args are preserved,
/// so distinct individuals stay distinct (no over-cut of legitimate per-individual
/// recursion). Facts with no event-Skolem arg are returned unchanged (fast path) —
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
                GroundTerm::Constant(CYCLE_SKOLEM_SENTINEL.to_string())
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

    // Normal phase: fire rules matching the goal directly (no tense lifting).
    if let Some(root) = process_phase(
        fact,
        None,
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

    // Temporal lifting: a tensed goal also tries bare (timeless) rules, re-tensing
    // each condition with the goal's tense.
    if let Some(bare_fact) = strip_tense_from_fact(fact) {
        if let Some(root) = process_phase(
            &bare_fact,
            Some(fact),
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

/// Strip tense wrapper from a StoredFact, returning the bare fact.
fn strip_tense_from_fact(fact: &StoredFact) -> Option<StoredFact> {
    match fact {
        StoredFact::Past(f) | StoredFact::Present(f) | StoredFact::Future(f) => {
            Some(StoredFact::Bare(f.clone()))
        }
        _ => None,
    }
}

/// Apply the tense of `source` to a bare fact.
fn apply_tense_to_fact(fact: &StoredFact, source: &StoredFact) -> StoredFact {
    match source {
        StoredFact::Past(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Past(f.clone()),
            other => other.clone(),
        },
        StoredFact::Present(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Present(f.clone()),
            other => other.clone(),
        },
        StoredFact::Future(_) => match fact {
            StoredFact::Bare(f) => StoredFact::Future(f.clone()),
            other => other.clone(),
        },
        _ => fact.clone(),
    }
}

/// Cartesian product over typed GroundTerm vectors.
struct TypedMultiCartesian<'a> {
    sets: &'a [Vec<GroundTerm>],
    indices: Vec<usize>,
    done: bool,
    /// Cooperative cancellation flag: when raised, the product stops yielding so
    /// a candidates^k backward-chaining blowup terminates promptly. `None` for
    /// every non-server caller, so iteration is unchanged there.
    cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

impl<'a> TypedMultiCartesian<'a> {
    fn new(
        sets: &'a [Vec<GroundTerm>],
        cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    ) -> Self {
        let done = sets.iter().any(|s| s.is_empty());
        Self {
            sets,
            indices: vec![0; sets.len()],
            done,
            cancel,
        }
    }
}

impl<'a> Iterator for TypedMultiCartesian<'a> {
    type Item = Vec<GroundTerm>;

    fn next(&mut self) -> Option<Self::Item> {
        if self
            .cancel
            .as_ref()
            .is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed))
        {
            return None;
        }
        if self.done || self.sets.is_empty() {
            if self.sets.is_empty() && !self.done {
                self.done = true;
                return Some(vec![]);
            }
            return None;
        }
        let combo: Vec<GroundTerm> = self
            .indices
            .iter()
            .enumerate()
            .map(|(set_idx, &item_idx)| self.sets[set_idx][item_idx].clone())
            .collect();
        let mut carry = true;
        for i in (0..self.sets.len()).rev() {
            if carry {
                self.indices[i] += 1;
                if self.indices[i] >= self.sets[i].len() {
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
    memo: &mut HashMap<String, u32>,
    visited: &mut HashSet<StoredFact>,
) -> u32 {
    let display = fact.to_display_string();

    if let Some(&cached_idx) = memo.get(&display) {
        // Memo hit — emit a lightweight ProofRef leaf instead of
        // re-deriving the full proof sub-tree. The original derivation
        // lives at steps[cached_idx]. We store cached_idx in children
        // so consumers can follow the back-reference if needed.
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::ProofRef { fact: display },
            holds: steps[cached_idx as usize].holds,
            children: vec![cached_idx],
        });
        return idx;
    }

    // Exact store hit → genuinely asserted.
    if inner.fact_store.contains(fact) {
        let idx = steps.len() as u32;
        steps.push(ProofStep {
            rule: ProofRule::Asserted {
                fact: display.clone(),
            },
            holds: true,
            children: vec![],
        });
        memo.insert(display, idx);
        return idx;
    }

    // Holds only via a directly-asserted du-equivalent variant → render the
    // substitution honestly as EqualitySubstitution (the fact itself was never
    // asserted). The combined condition (exact contains OR an asserted equivalent
    // variant) is identical to `typed_fact_is_asserted`, so the trace fires in
    // exactly the cases the verdict treats as asserted — only the LABEL of the
    // asserted-via-equivalence sub-case changes. The recursive child trace bottoms
    // out at the asserted variant (an exact store hit, above). A RULE-DERIVED
    // equivalent variant is NOT caught here (it is not in the store); it flows to
    // the rule-derived equality fallback further down.
    if !inner.equivalence_parent.is_empty() {
        if let Some(variant) = typed_fact_is_asserted_with_equivalence(fact, inner) {
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
            let idx = steps.len() as u32;
            steps.push(ProofStep {
                rule: ProofRule::EqualitySubstitution {
                    original: display.clone(),
                    equality_facts: equals_note,
                    substituted,
                },
                holds: true,
                children: vec![child],
            });
            memo.insert(display, idx);
            return idx;
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
            memo.insert(display, idx);
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
    // for a genuinely-provable variant (which bottoms out at an asserted fact /
    // rule), so it terminates as well. No extra depth gate is needed here, and
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
            for combo in CartesianProduct::new(&equiv_args) {
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
            if let Some(variant) = satisfying {
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
                let idx = steps.len() as u32;
                steps.push(ProofStep {
                    rule: ProofRule::EqualitySubstitution {
                        original: display.clone(),
                        equality_facts: equals_note,
                        substituted,
                    },
                    holds: true,
                    children: vec![child],
                });
                memo.insert(display, idx);
                return idx;
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
    let idx = steps.len() as u32;
    steps.push(ProofStep {
        rule: ProofRule::PredicateNotFound { predicate: display },
        holds: false,
        children: vec![],
    });
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
