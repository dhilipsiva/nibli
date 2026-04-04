# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

## Tier 2: Completeness & Explanation

1. **Add failure traces / "why not?" explanation**
   When `check_formula_holds` returns FALSE, no information about the failure path is available.

   - Define `FailureTrace` in nibli-types with variants: `PredicateNotFound`, `NoMatchingRule`, `ConditionFailed`, `DepthExceeded`, `CycleCut`.
   - Modify `check_formula_holds` to collect dead-end information on false paths.
   - Add `query_failure_trace` API, `:why-not` REPL command, GraphQL `whyNot` query.
   - UI: render failure traces in the proof panel with distinct styling.

7. **Add hypothetical / counterfactual reasoning**
   No way to ask "what if X were true?" without mutating the real KB.

   - Add `KnowledgeBase::with_assumptions(assumptions, callback)`: clone KB, assert assumptions, run callback, discard.
   - REPL: `:assume <lojban> then <query>`.
   - GraphQL: `queryWithAssumptions` mutation.
   - Cloning is acceptable for v1. Copy-on-write overlay is a future optimisation.
   - Tests: assumption doesn't persist, nested assumptions, assumption creating contradiction.

8. **Add aggregation (count/sum over witnesses)**
   No way to ask "how many entities satisfy P?" or "what is the sum of X where P(X)?" Needed for GDPR (counting data subjects) and pharma (summing dosages).

   - Add `count_witnesses(formula) -> usize` alongside `find_witnesses`.
   - Add `aggregate(formula, variable, op) -> f64` where op is Sum/Min/Max/Avg.
   - Wire through WIT, REPL (`:count`), and GraphQL.
   - Tests: count with 0/1/N witnesses, sum over numeric terms, aggregate with backward-chained witnesses.

## Tier 3: Storage, Search Strategy & Performance

9. **Replace fixed-depth search with iterative deepening**
   The depth cutoff silently collapses "not found within depth N" to ResourceExceeded. Iterative deepening guarantees finding the shallowest proof.

   - Modify `check_formula_holds` to accept max_depth parameter.
   - Add wrapper that calls with depth 1, 2, ... up to `max_chain_depth`.
   - Proof found at depth D → True. Exhausted all depths → False. Hit max_chain_depth → ResourceExceeded.
   - Future: SLG tabling for full recursive completeness (subsumes visited-set cycle detection).

10. **Add argument-position indexing**
    `typed_predicate_facts` indexes by relation name only. Queries like "everything where x2 is adam" scan all facts for that predicate.

    - Add `typed_arg_index: HashMap<(String, usize, GroundTerm), HashSet<StoredFact>>`.
    - On `assert_typed_fact`, index each fact by (relation, arg_position, arg_value) for ground arguments.
    - Use argument index in `check_predicate_in_kb_typed` and witness extraction when query has ground arguments.
    - Benchmark: compare query latency before/after on 1000+ facts for a single predicate.

11. **Add incremental truth maintenance (TMS)**
    Retraction currently rebuilds the entire KB from surviving base facts. O(KB) per retraction.

    - Add `Justification` to derived facts: which rule + which bindings + which supporting facts.
    - On retraction, walk the dependency cone and retract derived facts recursively.
    - Keep full rebuild as fallback (`:rebuild` REPL command).
    - Tests: retract base fact → derived facts removed, unrelated facts survive.

12. **Selective forward propagation for marked rules**
    Keep backward chaining as primary. Allow opt-in forward propagation for specific rules (e.g., contradiction detection).

    - Add `forward: bool` flag to `UniversalRuleRecord` (default false).
    - On fact assertion, check all `forward: true` rules. If all conditions met, assert conclusion immediately.
    - REPL: `:forward <rule-id>` to mark a rule.
    - Primary use: contradiction detection rules. Secondary: hot derived predicates.

## Tier 4: Code Quality & Measurement

13. **Break up oversized core files**
    - `logji/src/lib.rs` (4,715 lines) → extract `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`.
    - `gerna/src/grammar.rs` (4,452 lines) → split per-construct (sumti, selbri, sentence parsing).

14. **Add criterion benchmarks**
    - Query latency at 10² / 10³ / 10⁴ facts (parametric).
    - Recursive rule chains (depth 2, 5, 10).
    - Witness extraction over growing domain sizes.
    - Equality-heavy workloads (once equality lands).
    - Retract + rebuild vs retract + TMS (once TMS lands).
    - Store baseline in `benches/baseline.json`.

15. **Publish GUARANTEES.md**
    Formal statement of engine properties: soundness, completeness bounds, negation policy, equality semantics, resource limits, retraction model.


## Others

16. WASI lazy-loading backend: implement WasiFactStore using WASI file I/O (fd_read/fd_write/fd_seek) + LRU cache with per-predicate lazy loading. That's deferred per the todo.
