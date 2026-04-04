# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

## Tier 1: Soundness & Correctness Gaps

1. **Add equality / identity reasoning (`du`)**
   The biggest classical FOL gap. No way to state "Adam is the same entity as the King."

   - Reserve `du` as a special predicate in logji.
   - Implement congruence closure (union-find): `du(a,b)` + `du(b,c)` → `du(a,c)`.
   - Modify `check_predicate_in_kb_typed`: when checking `P(a)`, also check `P(x)` for all `x` in `a`'s equivalence class.
   - Modify backward chaining: treat equivalent terms as matching during unification.
   - Add `ProofRule::EqualitySubstitution` variant for proof traces.
   - Start with untensed equality only. Tensed equality (`Past(du(a,b))`) is future work.
   - Tests: simple alias, transitive chain, interaction with universal rules, interaction with Skolem terms.

3. **Add predicate signature validation**
   logji accepts any predicate with any arity from any entry path. Arity mismatches are silent.

   - Add `PredicateRegistry` to `KnowledgeBaseInner` seeded from the PHF dictionary (known gismu/lujvo arities).
   - On fact assertion, validate arity. Unknown predicates: accept + register with `Inferred` source + warning (permissive mode initially).
   - Validate all entry paths: `process_assertion`, `assert_fact_with_id`, compute ingestion.
   - Tests: valid arity, invalid arity, unknown predicate.

4. **Add integrity constraints (`deny`)**
   No mechanism to declare "this must never be true." Domain modelling errors (asserting contradictory facts) are silent.

   - Add `deny` constraint registration: `deny P(x) ∧ Q(x)` means "if both hold for any x, error."
   - Check constraints on every assertion (after fact is added, before returning success).
   - If violated, return `NibliError::Reasoning("Integrity violation: ...")` with the violating bindings.
   - Pairs with predicate validation (#3) and contradiction detection.
   - Tests: simple mutual exclusion, constraint with universal quantifier, constraint violation on derived fact.

## Tier 2: Completeness & Explanation

5. **Make NAF dependencies explicit and surfaceable**
   Currently NAF is applied uniformly with no visibility into which conclusions depend on it.

   - Tag proof trace steps that depend on NAF with a `NafDependency` marker.
   - When a conclusion's proof contains NAF-dependent steps, `QueryResult` carries metadata.
   - Add `:naf-deps` REPL command showing which active conclusions depend on NAF.
   - Document: "Under CWA, `False` means 'not derivable.' Under open-world, it would mean `Unknown`."

6. **Add failure traces / "why not?" explanation**
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

9. **Persistent fact store with lazy on-demand loading**
   Everything is in-memory. WASM has a 4 GB limit. Large KBs (10K+ facts) must not load data they don't need.

   **Design: append-only facts log + predicate index + LRU page cache.**

   On-disk format (two files):
   - **Facts log** — append-only. Each entry: `[u64 fact_id][u32 lojban_len][lojban bytes][u32 stored_fact_len][postcard StoredFact]`. Original Lojban source preserved alongside compiled form (pipeline is one-way; can't reconstruct Lojban from StoredFact).
   - **Predicate index** — `HashMap<relation, Vec<u64 offset>>` serialized on flush. Loaded on startup (kilobytes). Points into facts log.

   In-memory (bounded, configurable):
   - Predicate index — always loaded (small).
   - LRU page cache — recently accessed `StoredFact` entries (e.g., 16 MB budget). Only facts touched by the current query chain are loaded.
   - Universal rules — always loaded (small, needed for every query).
   - Domain member sets — always loaded (needed for quantifier evaluation). These are just the set of known entity names, not the facts themselves.
   - Equality index / union-find — always loaded once equality lands (#2).

   **Critical invariant: never read a fact from disk unless backward chaining or predicate lookup demands it.** A query for `gerku(adam)` touches only the `gerku` index entries, not the entire KB.

   Query path:
   1. Predicate lookup → in-memory index → file offsets for that relation.
   2. Check LRU cache for each offset.
   3. Cache miss → `seek` + `read` from facts log → postcard deserialize → insert into cache.
   4. Backward chaining operates on cached facts. Rule condition checks trigger further lazy loads.

   Assertion path:
   1. Serialize StoredFact + Lojban source → append to facts log (one sequential write).
   2. Update in-memory predicate index with new offset.
   3. Insert into LRU cache (hot on assertion).
   4. Periodically flush predicate index to disk.

   Retraction path:
   - Mark fact as tombstoned in index (don't rewrite log). Compaction pass reclaims space offline.

   Abstraction layer (`FactStore` trait):
   ```rust
   trait FactStore {
       fn lookup_predicate(&self, relation: &str) -> impl Iterator<Item = &StoredFact>;
       fn append(&mut self, fact: &StoredFact, source: &str) -> Result<u64>;
       fn retract(&mut self, fact_id: u64) -> Result<()>;
       fn domain_members(&self) -> &DomainMembers;
   }
   ```
   - WASM impl: WASI file I/O (`fd_read`/`fd_write`/`fd_seek`) + LRU cache.
   - Native impl: `memmap2` for zero-copy reads + same LRU cache interface.
   - In-memory impl: current `HashSet<StoredFact>` wrapped in the trait (for tests and small KBs).

   **Why not redb/sled/SQLite:** All use `mmap` or C FFI. None compile to `wasm32-wasip2`. The access pattern (predicate-indexed lookup) is narrow enough that a custom store is simpler and faster than a general-purpose DB.

   Estimated scope: ~500 lines (log format, index, LRU cache, trait, WASI impl, native impl).

10. **Replace fixed-depth search with iterative deepening (depends on #9)**
   The depth cutoff silently collapses "not found within depth N" to ResourceExceeded. Iterative deepening guarantees finding the shallowest proof.

   - Modify `check_formula_holds` to accept max_depth parameter.
   - Add wrapper that calls with depth 1, 2, ... up to `max_chain_depth`.
   - Proof found at depth D → True. Exhausted all depths → False. Hit max_chain_depth → ResourceExceeded.
   - Future: SLG tabling for full recursive completeness (subsumes visited-set cycle detection).

11. **Add argument-position indexing (depends on #9)**
    `typed_predicate_facts` indexes by relation name only. Queries like "everything where x2 is adam" scan all facts for that predicate.

    - Add `typed_arg_index: HashMap<(String, usize, GroundTerm), HashSet<StoredFact>>`.
    - On `assert_typed_fact`, index each fact by (relation, arg_position, arg_value) for ground arguments.
    - Use argument index in `check_predicate_in_kb_typed` and witness extraction when query has ground arguments.
    - Benchmark: compare query latency before/after on 1000+ facts for a single predicate.

12. **Add incremental truth maintenance (TMS)**
    Retraction currently rebuilds the entire KB from surviving base facts. O(KB) per retraction.

    - Add `Justification` to derived facts: which rule + which bindings + which supporting facts.
    - On retraction, walk the dependency cone and retract derived facts recursively.
    - Keep full rebuild as fallback (`:rebuild` REPL command).
    - Tests: retract base fact → derived facts removed, unrelated facts survive.

13. **Selective forward propagation for marked rules**
    Keep backward chaining as primary. Allow opt-in forward propagation for specific rules (e.g., contradiction detection).

    - Add `forward: bool` flag to `UniversalRuleRecord` (default false).
    - On fact assertion, check all `forward: true` rules. If all conditions met, assert conclusion immediately.
    - REPL: `:forward <rule-id>` to mark a rule.
    - Primary use: contradiction detection rules. Secondary: hot derived predicates.

## Tier 4: Code Quality & Measurement

14. **Break up oversized core files**
    - `logji/src/lib.rs` (4,715 lines) → extract `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`.
    - `gerna/src/grammar.rs` (4,452 lines) → split per-construct (sumti, selbri, sentence parsing).

15. **Add criterion benchmarks**
    - Query latency at 10² / 10³ / 10⁴ facts (parametric).
    - Recursive rule chains (depth 2, 5, 10).
    - Witness extraction over growing domain sizes.
    - Equality-heavy workloads (once equality lands).
    - Retract + rebuild vs retract + TMS (once TMS lands).
    - Store baseline in `benches/baseline.json`.

16. **Publish GUARANTEES.md**
    Formal statement of engine properties: soundness, completeness bounds, negation policy, equality semantics, resource limits, retraction model.
