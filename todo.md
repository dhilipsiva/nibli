## Replace egglog with a custom demand-driven reasoning engine

### Motivation

Nibli currently runs two redundant reasoning systems:
1. **Eager** (egglog): saturates the e-graph at insert-time, materialising every derivable fact. Discards derivation history.
2. **Lazy** (proof trace overlay): `check_formula_holds_traced` backward-chains through `UniversalRuleRecord`s to reconstruct proofs, because egglog merges equivalence classes and loses provenance.

We pay the costs of both — memory for eager saturation AND query-time work for proof tracing — without the full benefits of either. The And rewrite explosion (57,006 terms from 7 leaves) is a symptom: egglog eagerly materialises rewrites we never need. The workaround (flatten conjunctions before asserting) patches the symptom but doesn't fix the architectural mismatch.

### Target architecture

Replace egglog with a **purpose-built demand-driven reasoning engine**:

- **Indexed fact store**: Base facts stored in a predicate-name → argument-list index. No e-graph, no equality saturation. Insertion is O(1).
- **Backward-chaining query engine**: Queries backward-chain from the goal through universal rules, deriving only what is needed. The derivation path IS the proof trace — no separate overlay.
- **Memoisation / tabling**: Cache query results to prevent redundant re-derivation across repeated queries. Similar to XSB Prolog's tabled resolution. The existing `ProofRef` memo table is a prototype of this.
- **Conjunction on demand**: Instead of eagerly deriving `And(A, B)` via guarded conjunction introduction, check conjuncts individually at query time. Trivial and bounded.

### What already exists (reusable)

The existing `check_formula_holds_traced` infrastructure is ~80% of the target engine:
- `UniversalRuleRecord`: compiled rule templates with s-expression patterns
- `trace_predicate_provenance` / `try_backward_chain_traced`: backward-chaining through rule chains
- `asserted_sexps`: base fact lookup
- `ProofRef` memo table: deduplication of repeated sub-proofs
- `all_domain_members()`: entity enumeration for existential witness search
- Existential quantifier handling, tense discrimination, negation

### Migration plan

1. **Fact store**: Replace `EGraph` with a `HashMap<String, Vec<Vec<LogicalTerm>>>` (predicate → list of argument tuples). Support `InDomain` tracking as a simple `HashSet<String>`.
2. **Assert path**: `process_assertion()` stores facts in the index instead of generating egglog s-expressions. Skolemisation stays the same. No saturation step.
3. **Universal rules**: Keep `UniversalRuleRecord` and `compile_forall_to_rule`. Instead of emitting egglog `(rule ...)` commands, store as backward-chaining templates.
4. **Query path**: Promote `check_formula_holds_traced` to the primary query engine. Remove the non-traced `check_formula_holds` (every query produces a trace). Remove egglog `(check ...)` calls.
5. **Entailment check**: Backward-chain from the query formula through rules. Base case: fact exists in the index. Inductive case: a universal rule's conclusion unifies with the query, recurse on the rule's conditions.
6. **Witness extraction**: `find_witnesses` iterates domain members, calling the query engine for each candidate binding. Same as today but without egglog.
7. **Memoisation**: Extend the `ProofRef` memo table to cache across queries within a session. Key: normalised s-expression. Value: (holds: bool, proof_step_idx: u32). Clear on KB mutation (assert/retract).
8. **Belief revision**: Retraction removes from the fact index + invalidates memo cache. No full KB rebuild needed.
9. **Remove egglog dependency**: Delete the egglog crate from `Cargo.toml`, remove `make_fresh_egraph()`, the schema string, `run_saturation()`, all `parse_and_run_program` calls.

### What we gain

- **Memory**: No eager materialisation. No And/Or/Not rewrite explosion. No Catalan-scale blowup. No `NIBLI_MEMORY_MB` guardrail needed.
- **Traceability**: Proof trace is the computation, not a reconstruction. Every conclusion carries its derivation for free.
- **Simplicity**: One reasoning system instead of two. Remove ~300 lines of egglog schema + s-expression reconstruction + saturation management.
- **No tuning knobs**: No `NIBLI_RUN_BOUND`, no `NIBLI_FUEL` for saturation. Query depth is the natural bound.
- **Faster assertions**: O(1) insert into fact index vs. O(N) saturation.
- **Cheaper retraction**: Remove from index + invalidate cache vs. full e-graph rebuild.

### What we pay

- **Query-time computation**: Each query must backward-chain. Bounded by KB size × rule chain depth. For Nibli's workload (< 100 facts, < 10 rules, < 5 hop depth), this is microseconds.
- **We are already paying this cost**: `check_formula_holds_traced` already does the full backward-chain work. Removing egglog just eliminates the redundant eager pass.
- **Implementation effort**: Moderate. Most of the backward-chaining logic exists. Main work is replacing the egglog-based assert/query with index-based equivalents.

### Risk mitigation

- **Completeness**: Tabled resolution (memoisation with cycle detection) ensures termination and completeness for Datalog-expressible rules. Nibli's rules are all in this fragment.
- **Negation**: Currently handled via belief revision (retract + rebuild). With lazy evaluation, use well-founded semantics or stratified evaluation on the demand-driven engine.
- **Multi-premise rules**: Rules where the conclusion depends on multiple independent premises (not just a chain) need the backward-chainer to speculatively check each premise. The existing existential witness loop already does this pattern.

### Phases

- **Phase A**: Build the indexed fact store alongside egglog. Dual-write assertions to both. Validate that backward-chaining produces the same results as egglog for all existing tests.
- **Phase B**: Switch query path to use backward-chaining exclusively (stop using egglog `(check ...)`). This is mostly done — `check_formula_holds_traced` already does this.
- **Phase C**: Stop running `run_saturation()`. Assertions only write to the fact index. Verify all tests still pass.
- **Phase D**: Remove egglog dependency entirely. Clean up dead code.
- **Phase E**: Add cross-query memoisation with cache invalidation on KB mutation.

## Deferred / Low Priority

- **Async compute backend** — Current synchronous TCP + JSON Lines protocol is a bottleneck only under heavy external predicate use. Built-in arithmetic bypasses TCP entirely, and auto-ingestion caches results. Move to async (tokio) + binary IPC if external dispatch frequency becomes a real bottleneck.
