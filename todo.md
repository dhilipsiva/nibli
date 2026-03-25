# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Dead Code Removal (Low Effort, High Cleanup Value)

1. **Delete legacy types from logji** — `LegacyPatternTree`, `LegacyInterner`, `LegacySortedVec`, `legacy_tokenize()`, `legacy_extract_at()`, `intern_vec()`, `add_universal_rule()`, and legacy fields in `UniversalRuleRecord` (`condition_templates`, `conclusion_templates`, `condition_trees`, `conclusion_trees`) are all dead code. Backward-chaining is fully typed. Delete them and remove the `#![allow(dead_code)]` ICE workaround. ~320 lines.

2. **Remove `run_bound` / `:saturate`** — `run_bound` field in `KnowledgeBaseInner`, `set-run-bound`/`get-run-bound` WIT methods, `NIBLI_RUN_BOUND` env var, `:saturate` REPL command. Value stored but never read during reasoning — pure egglog artifact. Touches: `wit/world.wit`, `logji/src/lib.rs`, `lasna/src/lib.rs`, `gasnu/src/main.rs`, CLAUDE.md.

3. **Remove `check-membership` WIT method** — Defined in `wit/world.wit`, stub in gasnu (returns empty), `dispatch_check_membership()` in `logji/src/compute.rs` never called. Dead end-to-end.

## Tier 2: Pipeline Efficiency (Medium Effort, High Impact)

4. **Migrate `subs` HashMap from `String` to `GroundTerm`** — `check_formula_holds()`, `check_formula_holds_traced()`, and `find_witnesses()` all use `HashMap<String, String>` where values are legacy-formatted strings like `(Const "adam")`. Every predicate leaf parses these strings via `parse_repr_to_ground_term()`. Change to `HashMap<String, GroundTerm>` and build GroundTerms from domain members directly. Eliminates per-query string parsing overhead. Touches: `logji/src/reasoning.rs`, `logji/src/lib.rs`.

5. **Consolidate compute node transform** — Identical `Predicate → ComputeNode` transform exists in `lasna/src/lib.rs:442` and `nibli-engine/src/lib.rs:293`. Called 5× per query in lasna alone. Merge into one function, call once after smuni compilation. ~20 lines saved + fewer node array iterations.

6. **Consolidate proof trace formatting** — Proof tree formatting in both `nibli-protocol/src/lib.rs` and `gasnu/src/main.rs`. Error formatting repeated 3× in `nibli-engine/src/lib.rs`. Term serialization (`write_term`/`write_term_list`) duplicated between `lasna` and `nibli-engine`. Consolidate to `nibli-protocol`. ~130 lines saved.

7. **Remove duplicate representation reconstruction** — `lasna/src/lib.rs` and `nibli-engine/src/lib.rs` both have `reconstruct_repr()` / `write_repr()` / `write_term()`. Used only by `compile-debug` output. Consolidate or replace with typed display.

## Tier 3: Architecture (High Effort, High Impact)

8. **Shared WIT type packages** — Each crate (gerna, smuni, logji) generates independent copies of identical enum types via WIT bindings. `nibli-engine` has ~150 lines of exhaustive enum conversion (gerna→smuni, smuni→logji). A shared WIT package (`lojban:nibli-shared-types`) would define canonical types once. Eliminates all conversion code.

9. **SelbriSnapshot deep-clone optimization** — go'i resolution deep-clones entire selbri subtree + dependencies for every assertion/query (`lasna/src/lib.rs:94-106, 283-297`). ~150 lines of remapping logic. Replace with index offset mapping (add base offset to all indices in place) to avoid cloning. High impact for `:load` batch operations.

## Tier 4: Correctness & Robustness

10. **CRDT tombstone conflict handling** — `tavla` merge doesn't handle tombstone conflicts correctly. If two nodes retract different envelopes, merging could resurrect retracted facts. Vector clock comparison assumes missing agents at counter 0, breaks under partitions.

## Tier 5: Maintainability

11. **Split god files** — `logji/src/lib.rs` (~5000 lines) and `gerna/src/grammar.rs` (4,471 lines) are too large. Split logji into `kb.rs`, `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`. Split grammar into per-construct modules.

12. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals. Some already configurable (fuel, memory); pattern is inconsistent.

13. **WIT schema versioning** — No migration path for WIT interface evolution.

## Tier 6: Infrastructure & Deployment

14. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with per-resource locks or `RwLock`.

15. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint.

16. **Guard `RefCell` against non-WASM misuse** — Add `#[cfg]` compile-time guards.

17. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections.

18. **Gossip envelope expiration** — CRDT log is append-only with no TTL.
