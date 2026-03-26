# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: DRY Consolidation (Medium Effort, High Impact)

1. **Eliminate bridge modules via type re-export** — `smuni/src/gerna_bridge.rs` (196 lines) and `logji/src/smuni_bridge.rs` (82 lines) do mechanical enum-to-enum conversion between structurally identical WIT-generated types. Have smuni re-export `gerna::bindings::...::ast_types` and logji re-export `smuni::bindings::...::logic_types` so callers use one canonical type. Compute predicate Predicate→ComputeNode transform (currently in smuni_bridge) moves to a small standalone function. ~278 lines eliminated.

2. **Consolidate S-expr reconstruction into nibli-protocol** — `reconstruct_repr()`, `write_repr()`, `write_term_list()`, `write_term()` duplicated in `lasna/src/lib.rs` (127 lines) and `nibli-engine/src/lib.rs` (131 lines). Move to `nibli-protocol` as public helpers. ~258 lines → ~130.

3. **Consolidate proof trace conversion into nibli-protocol** — `term_to_json()`, `rule_to_json()`, `proof_trace_to_wire()` in nibli-engine (94 lines) and equivalent `format_term()`, `term_to_proto()`, `rule_to_proto()`, `trace_to_proto()` in gasnu (87 lines). Both target nibli-protocol wire types. Move canonical converters into nibli-protocol. ~181 lines → ~90.

4. **Consolidate error formatting into nibli-protocol** — `format_nibli_error!` macro + helpers in nibli-engine (37 lines) and standalone `format_nibli_error()` in gasnu (23 lines). Move to nibli-protocol. ~60 lines → ~30.

## Tier 2: Architecture (High Effort, High Impact)

5. **SelbriSnapshot deep-clone optimization** — go'i resolution deep-clones entire selbri subtree + dependencies for every assertion/query (`lasna/src/lib.rs`). ~150 lines of remapping logic. Replace with index offset mapping (add base offset to all indices in place) to avoid cloning. High impact for `:load` batch operations.

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
