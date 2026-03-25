# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Pipeline Efficiency (Medium Effort, High Impact)

4. **Consolidate proof trace + error formatting** — Proof tree formatting in both `nibli-protocol/src/lib.rs` and `gasnu/src/main.rs`. Error formatting repeated 3× in `nibli-engine/src/lib.rs`. Term serialization duplicated between `lasna` and `nibli-engine`. Consolidate to `nibli-protocol`. ~130 lines saved.

10. **known_rules dedup key** — `HashSet<String>` uses full serialized rule as dedup key. Switch to structural hash of typed conditions/conclusions for O(1) dedup instead of O(k) string hashing.

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
