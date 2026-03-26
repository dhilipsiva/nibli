# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: DRY Consolidation (Medium Effort, High Impact)

## Tier 5: Maintainability

12. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals. Some already configurable (fuel, memory); pattern is inconsistent.

13. **WIT schema versioning** — No migration path for WIT interface evolution.

## Tier 6: Infrastructure & Deployment

14. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with per-resource locks or `RwLock`.

15. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint.

16. **Guard `RefCell` against non-WASM misuse** — Add `#[cfg]` compile-time guards.

17. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections.

18. **Gossip envelope expiration** — CRDT log is append-only with no TTL.
