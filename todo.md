# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Dead Code Cleanup (Low Effort, High Impact)

1. **Delete dead WIT export stubs** — `struct GernaComponent`, `struct SmuniComponent`, `bindings::export!()` macros in gerna/smuni/logji are `#[cfg(target_arch = "wasm32")]` and unreachable. Remove all cfg-gated export infrastructure from these 3 crates.

3. **Simplify crate-type** — gerna, smuni, logji Cargo.toml have `crate-type = ["cdylib", "lib"]` but cdylib is never built. Change to `["lib"]`.

4. **Inline thin wrapper debug_logic()** — `lasna/src/lib.rs` and `nibli-engine/src/lib.rs` each have a one-liner `debug_logic()` that just calls `logji::repr::debug_logic()`. Inline at call sites.

5. **Flatten nibli-engine module aliases** — `mod gerna_err`, `mod smuni_err`, `mod logji_logic`, `mod logji_err` are unnecessary indirection. Use direct paths.

## Tier 5: Maintainability

12. **Make hardcoded constants configurable** — Backward-chaining depth limit (10), UI GraphQL URL, MAX_OUTPUT_ENTRIES (200), polling intervals. Some already configurable (fuel, memory); pattern is inconsistent.

13. **WIT schema versioning** — No migration path for WIT interface evolution.

## Tier 6: Infrastructure & Deployment

14. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with per-resource locks or `RwLock`.

15. **Runtime-configurable UI server URL** — `nibli-ui` hardcodes the GraphQL endpoint.

16. **Guard `RefCell` against non-WASM misuse** — Add `#[cfg]` compile-time guards.

17. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections.

18. **Gossip envelope expiration** — CRDT log is append-only with no TTL.
