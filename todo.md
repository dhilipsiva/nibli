# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 6: Infrastructure & Deployment

14. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in nibli-server (check_mod_deathness panic prevents compilation with RwLock). Retry after rustc upgrade past 1.94.0.

15. **Guard `RefCell` against non-WASM misuse** — Add `#[cfg]` compile-time guards.

17. **Stale TCP connection cleanup in gasnu** — No idle timeout on compute backend connections.

18. **Gossip envelope expiration** — CRDT log is append-only with no TTL.
