# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Correctness Bugs

## Tier 2: Performance (Hot Path)

## Tier 3: Code Quality

## Tier 4: Infrastructure & Deployment

10. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in nibli-server (check_mod_deathness panic prevents compilation with RwLock). Retry after rustc upgrade past 1.94.0.

## Others

11. Ensure that the whole codebase does not abrubtly panic anywhere (especially in the core engine). It must always fail gracefully (atleast ensure it panics with proper messages so debugging becomes easier).
