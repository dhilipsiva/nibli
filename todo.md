# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Correctness Bugs

## Tier 2: Performance (Hot Path)

## Tier 3: Code Quality

## Tier 4: Test Coverage

1. **No tests for compute error propagation** — `dispatch_to_backend` returning `Err` is never tested through `check_formula_holds`. Add test asserting that compute backend errors surface correctly.

8. **No tests verifying memo cache returns cached index** — Tests check that ProofRef steps exist but don't verify that `cached_idx` is actually used. Directly validates the fix for item #1.

9. **No tests for unify_facts edge cases** — Missing coverage for: pattern variable rebinding, SkolemFn nested unification, DepPair unification. ~3 test functions in `logji/src/kb.rs`.

## Tier 5: Infrastructure & Deployment

10. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in nibli-server (check_mod_deathness panic prevents compilation with RwLock). Retry after rustc upgrade past 1.94.0.

## Others

11. Ensure that the whole codebase does not abrubtly panic anywhere (especially in the core engine). It must always fail gracefully (atleast ensure it panics with proper messages so debugging becomes easier).
