# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Correctness Bugs

## Tier 2: Performance (Hot Path)

1. **SkolemFn registry cloned on every witness search** — `inner.skolem_fn_registry.clone()` appears 3× in hot paths (reasoning.rs). Should iterate by reference. ~3 lines.

4. **all_typed_domain_members().to_vec() cloned on every quantifier evaluation** — The cached slice is already available; `.to_vec()` forces an unnecessary allocation+copy on every ∃/∀ evaluation. ~5 lines in `logji/src/reasoning.rs`.

## Tier 3: Code Quality

5. **Save/restore pattern for substitutions repeated 6+ times** — The `let prev = subs.remove(&key); ... subs.insert(key, member); ... match prev { restore }` pattern is duplicated across `check_formula_holds`, `check_formula_holds_traced`, and `find_witnesses`. Extract to a scoped helper or macro. ~60 lines saved.

6. **assert_fact_inner returns Result but never errors** — Misleading signature. `process_assertion` is infallible, so the Result wrapper on `assert_fact_inner` / `assert_fact_with_id` is dead code. Change to return `u64` directly. ~10 lines in `logji/src/lib.rs`.

## Tier 4: Test Coverage

7. **No tests for compute error propagation** — `dispatch_to_backend` returning `Err` is never tested through `check_formula_holds`. Add test asserting that compute backend errors surface correctly.

8. **No tests verifying memo cache returns cached index** — Tests check that ProofRef steps exist but don't verify that `cached_idx` is actually used. Directly validates the fix for item #1.

9. **No tests for unify_facts edge cases** — Missing coverage for: pattern variable rebinding, SkolemFn nested unification, DepPair unification. ~3 test functions in `logji/src/kb.rs`.

## Tier 5: Infrastructure & Deployment

10. **Fine-grained server locking** — Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in nibli-server (check_mod_deathness panic prevents compilation with RwLock). Retry after rustc upgrade past 1.94.0.
