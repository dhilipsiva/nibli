# Scaling & Correctness Fixes Plan

## 1. Remove transactional clone-per-assertion

**Problem:** `assert_fact_inner()` clones the entire `KnowledgeBaseInner` (~15 fields, multiple HashSets/HashMaps) before every assertion, then swaps on success. `process_assertion()` never actually returns `Err` (verified: `compile_forall_to_rule` always returns `Ok(())`).

**Fix:** Remove the clone-then-swap pattern. Mutate `inner` directly. Since `process_assertion` is infallible, the transactional pattern is pure overhead.

- Change `assert_fact_inner` to borrow_mut and operate in-place
- Change `assert_fact_with_id` similarly
- Remove `let mut staged = inner.clone()` + `*inner = staged` pattern

**Risk:** Zero — the function never fails, so rollback never triggers.

## 2. Negation-as-failure analysis

**Current state:** `NotNode` is already NAF: `!check_formula_holds(inner)`. This is sound for the current system because:
- Assertions are ground facts or universal rules (Horn clauses with negation in conditions)
- Negation only appears in material conditionals (`ganai...gi` compiles to `Or(Not(P), Q)`)
- No recursive negation or circular definitions exist in Lojban input
- The system is stratifiable by construction (facts at stratum 0, rules at stratum 1)

**Conclusion:** No code change needed. The system already has sound NAF for its use case. Document this in a code comment.

## 3. Optimize brute-force witness search

**Problem:** `find_witnesses` for `ExistsNode` iterates ALL domain members (entities + descriptions + SkolemFn combinations) for each existential variable. For nested `∃x.∃y.P(x,y)` with N domain members, this is O(N²).

**Fix: Index-driven candidate narrowing.** Instead of trying all domain members blindly, use the predicate index (`typed_predicate_facts`) to extract only the arguments that actually appear in matching facts.

For `∃x. P(x, adam)` where `x` is unbound:
- Current: try all N domain members, check `P(member, adam)` for each
- Optimized: look up `typed_predicate_facts["P"]`, filter facts matching `(_, adam)` pattern, extract x values directly

This turns O(N) into O(|matching facts for P|), which is typically much smaller.

Implementation:
- Add `fn candidate_values_for_predicate()` in reasoning.rs
- In `find_witnesses` ExistsNode handler, before the brute-force loop, check if the body is a simple predicate with the existential var in a known position
- If so, use index-driven lookup; otherwise fall back to brute-force
- The SkolemFn cartesian product loop can remain as fallback (rarely triggered)

## Files touched

- `logji/src/lib.rs` — remove clone-per-assertion (~10 lines changed)
- `logji/src/reasoning.rs` — add candidate narrowing for witness search (~40 lines)
- `logji/src/kb.rs` — add helper for extracting candidates from predicate index
