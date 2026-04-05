# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

## Tier 3: Search Strategy & Performance

1. **Add incremental truth maintenance (TMS)**
    Retraction currently rebuilds the entire KB from surviving base facts. O(KB) per retraction.

    - Add `Justification` to derived facts: which rule + which bindings + which supporting facts.
    - On retraction, walk the dependency cone and retract derived facts recursively.
    - Keep full rebuild as fallback (`:rebuild` REPL command).
    - Tests: retract base fact → derived facts removed, unrelated facts survive.

12. **Selective forward propagation for marked rules**
    Keep backward chaining as primary. Allow opt-in forward propagation for specific rules (e.g., contradiction detection).

    - Add `forward: bool` flag to `UniversalRuleRecord` (default false).
    - On fact assertion, check all `forward: true` rules. If all conditions met, assert conclusion immediately.
    - REPL: `:forward <rule-id>` to mark a rule.
    - Primary use: contradiction detection rules. Secondary: hot derived predicates.

## Tier 4: Code Quality & Measurement

13. **Break up oversized core files**
    - `logji/src/lib.rs` (4,715 lines) → extract `assertion.rs`, `query.rs`, `witness.rs`, `proof.rs`.
    - `gerna/src/grammar.rs` (4,452 lines) → split per-construct (sumti, selbri, sentence parsing).

14. **Add criterion benchmarks**
    - Query latency at 10² / 10³ / 10⁴ facts (parametric).
    - Recursive rule chains (depth 2, 5, 10).
    - Witness extraction over growing domain sizes.
    - Equality-heavy workloads (once equality lands).
    - Retract + rebuild vs retract + TMS (once TMS lands).
    - Store baseline in `benches/baseline.json`.

15. **Publish GUARANTEES.md**
    Formal statement of engine properties: soundness, completeness bounds, negation policy, equality semantics, resource limits, retraction model.


## Others

16. WASI lazy-loading backend: implement WasiFactStore using WASI file I/O (fd_read/fd_write/fd_seek) + LRU cache with per-predicate lazy loading. That's deferred per the todo.
