# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

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
