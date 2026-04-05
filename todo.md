# Nibli — Reasoning Engine Backlog

Ordered by dependency, correctness impact, then user value.

1. **Publish GUARANTEES.md**
    Formal statement of engine properties: soundness, completeness bounds, negation policy, equality semantics, resource limits, retraction model.


## Others

16. WASI lazy-loading backend: implement WasiFactStore using WASI file I/O (fd_read/fd_write/fd_seek) + LRU cache with per-predicate lazy loading. That's deferred per the todo.
