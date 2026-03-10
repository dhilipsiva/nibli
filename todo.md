## Refactor

1. Analyse the entire codebase. If there is some part of the code that can be simplified (reduce unwanted algorithmic complexity) without affecting correctness or functionality, let us please so those.
2. Analuse the entire codebase. If there is some part of the code that can be optimized for performance without sacrificing correctness or functionality, let us do that. 
2. Analyse the entite codebase. If there is some part of the code that can be refactored for better name without sacrificing correcness or performance, let us do that.
4. Analyse the entire codebase. Is there is some part fo the code that cab en refactored for readability (improve naming, types, algorithm), let us fo that


## Cross-query memoisation (Phase E of backward-chaining migration)

Extend the `ProofRef` memo table to cache across queries within a session. Key: normalised s-expression. Value: `(holds: bool, proof_step_idx: u32)`. Clear on KB mutation (assert/retract). Currently memo is created fresh per `query_entailment_with_proof_inner` call (no cross-query leakage).

## Deferred / Low Priority

- **Async compute backend** — Current synchronous TCP + JSON Lines protocol is a bottleneck only under heavy external predicate use. Built-in arithmetic bypasses TCP entirely, and auto-ingestion caches results. Move to async (tokio) + binary IPC if external dispatch frequency becomes a real bottleneck.
