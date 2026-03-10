## Cross-query memoisation (Phase E of backward-chaining migration)

Extend the `ProofRef` memo table to cache across queries within a session. Key: normalised s-expression. Value: `(holds: bool, proof_step_idx: u32)`. Clear on KB mutation (assert/retract). Currently memo is created fresh per `query_entailment_with_proof_inner` call (no cross-query leakage).

## Deferred / Low Priority

- **Async compute backend** — Current synchronous TCP + JSON Lines protocol is a bottleneck only under heavy external predicate use. Built-in arithmetic bypasses TCP entirely, and auto-ingestion caches results. Move to async (tokio) + binary IPC if external dispatch frequency becomes a real bottleneck.
