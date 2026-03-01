## Deferred / Low Priority

- **Async compute backend** — Current synchronous TCP + JSON Lines protocol is a bottleneck only under heavy external predicate use. Built-in arithmetic bypasses TCP entirely, and auto-ingestion caches results. Move to async (tokio) + binary IPC if external dispatch frequency becomes a real bottleneck.
- **E-graph cycle detection** — Prevent infinite rewrite loops in egglog. May be handled natively by egglog's `(run N)` iteration bound + saturation guarantees. Investigate only if pathological rules surface in practice.
