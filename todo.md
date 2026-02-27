# Nibli — Production Readiness Roadmap

Single-phase backlog ordered by severity: soundness bugs first, then safety, then capability gaps, then improvements.

---

## Capability Gaps

### C1. Multi-hop derivation provenance

Proof traces show "found in egglog" for facts derived via rule saturation. Cannot reconstruct the causal chain (e.g., `gerku(alis) → danlu(alis) → xanlu(alis)` via two universal rules).

**Possible approaches:**
- egglog proof extraction — investigate upstream API for proof terms
- Shadow derivation log — append-only `(rule-id, premises, conclusion)` tuples during saturation; reconstruct by walking backwards from queried fact
- Annotated e-nodes — tag each e-node with derivation parent(s); O(1) per rule firing, O(depth) at query time

**Crate:** reasoning/lib.rs
**Complexity:** high
**Constraint:** derivation recording is on the saturation hot path; must not degrade throughput

### C2. Non-monotonic reasoning / belief revision

Retraction + justification tracking (TMS-style). egglog doesn't natively support retraction — needs wrapper layer. Required for any evolving knowledge base (legal corpus where statutes get amended/repealed, biology with hypothesis revision).

**Crate:** reasoning (new subsystem)
**Complexity:** very high

### C3. Temporal reasoning in e-graph

Encode Past/Present/Future in egglog schema with inference rules. Currently tense is stripped at assertion and transparent at query — asserting `pu mi klama` and querying `ba mi klama` returns TRUE (wrong).

**Crate:** reasoning/lib.rs schema + `check_formula_holds`
**Complexity:** high

### C4. Event semantics (Neo-Davidsonian)

Structured events with named roles, temporal ordering, causal links. Resolves tanru intersective fallacy.

**Complexity:** research-grade

### C5. Description term opacity (`le` vs `lo`)

Currently `le` and `la` both produce `LogicalTerm::Description` — a non-quantified opaque token. Matters for belief contexts and intensional reasoning.

**Crate:** semantics/semantic.rs, reasoning schema
**Complexity:** high

### C6. Module / namespace system

Domain-prefixed predicates for multi-domain KBs. Essential when combining astrophysics + chemistry ontologies or multiple legal codes.

**Complexity:** medium

---

## Deferred / Low Priority

- **SkolemFn multi-dependency** — Currently supports dep_count=1 only (single universal dependency). Multi-dependency (`∀x.∀y. → ∃z.`) needs SkolemPair or TermList encoding. Deferred until needed.
- **Async compute backend** — Current synchronous TCP + JSON Lines protocol is a bottleneck only under heavy external predicate use. Built-in arithmetic bypasses TCP entirely, and auto-ingestion caches results. Move to async (tokio) + binary IPC if external dispatch frequency becomes a real bottleneck.
- **E-graph cycle detection** — Prevent infinite rewrite loops in egglog. May be handled natively by egglog's `(run N)` iteration bound + saturation guarantees. Investigate only if pathological rules surface in practice.
