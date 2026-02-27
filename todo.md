# Nibli — Production Readiness Roadmap

Single-phase backlog ordered by severity: soundness bugs first, then safety, then capability gaps, then improvements.

---

## Soundness Bugs

### S1. Silent partial-parse assertion

When a multi-sentence text has parse failures, `compile_pipeline` asserts the successfully parsed sentences and discards the failures. Warnings are collected but callers (`assert_text`, `query_text`, etc.) discard them with `_warnings`. The user is never told a constraint was dropped.

**Fix:** If any sentence in a multi-sentence assertion fails to parse, abort the entire transaction. Return an error containing both the partial results and the parse errors so the caller can decide policy. For queries (read-only), partial parse is acceptable with warnings surfaced to the user.

**Crate:** orchestrator/lib.rs (`compile_pipeline`, all call sites)
**Severity:** critical — incomplete KB leads to unsound proofs

### S2. Existential introduction gap

`ro lo gerku cu danlu` then `? lo gerku cu danlu` returns FALSE. Engine lacks ∀x.P(x) ⊢ ∃x.P(x) bridging when domain is non-empty. The universal rule fires per entity, but querying via existential over the same predicate doesn't find witnesses if no entity was explicitly asserted for the restrictor.

**Fix:** Add bridge rule in egglog schema: when a universal rule has fired for at least one entity, the consequent should be discoverable via existential query. Alternatively, revisit xorlo presupposition (lo X presupposes at least one X exists).

**Crate:** reasoning/lib.rs (egglog schema)
**Severity:** high — correct logical entailment fails

---

## Runtime Safety

### R1. Wasmtime memory limits

`Store` has fuel limits (CPU) but no memory cap. An adversarial or pathological input creating combinatorial e-graph growth can consume unbounded memory, crashing the host process.

**Fix:** Configure `StoreLimits` with a hard memory cap on the `wasmtime::Store`. Make it configurable via `NIBLI_MEMORY_MB` env var and `:memory` REPL command, defaulting to a reasonable bound (e.g., 512 MB).

**Crate:** runner/src/main.rs
**Severity:** high — production safety requirement

### R2. inject_variable ambiguity in nested descriptions

When a relative clause lacks explicit `ke'a` and contains nested descriptions, `inject_variable` injects the bound variable into restrictor predicates of inner descriptions, corrupting the logic graph. Currently documented + warned at runtime, but the heuristic can silently produce wrong FOL.

**Fix:** Replace tree-walk heuristic with a strict "open slot" index tracker during AST lowering. Track which predicate introduced each `Unspecified` slot and only inject into the clause's own top-level predicate. Alternatively, require `ke'a` when ambiguity is detected (promote warning to error).

**Crate:** semantics/src/semantic.rs (`inject_variable`)
**Severity:** medium — only affects implicit `ke'a` in complex relative clauses

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
