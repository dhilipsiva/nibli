# Nibli Roadmap

## Tier 4 — Production Reasoning Features

Features needed for the engine to be genuinely useful (not just correct) in real applications.

### 4.7 WASI capability sandboxing

Remove `inherit_stdio()`. Grant minimal capabilities.

**Crate:** runner/main.rs
**Complexity:** low

### 4.8 Remove deep clones in `apply_selbri` for `Jo`/`Ju` connectives

Restructure to avoid cloning recursive `LogicalForm` trees.

**Crate:** semantics/semantic.rs lines 421-438
**Complexity:** low

### 4.9 Arena allocator for parser AST

Batch processing of corpora will stress the allocator. Arena allocation reduces fragmentation and improves throughput.

**Crate:** parser
**Complexity:** medium

---

## Tier 5 — Advanced Reasoning

Features for complex domains that require deeper logical machinery.

### 5.1 Non-monotonic reasoning / belief revision

Retraction + justification tracking (TMS-style). egglog doesn't natively support retraction — needs wrapper layer.

**Crate:** reasoning (new subsystem)
**Complexity:** very high
**Impact:** legal corpus (statutes get amended/repealed, precedent overturned), biology (hypothesis revision), any evolving knowledge base

### 5.2 Temporal reasoning in e-graph

Encode Past/Present/Future in egglog schema with inference rules. Currently tense is stripped at assertion and transparent at query — asserting `pu mi klama` and querying `ba mi klama` returns TRUE (wrong).

**Crate:** reasoning/lib.rs schema + `check_formula_holds`
**Complexity:** high
**Impact:** astrophysics (stellar evolution, cosmological timelines), legal (effective dates, statute of limitations), biology (developmental stages)

### 5.3 Event semantics (Neo-Davidsonian)

Structured events with named roles, temporal ordering, causal links. Resolves tanru intersective fallacy.

**Complexity:** research-grade
**Impact:** physics (physical processes), legal (actions and liability), biology (metabolic pathways)

### 5.4 Description term opacity (`le` vs `lo`)

Currently `le` and `la` both produce `LogicalTerm::Description` — a non-quantified opaque token. Matters for belief contexts and intensional reasoning.

**Crate:** semantics/semantic.rs, reasoning schema
**Complexity:** high

### 5.5 Module / namespace system

Domain-prefixed predicates for multi-domain KBs. Essential when combining astrophysics + chemistry ontologies or multiple legal codes.

**Complexity:** medium

### 5.6 E-graph cycle detection

Prevent infinite rewrite loops in egglog. May be handled natively by egglog's saturation guarantees.

**Complexity:** medium

---

## Tier 6 — Derivation Provenance

### 6.1 Multi-hop derivation chain recording

Current proof traces only show "found in egglog" for facts derived via rule saturation, because egglog derives facts at assertion time (during saturation) — not at query time. The proof trace cannot reconstruct *how* a fact was derived (e.g., `gerku(alis) → danlu(alis) → xanlu(alis)` via two universal rules).

Record the full derivation chain so proof traces show which rule fired at each hop, what premises matched, and what conclusion was produced. Must be efficient — derivation recording happens during saturation (hot path), so cannot add significant per-rule overhead.

**Possible approaches:**
- **egglog proof extraction** — egglog may expose proof terms natively; investigate upstream API
- **Shadow derivation log** — lightweight append-only log recording `(rule-id, premises, conclusion)` tuples during saturation; proof trace reconstructs chain by walking backwards from queried fact
- **Annotated e-nodes** — tag each e-node with its derivation parent(s); amortized O(1) per rule firing, O(depth) reconstruction at query time

**Crate:** reasoning/lib.rs
**Complexity:** high
**Constraint:** must be performant — saturation is the inner loop; derivation recording must not degrade throughput significantly

---

## Deferred / Known Gaps

Items identified during implementation but not yet prioritized into a tier.

- **Existential introduction gap** — `ro lo gerku cu danlu` then `? lo gerku cu danlu` returns FALSE. Engine lacks ∀x.P(x) ⊢ ∃x.P(x) bridging when domain is non-empty. Revisit xorlo presupposition.
- **SkolemFn multi-dependency** — Currently supports dep_count=1 only (single universal dependency). Multi-dependency (`∀x.∀y. → ∃z.`) needs SkolemPair or TermList encoding. Deferred until needed.

