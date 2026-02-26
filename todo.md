# Nibli Roadmap

## Tier 3 — Domain-Specific Language Coverage

Features needed to express domain knowledge naturally in Lojban.

### 3.2 `sa` proper implementation

Requires selma'o classification for the erasure-to-next-construct behavior.

**Crate:** parser/preprocessor.rs
**Complexity:** medium

---

## Tier 4 — Production Reasoning Features

Features needed for the engine to be genuinely useful (not just correct) in real applications.

### 4.1 Existential witness extraction (answer variables)

`query_entailment` returns bool. Need: `query_find` returning bindings. "ma klama" → "mi". The `check_formula_holds` existential branch already enumerates entities — capture the successful binding.

**Crate:** reasoning/lib.rs, WIT interface (new export)
**Complexity:** medium
**Impact:** every domain — "what satisfies this?" is the most natural query form

### 4.2 Proof trace generation

`check_formula_holds` builds proof tree as it recurses. Each node records which rule/axiom was applied.

**Crate:** reasoning/lib.rs
**Complexity:** medium-high
**Impact:** legal (arguments require justification), scientific (reproducibility), astrophysics (audit trail for derived conclusions)

### 4.3 Parser error recovery

Skip to next `.i` on syntax error, continue parsing. Return `Vec<Result<Sentence, SyntaxError>>` instead of failing entire input.

**Crate:** parser/grammar.rs
**Complexity:** medium
**Impact:** all domains — real corpora have errors; failing on first bad sentence is unusable

### 4.4 WASM fuel/epoch limits

Prevent unbounded execution. Wasmtime API supports natively.

**Crate:** runner/main.rs
**Complexity:** low
**Blocks:** production deployment

### 4.5 Conjunction introduction rule (guarded)

Assert A, assert B → egglog can derive `And(A, B)`. Guard: only fire when both A, B are atomic predicates sharing at least one term. Prevents combinatorial explosion.

**Crate:** reasoning/lib.rs schema
**Complexity:** low

### 4.6 WIT error variants

Replace `Result<_, String>` with typed error enums: `SyntaxError(pos)`, `SemanticError(msg)`, `ReasoningTimeout`, `BackendError(backend, msg)`.

**Crate:** wit/world.wit, all 4 components
**Complexity:** medium

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

## Deferred / Known Gaps

Items identified during implementation but not yet prioritized into a tier.

- **Existential introduction gap** — `ro lo gerku cu danlu` then `? lo gerku cu danlu` returns FALSE. Engine lacks ∀x.P(x) ⊢ ∃x.P(x) bridging when domain is non-empty. Revisit xorlo presupposition.
- **SkolemFn multi-dependency** — Currently supports dep_count=1 only (single universal dependency). Multi-dependency (`∀x.∀y. → ∃z.`) needs SkolemPair or TermList encoding. Deferred until needed.

