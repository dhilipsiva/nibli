# Nibli Roadmap

## Tier 1 — Architecture for Scale (the gate to real domains)

Without this tier, the engine caps out at ~100 entities. Science and legal domains need 1K-50K+.

### 1.1 Native egglog rules — Phase B: Dependent Skolem functions

**Phase A complete.** Simple universals (no ∃ under ∀) now compile to native egglog rules with O(K) hash-join matching. Old Herbrand fallback retained for dependent-Skolem universals.

**Remaining:** Add `SkolemFn` term to egglog schema for dependent Skolems (`∀x. P(x) → ∃y. R(x,y)`). The rule head creates `(SkolemFn "sk_N" (Cons x (Nil)))` — a unique witness per entity. Requires query-side SkolemFn witness registry for existential enumeration. Then remove all remaining Herbrand machinery (`UNIVERSAL_TEMPLATES`, `register_entity`, `instantiate_for_entity`, `collect_forall_nodes`).

**Also still pending:**
- Existential introduction gap (0.2 deferred) — revisit xorlo presupposition after Phase B
- String replacement fragility (0.3 deferred) — fully eliminated once Phase B removes Herbrand fallback

**Crate:** reasoning/lib.rs
**Complexity:** medium (Phase A infrastructure in place)
**Blocks:** full elimination of O(E×T) cross-product

### 1.2 WASI state hoisting (replaces `OnceLock` anti-pattern)

Move knowledge base to host-managed WASI Resource. Enables: reset, multi-tenant, persistence.

Current `OnceLock<Mutex<EGraph>>` works only because the runner reuses a single component instance. The `Mutex` is unnecessary overhead in single-threaded WASI. If wasmtime ever instantiates fresh, all state is silently lost.

**Crate:** reasoning/lib.rs, runner/main.rs
**Complexity:** high (architectural rework)
**Blocks:** persistence, multi-tenant deployment, clean `:reset`

### 1.3 `reconstruct_sexp` deduplication

Orchestrator and reasoning have near-identical copies of `reconstruct_sexp`. Extract into shared utility or unify via the WIT interface.

**Note:** If 1.1 removes `reconstruct_sexp` from reasoning entirely, this becomes moot — just verify orchestrator's copy is the sole survivor.

**Crate:** orchestrator, reasoning
**Complexity:** low

### 1.4 String pre-allocation in `reconstruct_sexp`

Currently O(n^2) from nested `format!` calls. Use a `String` buffer with `write!` or pre-calculate capacity.

**Note:** Reduced in scope if 1.1 eliminates the reasoning-side copy.

**Crate:** reasoning, orchestrator
**Complexity:** low

### 1.5 wasip1 → wasip2 alignment

Ensure Justfile and flake.nix target consistent WASI preview version.

**Crate:** Justfile, flake.nix
**Complexity:** low

### 1.6 Remove `bumpalo` dependency

Imported but unused — dead weight in WASM binary.

**Crate:** parser/Cargo.toml
**Complexity:** trivial (2 min)

### 1.7 Delete dead `push_bridi` method in Flattener

Superseded by `push_sentence`, generates unused-code warning.

**Crate:** parser/lib.rs lines 82-113
**Complexity:** trivial (2 min)

### 1.8 Delete dead commented-out loop in `Flattener::flatten`

**Crate:** parser/lib.rs lines 68-76
**Complexity:** trivial (1 min)

### 1.9 `ast-types` WIT interface naming

Split logic types into separate WIT interface from AST types. Currently both live in `ast-types` which is misleading.

**Crate:** wit/world.wit
**Complexity:** medium

---

## Tier 2 — Quantitative Reasoning (science needs numbers and computation)

Without this tier, the engine can only do qualitative symbolic reasoning. Every scientific domain needs quantitative capabilities.

### 2.1 Numerical comparison predicates in egglog

`zmadu`/`mleca`/`dunli` operating on `Num` terms. The `Num` datatype already exists in the schema.

**Crate:** reasoning/lib.rs schema
**Complexity:** medium
**Impact:** astrophysics (magnitude comparisons, orbital parameters), chemistry (bond energies, molecular weights), legal (monetary thresholds, statutory limits)

### 2.2 Computation dispatch WIT protocol

New interface: `compute-backend` with dispatch function. New IR node: `ComputeNode`. Predicate registry marks which predicates dispatch externally.

**Crate:** new crate + WIT interface
**Complexity:** high
**Impact:** unlocks all quantitative science — without external computation, the engine can only do symbolic manipulation

### 2.3 Python backend adapter

Subprocess or embedded. Covers SciPy, NumPy, AstroPy, SymPy, RDKit, BioPython, MadGraph, PK/PD solvers.

**Depends on:** 2.2
**Complexity:** medium
**Impact:** the bridge between symbolic reasoning and numerical computation

### 2.4 Result ingestion as assertions

Computation results → Lojban assertions → knowledge base. Closes the reason→compute→reason loop. Needs trusted assertion path (bypass user input parsing).

**Depends on:** 2.2, 2.3
**Complexity:** medium

---

## Tier 3 — Domain-Specific Language Coverage

Features needed to express domain knowledge naturally in Lojban.

### 3.1 Deontic predicates (`bilga`/`curmi`/`nitcu`)

Predicate-based deontic modality: `bilga` (obligated), `curmi` (permitted), `nitcu` (needed). These are standard gismu — should work if dictionary arity entries exist.

Attitudinal forms (`e'e`/`ei`) require new parser category — defer to 3.1b.

**Crate:** semantics/dictionary, parser (if attitudinal)
**Complexity:** low (predicate) or high (attitudinal)
**Impact:** critical for legal corpus (obligation, permission, prohibition)

### 3.2 Lujvo morphological recognition

Lexer only recognizes gismu (5-letter CVCCV/CCVCV) and cmavo. Lujvo (compound brivla like `brivla`, `nunprami`) fall through.

**Approach:** Dictionary lookup at lex time — check if token is a known lujvo from jbovlaste (already in PHF map from `build.rs`). Handles ~95% of real text.

**Crate:** parser/lexer.rs
**Complexity:** medium
**Impact:** all domains — real Lojban text uses compound words heavily

### 3.3 Observative sentences

`mi do` (observative, implicit `go'i`) currently errors. Low priority but affects naturalness of input.

**Crate:** parser/grammar.rs
**Complexity:** medium (requires `go'i` pro-bridi resolution)

### 3.4 `sa` proper implementation

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

## Dependency Graph

```
Tier 0 (correctness)
  0.1 da/de/di closure ── no dependencies, do anytime
  0.2 existential introduction gap ── partially solved by 1.1
  0.3 string replacement ── eliminated by 1.1

Tier 1 (scale)                        Tier 2 (quantitative)
  1.1 native egglog rules               2.1 numerical predicates
       │                                 2.2 computation dispatch WIT
       ├── eliminates 0.3                     │
       ├── partially solves 0.2          2.3 Python adapter ──→ 2.4 result ingestion
       ├── may make 1.3, 1.4 moot
       └── enables Tier 4, 5
  1.2 WASI state hoisting
       └── enables persistence, multi-tenant

Tier 3 (language)         Tier 4 (production)         Tier 5 (advanced)
  3.1 deontic               4.1 witness extraction      5.1 non-monotonic
  3.2 lujvo                 4.2 proof traces            5.2 temporal
  3.3 observative           4.3 error recovery          5.3 event semantics
  3.4 sa impl               4.4 fuel limits             5.4 description opacity
                            4.5 conj. introduction      5.5 namespaces
                            4.6 WIT error variants      5.6 cycle detection
                            4.7 WASI sandboxing
                            4.8 clone elimination
                            4.9 arena allocator
```
