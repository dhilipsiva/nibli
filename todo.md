### 1.3 BAI modal tags (minimum viable set: `ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`, `fi'o...fe'u`)

New grammatical category. BAI tags create a new predicate relation rather than filling an existing place. `mi klama ri'a lo nu brife` → "I go, caused-by the event of wind."

Semantics: conjoined predication with modal relation connecting main bridi to tagged sumti.

**Crate:** parser (new tag class), semantics (modal predication)
**Complexity:** high
**Needed by:** causation in every domain

### 1.4 Numeric quantifiers (`re lo`, `ci lo`, `su'o`, `no`)

Parser: number + gadri in quantifier position. Semantics: existential with cardinality constraint. Expanding "exactly N" in raw FOL is verbose — add a dedicated `CountNode` in the IR.

**Crate:** parser/grammar.rs, semantics/ir.rs, semantics/semantic.rs
**Complexity:** medium

### 1.5 Afterthought sentence connectives (`.i je` / `.i ja` / `.i naja` / `.i jo`)

Parser: recognize connective after `.i`. Semantics: combine adjacent sentence logic forms.

**Crate:** parser/grammar.rs
**Complexity:** low

### 1.6 Relative clause stacking + `voi`

`voi` (non-veridical restrictive) missing. Can't stack multiple relative clauses. Needed for: "the protein which binds ATP and which is phosphorylated."

**Crate:** parser/grammar.rs, parser/ast.rs
**Complexity:** low-medium

### 1.7 Deontic predicates (`bilga`/`curmi`/`nitcu`/`e'e`/`ei`)

If predicate-based: `bilga`/`curmi` already work as gismu, just need dictionary arity entries. If attitudinal-based: new parser category required.

**Crate:** semantics/dictionary, parser (if attitudinal)
**Complexity:** low (predicate) or high (attitudinal)

### 1.8 `[NEW]` `da`/`de`/`di` quantifier closure

Currently compiled as free `Variable(Spur)` with no quantifier wrapping. `da prami mi` should produce `∃x.prami(x, mi)`, not an open formula with free `da`.

**Fix:** In `compile_bridi`, after building the predication, scan the args for pro-sumti `da`/`de`/`di`. For each, wrap the final form in `Exists(var, ...)`.

**Crate:** semantics/semantic.rs `compile_bridi`
**Complexity:** low-medium
**Needed by:** correct reasoning on any sentence using `da`/`de`/`di`

### 1.9 `[NEW]` Lujvo morphological recognition

Lexer only recognizes gismu (5-letter CVCCV/CCVCV) and cmavo. Lujvo (compound brivla like `brivla`, `nunprami`) fall through to Cmavo or Cmevla depending on ending. The `Compound` selbri variant exists but is only populated via `zei`-gluing.

**Options:**
- (a) Dictionary lookup at lex time — check if token is a known lujvo from jbovlaste (already have the dictionary at build time). Low complexity, high coverage.
- (b) Rafsi decomposition — algorithmic, handles novel lujvo. High complexity, complete.

Start with (a). The jbovlaste phf map already includes lujvo entries from `build.rs`.

**Crate:** parser/lexer.rs (or post-lex classification pass)
**Complexity:** medium
**Needed by:** any Lojban text using compound words

### 1.10 `[NEW]` Observative sentences

`mi do` (observative, implicit `go'i`) currently errors: "observative sentences not yet supported." Low priority but affects naturalness.

**Crate:** parser/grammar.rs
**Complexity:** medium (requires `go'i` pro-bridi resolution)


## PHASE 2 — Reasoning Engine Correctness + Power

egglog schema + Rust-side reasoning changes.

### 2.1 `[AMENDED]` WASI state hoisting (replaces `OnceLock` anti-pattern)

Move knowledge base to host-managed WASI Resource. Enables: reset, multi-tenant, persistence. Subsumes `:reset` command and persistence layer.

**Additional context from review:** Current `OnceLock<Mutex<EGraph>>` works only because the runner reuses a single component instance. The `Mutex` is unnecessary overhead in single-threaded WASI. If wasmtime ever instantiates fresh, all state is silently lost. This is the most fragile part of the architecture.

**Crate:** reasoning/lib.rs, runner/main.rs
**Complexity:** high (architectural rework)
**Blocks:** 2.2, 2.5, deployment, `:reset`

### 2.2 Herbrand explosion → egglog native rules

Replace eager N×M entity grounding with lazy `(rule ...)` definitions. Current approach hits wall at ~10K entities.

**Crate:** reasoning/lib.rs
**Complexity:** high
**Blocks:** scaling to real datasets

### 2.3 Numerical comparison predicates in egglog

`zmadu`/`mleca`/`dunli` operating on `Number` terms. Requires 0.5 (`Num` datatype) first.

**Crate:** reasoning/lib.rs schema
**Complexity:** medium
**Depends on:** 0.5

### 2.4 Conjunction introduction rule (guarded)

Assert A, assert B → egglog can derive `And(A, B)`. Guard: only fire when both A, B are atomic predicates sharing at least one term. Prevents combinatorial explosion.

**Crate:** reasoning/lib.rs schema
**Complexity:** low

### 2.5 Existential witness extraction (answer variables)

`query_entailment` → bool. Need: `query_find` → bindings. "ma klama" → returns "mi". Modify `check_formula_holds` to return successful bindings. Existential branch already enumerates entities — capture the match.

**Crate:** reasoning/lib.rs, WIT interface (new export)
**Complexity:** medium

### 2.6 Non-monotonic reasoning / belief revision

Retraction + justification tracking (TMS-style). egglog doesn't natively support retraction — needs wrapper layer.

**Crate:** reasoning (new subsystem)
**Complexity:** very high

### 2.7 `[NEW]` Herbrand instantiation via string replacement is fragile

`body_sexp.replace(&format!("(Var \"{}\")", var_name), ...)` does global string substitution. If variable names are substrings of other variables (`_v1` inside `_v10`), or appear in predicate names, silent corruption occurs.

**Fix:** Use proper s-expression tree manipulation instead of string replacement. Or ensure variable names are always terminated by `"` in the sexp format (which they currently are due to quoting — verify this invariant holds).

**Crate:** reasoning/lib.rs `register_entity`, Herbrand instantiation
**Complexity:** low (verification) or medium (proper tree manip)


## PHASE 3 — Security + Deployment Readiness

### 3.1 WASM fuel/epoch limits

Prevent unbounded execution. Wasmtime API supports natively.

**Crate:** runner/main.rs
**Complexity:** low
**Blocks:** production deployment

### 3.2 WIT error variants

Replace `Result<_, String>` with typed error enums: `SyntaxError(pos)`, `SemanticError(msg)`, `ReasoningTimeout`, `BackendError(backend, msg)`.

**Crate:** wit/world.wit, all 4 components
**Complexity:** medium

### 3.3 WASI capability sandboxing

Remove `inherit_stdio()`. Grant minimal capabilities.

**Crate:** runner/main.rs
**Complexity:** low

### 3.4 Parser error recovery

Skip to next `.i` on syntax error, continue parsing. Return `Vec<Result<Sentence, SyntaxError>>` instead of failing entire input.

**Crate:** parser/grammar.rs
**Complexity:** medium

### 3.5 Explanation / proof trace generation

`check_formula_holds` builds proof tree as it recurses. Each node records which rule/axiom was applied.

**Crate:** reasoning/lib.rs
**Complexity:** medium-high
**Needed by:** every high-stakes domain


## PHASE 4 — Computation Dispatch

### 4.1 Computation dispatch WIT protocol

New interface: `compute-backend` with dispatch function. New IR node: `ComputeNode`. Predicate registry marks which predicates dispatch externally.

**Crate:** new crate + WIT interface
**Complexity:** high

### 4.2 Python backend adapter

Subprocess or embedded. Covers SciPy, SymPy, RDKit, BioPython, MadGraph, PK/PD solvers.

**Complexity:** medium

### 4.3 Mathematica/Wolfram backend adapter

Via WSTP or WolframScript CLI.

**Complexity:** medium

### 4.4 Result ingestion as assertions

Computation results → Lojban assertions → knowledge base. Closes the reason→compute→reason loop. Needs trusted assertion path (bypass user input parsing).

**Complexity:** medium


## PHASE 5 — Theoretical Depth

### 5.1 Event semantics (Neo-Davidsonian)

Structured events with named roles, temporal ordering, causal links. Resolves tanru intersective fallacy.

**Complexity:** research-grade

### 5.2 Temporal reasoning in e-graph

Encode Past/Present/Future in egglog schema with inference rules. Current tense-transparent approach becomes dispatch point.

**Additional context:** Currently tense is stripped at assertion and transparent at query — asserting `pu mi klama` and querying `ba mi klama` will return TRUE. This is the first thing that breaks when encoding any temporally-sensitive domain.

**Crate:** reasoning/lib.rs schema + `check_formula_holds`
**Complexity:** high

### 5.3 `[AMENDED]` Description term opacity (`le` vs `lo`)

Currently `le` and `la` both produce `LogicalTerm::Description` — a non-quantified opaque token. The reasoning engine can't distinguish `le gerku` from `la gerku` at the logic level. Matters for belief contexts and intensional reasoning.

**Crate:** semantics/semantic.rs, reasoning schema
**Complexity:** high

### 5.4 E-graph cycle detection

Prevent infinite rewrite loops in egglog.

**Complexity:** medium (egglog may handle natively)

### 5.5 Module / namespace system

Domain-prefixed predicates for multi-domain KBs.

**Complexity:** medium


## ONGOING — Technical Debt

Interleave as convenient.

| ID | Item | Crate | Complexity |
|----|-------|-------|------------|
| D.1 | wasip1 → wasip2 alignment | Justfile, flake.nix | low |
| D.2 | `reconstruct_sexp` deduplication (orchestrator + reasoning have near-identical copies) | orchestrator, reasoning | low |
| D.3 | `ast-types` interface naming (split logic types into separate WIT interface) | wit/world.wit | medium |
| D.4 | String pre-allocation in `reconstruct_sexp` (currently O(n²) from nested `format!`) | reasoning, orchestrator | low |
| D.5 | Arena allocator for parser AST (when batch processing) | parser | medium |
| D.6 | `sa` proper implementation (requires selma'o classification) | parser/preprocessor.rs | medium |
| D.7 | `inject_variable` ambiguity warning (when multiple Unspecified slots and no ke'a) | semantics/semantic.rs | low |
| D.8 | `[NEW]` Remove `bumpalo` dependency from parser — imported but unused, dead weight in WASM binary | parser/Cargo.toml | 2 min |
| D.9 | `[NEW]` Delete dead `push_bridi` method in Flattener — superseded by `push_sentence` | parser/lib.rs lines 82-113 | 2 min |
| D.10 | `[NEW]` Delete dead commented-out loop in `Flattener::flatten` | parser/lib.rs lines 68-76 | 1 min |
| D.11 | `[NEW]` Fix or remove `looks_like_selbri_na` — dead code behind `#[allow(dead_code)]`, will break if used (missing cmavo-selbri like `go'i`) | parser/grammar.rs lines 335-349 | low |
| D.12 | `[NEW]` Verify Flattener test type correctness — tests construct `ParsedText { sentences: vec![Bridi {...}] }` but `sentences` is `Vec<Sentence>`. Either won't compile or has implicit conversion hiding a mismatch | parser/lib.rs flattener_tests | low |
| D.13 | `[NEW]` Remove `Connective::Jo` / `Connective::Ju` deep clones in `apply_selbri` — restructure to avoid cloning recursive `LogicalForm` trees | semantics/semantic.rs lines 421-438 | low |


## Dependency Graph (Critical Path)

```
0.1 ──→ 0.2
0.5 ──→ 2.3
0.4 ──→ (any ∀∃ formula correctness)
2.1 ──→ 2.2, 2.5, 3.1, persistence
1.2 ──→ 4.1 (ka/ni needed for computation dispatch)
1.3 ──→ 5.1 (BAI needed for event role binding)

Immediate (do today):
  0.5  — 5 minutes, prevents crashes
  0.6  — 5 minutes, prevents unsound inference
  D.8  — 2 minutes, smaller WASM binary
  D.9  — 2 minutes, dead code removal
  D.10 — 1 minute, dead code removal

This week:
  0.1  — unblocks 0.2 and all forethought connective usage
  0.3  — unblocks correct disjunctive reasoning
  0.4  — unblocks sound ∀∃ reasoning
  1.8  — unblocks correct da/de/di reasoning

Next sprint:
  1.1  — sumti connectives (high application value)
  1.5  — afterthought sentence connectives (low effort, high value)
  1.9  — lujvo recognition (coverage)
```
