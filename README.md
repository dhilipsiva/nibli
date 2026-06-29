# Nibli

**A zero-hallucination symbolic reasoning engine.**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via demand-driven backward chaining over an indexed fact store. Every conclusion is a formal derivation — never a guess, never a generated step.

> *nibli* (Lojban): x1 logically entails x2 under rules x3

---

## What "zero-hallucination" means here

Nibli derives every conclusion **from the facts and rules you assert**, under two explicit assumptions:

- **Closed world** — a fact you did not assert is taken to be *false*, not unknown.
- **Closed domain** — quantifiers range only over the entities the knowledge base knows.

Values returned by the external compute backend (arithmetic and similar predicates) are **trusted as axioms**, not re-derived. So a verdict reads as:

- **`TRUE`** — a proof exists from those premises (your facts + rules + trusted backend results).
- **`FALSE`** — *not derivable* from those premises. This is **not** a proof of ¬P.
- **`UNKNOWN`** — the search could not decide: a cycle, incomplete knowledge, or a negation over an undecided sub-goal.

The guarantee is **soundness relative to what you asserted**, not omniscience — change the premises and the verdict can change. What Nibli rules out is *fabrication*: it never invents a fact, a rule, or a proof step.

---

## Pipeline

```
Lojban text ──> Lexer ──> Parser (AST) ──> Semantic Compiler (FOL IR) ──> Reasoning Engine
                 │            │                    │                            │
               Logos     Recursive-descent    Skolemization           Backward chaining
              tokenizer   with recovery     + event semantics       over indexed fact store
```

The pipeline is composed of four stages, linked as internal Rust crate dependencies and compiled into a single WASM component:

| Crate | Lojban meaning | Role |
|-------|---------------|------|
| **gerna** | grammar | Lojban text → AST → flat WIT buffer |
| **smuni** | meaning | AST buffer → FOL logic IR → flat WIT logic buffer |
| **logji** | logic | FOL logic buffer → backward-chaining assertion, query, and proof |
| **lasna** | fasten | Orchestrator: chains gerna → smuni → logji into a single WASM component |
| **gasnu** | agent | Native Wasmtime host, REPL, and TCP compute backend client |

Supporting crates:

| Crate | Role |
|-------|------|
| **nibli-engine** | Native in-process embedding of the pipeline (used by tests and the store layer) |
| **nibli-ui** | Standalone Dioxus web UI — the engine is compiled in and runs fully in-browser |
| **nibli-wasm** | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo) |
| **nibli** | Native debug REPL and `nibli-validate` tooling |

---

## Runtime Surfaces

**Canonical entrypoints:**

- **`gasnu`** — Local REPL and operator runtime for the theorem prover. The main single-node runtime. Use `just run`.
- **`nibli-ui`** — Standalone browser frontend (Dioxus). The engine is compiled into the WASM bundle and runs fully in-browser — no server. Use `just ui`.

**Supporting surfaces:**

- **`nibli-engine`** — Shared native embedding library. Not a user-facing runtime.
- **`nibli-wasm`** — wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo at dhilipsiva.dev/nibli).
- **`nibli`** — Native direct-crate REPL and `nibli-validate`. Developer tooling, not the canonical production path.

---

## Getting Started

### Prerequisites

- [Nix](https://nixos.org/download.html) (all tools — rustc, cargo-component, just, wasmtime — come from `flake.nix`)

### Build and Run

```bash
# Enter the dev shell
nix --extra-experimental-features 'nix-command flakes' develop

# Build all components and launch the REPL
just run

# Run all 661 tests
just test
```

### REPL Usage

```
~/nibli> lo gerku cu barda
[Fact #1] Asserted.

~/nibli> ? lo gerku cu barda
[Query] TRUE
  Asserted: gerku(sk_0) & barda(sk_0) -> TRUE

~/nibli> ro lo gerku cu danlu
[Fact #2] Asserted.

~/nibli> la .adam. cu gerku
[Fact #3] Asserted.

~/nibli> ? la .adam. cu danlu
[Query] TRUE
  Derived (gerku -> danlu): danlu(adam) -> TRUE
    Asserted: gerku(adam) -> TRUE

~/nibli> ?? da gerku
[Witnesses] da = adam

~/nibli> :debug re lo gerku cu barda
[Logic]
Count _v0 = 2:
  And:
    ∃ _ev1:
      And:
        And:
          gerku(_ev1)
          gerku_x1(_ev1, _v0)
        gerku_x2(_ev1, zo'e)
    ∃ _ev0:
      And:
        And:
          And:
            barda(_ev0)
            barda_x1(_ev0, _v0)
          barda_x2(_ev0, zo'e)
        barda_x3(_ev0, zo'e)

[English] Exactly 2 things are such that X is a dog and X is big.

~/nibli> :assert tenfa 8 2 3
[Fact #4] tenfa(8, 2, 3) asserted.

~/nibli> :facts
[Facts] 4 active fact(s):
  #1: lo gerku cu barda (1 root(s))
  #2: ro lo gerku cu danlu (1 root(s))
  #3: la .adam. cu gerku (1 root(s))
  #4: :assert tenfa (1 root(s))

~/nibli> :retract 1
[Retract] Fact #1 retracted. KB rebuilt.

~/nibli> :load readme.lojban
[Fact #1] la .nibli. cu logji ciste
[Fact #2] la .nibli. cu birti ciste
...
[Load] Done: 82 asserted, 31 skipped, 0 errors

~/nibli> :reset
[Reset] Knowledge base cleared.
```

Query results use a four-valued contract: `TRUE`, `FALSE`, `UNKNOWN` (with reason: cycle cut, incomplete knowledge, or NAF dependence), or `RESOURCE_EXCEEDED` (depth, fuel, or memory limit hit). The engine never guesses.

You query by **stating the proposition you want checked**, not by asking a question. `? la .adam. cu danlu` reads *"is `Adam is an animal` entailed?"* — and the verdict *is* the answer. The engine has no interrogative form: Lojban's `xu` (the spoken yes/no marker) is not a query operator, so `? xu la .adam. cu danlu` is a syntax error. State `la .adam. cu danlu` ("Adam is an animal"), never `xu la .adam. cu danlu` ("Is Adam an animal?").

### REPL Commands

| Command | Description |
|---------|-------------|
| `<sentence>` | Assert a Lojban sentence as a fact or rule |
| `? <sentence>` | Query with proof trace |
| `?? <sentence>` | Witness extraction (find all satisfying bindings) |
| `:debug <sentence>` | Show compiled FOL logic |
| `:assert <rel> <args...>` | Assert a fact directly (bypasses Lojban parser) |
| `:retract <id>` | Retract a fact by ID and rebuild the KB |
| `:facts` | List all active facts |
| `:load <filepath>` | Batch-load a `.lojban` file into the KB |
| `:reset` | Clear the entire knowledge base |
| `:compute <predicate>` | Register a predicate for external compute dispatch |
| `:backend [host:port]` | Show or change the compute backend address |
| `:fuel [amount]` | Show or set the WASM fuel limit |
| `:memory [mb]` | Show or set the WASM memory limit |
| `:contradictions` | Scan the KB for contradictions |
| `:trace <predicate>` | Enable tracing for a predicate |
| `:untrace <predicate>` | Disable tracing for a predicate |
| `:traces` | List all active traces |

---

## Transparency Triad UI

Nibli includes a standalone web UI (Dioxus) — the full reasoning engine (gerna → smuni → logji) is compiled into the WASM bundle and runs **entirely in the browser**. nibli has no server.

```bash
# Start the web UI (port 8080)
just ui
```

The three tabs are **Source** (plain English), **Lojban** (the formal encoding), and **Back-translation** (the structure-exposing gloss). The reasoning is fully local; the **only** optional network call is **Translate** on the Source tab — a *bring-your-own-key* LLM request sent **directly from your browser** to a provider you choose (Anthropic, OpenAI, OpenRouter, Google Gemini, or any OpenAI-compatible/local endpoint). Configure it via the gear button: the API key is held **in that tab's memory only** — never persisted to storage and never routed through any nibli server (there is none), and it is erased on tab close/reload. Translation is a *draft outside the reasoning firewall* — you review the Lojban (and its back-translation) before the deterministic engine reasons over it. You can also skip Translate entirely and type Lojban directly. See `nibli-ui/src/llm.rs`.

The header has an **example** dropdown that loads a preloaded, book-derived knowledge base into the triad — **Syllogism** (Ch 19), **GDPR compliance** (Ch 20), or **Drug interactions** (Ch 21). In an example the KB source/Lojban is read-only, Translate is disabled, and the query box becomes a dropdown of that example's preset queries (selecting one runs it immediately). The default, **Custom**, is the editable/translatable mode. The example corpora are the same `gdpr.lojban` / `drug-interactions.lojban` files the engine's regression tests pin (`include_str!`-ed into the bundle).

The UI uses a stateless KB model: every query builds a fresh engine, re-asserts the full Lojban tab as the knowledge base, then runs the query. The query bar is queries only (no assertions). The Lojban tab is the single source of truth.

As in the REPL, you **state the claim to check, not ask a question**: type `la .adam. cu citka` ("Adam eats"), not `xu la .adam. cu citka` ("Does Adam eat?"). The query box shows a fixed `xu` purely as a reading cue — it is never typed into the field and never reaches the engine; the verdict (`TRUE` / `FALSE` / `UNKNOWN`) is the answer.

```
ro lo gerku cu danlu          # Every dog is an animal
ro lo danlu cu citka          # Every animal eats
la .adam. cu gerku            # Adam is a dog

Query: la .adam. cu citka     # state the claim -> TRUE + proof tree
```

The interface is styled with the **QUINE** design system — an instrument-grade, terminal-first look (IBM Plex Mono, ember accent, blueprint-grid proof well) where every meaning-bearing color is a semantic token (verdicts, proof rule types, error classes) paired with a glyph for colorblind safety. Styling lives in `nibli-ui/assets/tokens.css` (design tokens) + `nibli-ui/assets/style.css`. Dark is the default; a header toggle switches to the light "paper" theme via `data-theme="light"`.

---

## Compute Backend

Nibli can dispatch predicates to external compute backends via a TCP + JSON Lines protocol. Any language that speaks TCP and JSON can serve as a backend.

```bash
# Terminal 1: Start the Python reference backend
just backend

# Terminal 2: Run Nibli with the backend connected
just run-with-backend

# In the REPL:
:compute tenfa                      # Register tenfa for external dispatch
li bi tenfa li re li ci             # Assert: 8 = 2^3
? li bi tenfa li re li ci           # Query: TRUE (computed by Python)
```

**Built-in arithmetic** (always local, no backend needed): `pilji` (multiply), `sumji` (add), `dilcu` (divide).

> **One deliberate approximation.** `pilji`/`sumji`/`dilcu` check `x1 = x2 ∘ x3` with **tolerant** float equality — `isclose` with relative tolerance `1e-9` (matching Python's `math.isclose`), i.e. `|a − b| ≤ 1e-9 · max(|a|, |b|)`. So `0.3 = 0.1 + 0.2` answers `TRUE` despite IEEE-754 rounding making the sum `0.30000000000000004`. That is a real, bounded approximation on the numeric result — the one place Nibli is not bit-exact. The equality predicate **`dunli` (`=`) is exact** (`==`, tolerates no rounding); `dilcu`'s divide-by-zero check is likewise an exact guard. The single evaluator (`nibli-types/src/arithmetic.rs`) is shared by the in-WASM engine, the `gasnu` host, and the Python reference backend, so all three agree.

**External predicates** (via backend): `tenfa` (exponentiation), `dugri` (logarithm), and any custom predicates you add to the backend server.

Configure with `NIBLI_COMPUTE_ADDR=host:port` or `:backend host:port` in the REPL. Connection is lazy (connects on first dispatch) with auto-reconnect. The browser UI has no TCP, so external predicates resolve only in the `gasnu` REPL; built-in arithmetic still works everywhere.

If an external predicate's backend is unreachable (or unconfigured), the query returns `UNKNOWN (backend-unavailable)` — never a definitive `FALSE`. A backend the engine cannot consult is genuinely undetermined, not a derived falsehood.

---

## Tech Stack

| Component | Technology |
|-----------|-----------|
| Language | Rust (stable, 1.94.0) |
| WASM target | WASI Preview 2 Component Model (cargo-component) |
| WASM runtime | Wasmtime |
| Reasoning | Demand-driven backward chaining over indexed fact store |
| Lexer | Logos |
| Dictionary | Compile-time perfect hash function (PHF) |
| Dev environment | Nix flake |
| Compute protocol | TCP + JSON Lines |
| Task runner | Just |
| Web UI | Dioxus (standalone — engine compiled into the WASM bundle) |

---

## Lojban Coverage

The parser (`gerna`) accepts a practical subset of Lojban sufficient for formal encoding of domain rules:

- **Articles (gadri):** `lo` (existential: "something that is..."), `le` (descriptive: "the thing I have in mind"), `la` (name → constant)
- **Quantifiers:** `ro lo` / `ro le` (universal), `PA lo` / `PA le` (numeric), `su'o lo` (at least one)
- **Prenex:** `ro da [ro de ...] zo'u <body>` — multi-variable universally-quantified rules (lowers to nested `∀`). Firing is currently `members^dep_count`-expensive for two or more free join variables; see `todo.md`.
- **Place tags:** `fa`/`fe`/`fi`/`fo`/`fu` (explicit argument positions)
- **Modal tags:** BAI (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`) and `fi'o`...`fe'u`
- **Selbri (predicates):** root, tanru with Neo-Davidsonian event semantics (resolves the intersective fallacy), conversion (`se`/`te`/`ve`/`xe`), negation (`na`), grouping (`ke`...`ke'e`), compounds (`zei`), argument attachment (`be`...`bei`...`be'o`)
- **Relative clauses:** `poi`/`noi`/`voi` with `ke'a` bound variable and clause stacking. A **disjunctive** restrictor in a universal (`ro lo X poi P ja Q cu R`, also `ganai ga P gi Q gi R`) compiles to one backward-chaining rule per disjunct (DNF rule-splitting) and fires when either disjunct holds; `je` (AND) restrictors still require all conjuncts
- **Connectives:** sumti (`.e`/`.a`/`.o`/`.u` + `nai`), selbri (`je`/`ja`/`jo`/`ju`), sentence (forethought: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; afterthought: `.i je`/`ja`/`jo`/`ju` with `na`/`nai`)
- **Rule conclusions:** a **tensed** conclusion (`ganai A gi pu B`, `ro da zo'u ganai da P gi pu da Q`) derives the tensed fact (tense-exact; the simple `ro lo X cu pu Q` is whole-rule and stays rejected). A **disjunctive** conclusion (`ro lo X cu Q ja R`) is registered as the integrity constraint `¬(P ∧ ¬Q ∧ ¬R)` — flagged as a contradiction when P holds and every disjunct is explicitly denied (`na`); for the positive use, ask a disjunctive **query** (`? … Q ja R`)
- **Abstractions:** `nu` (event), `du'u` (proposition), `ka` with `ce'u` (property), `ni` (amount), `si'o` (concept)
- **Tense:** `pu` (past), `ca` (present), `ba` (future)
- **Deontic modifiers:** `ei` (obligation), `e'e` (permission)
- **Special forms:** observative sentences, `go'i` pro-bridi (deep-clones previous selbri structure), `ma` question pro-sumti (compiles to existential for witness extraction), quoted literals (`lu`...`li'u`), number sumti (`li` + PA)
- **Metalinguistic erasure:** `si` (word), `sa` (construct-class with selma'o classification), `su` (sentence)
- **Error recovery:** per-sentence recovery (skips to next `.i` on failure, continues parsing)

---

## Reasoning Engine

- **Backward chaining** over a typed, hash-indexed fact store with predicate-indexed lookup
- **Universal rules** compiled to backward-chaining templates (`UniversalRuleRecord`) at assertion time
- **Skolemization:** independent constants and dependent Skolem functions (`SkolemFn` + `DepPair` for multi-dependency)
- **Proof traces:** every query produces a proof tree (20 `ProofRule` variants) with DAG memoization via `ProofRef`
- **Witness extraction:** `query-find` returns all satisfying binding sets for existential variables
- **Belief revision:** retract-and-rebuild with monotonic fact IDs; `:retract <id>` and `:facts` REPL commands
- **Four-valued query result:** `TRUE`, `FALSE`, `UNKNOWN` (cycle cut / incomplete knowledge / NAF dependent), `RESOURCE_EXCEEDED` (depth / fuel / memory)
- **Temporal reasoning:** `Past`/`Present`/`Future` wrappers preserved end-to-end; timeless rules automatically derive tensed conclusions
- **Neo-Davidsonian event semantics:** every predication decomposes into event type + role predicates; tanru share event variables
- **Conjunction introduction:** `And(A, B)` verified recursively with mutual `InDomain` entities (bounded, no exponential blowup)
- **Numerical comparisons:** `zmadu` (>), `mleca` (<), `dunli` (==) evaluated at query time on `Num` terms
- **Compute dispatch:** `compute-backend` WIT protocol with `ComputeNode` IR variant; results auto-asserted into KB
- **Ground conjunction flattening:** top-level `And` trees flattened before assertion; ground material conditionals auto-registered as zero-variable rules for modus ponens
- **Equality reasoning:** `du` (identity) with union-find congruence closure
- **Stratification enforcement:** predicate dependency graph analysis prevents unsound negative cycles
- **Integrity constraints:** `deny` rules enforce assertion-time invariants
- **Defeasible rules:** priority-ordered rule matching (`priority: u32`)
- **Sorted logic:** type hierarchy with subsort checking
- **Hypothetical reasoning:** `with_assumptions()` for clone-query-discard patterns
- **Selective forward chaining:** `forward: bool` on rules with `trigger_forward_rules`
- **Aggregation:** `count_witnesses`, `aggregate(Sum/Min/Max/Avg)`
- **Persistent fact store:** `FactStore` trait with InMemory, Redb, and WASI backends
- **Iterative deepening:** shallowest-proof guarantee
- **Tabling:** cached results with invalidation on mutations
- **KB import/export:** RDF Turtle parser, OWL class mapping via `nibli-import` crate
- **Failure traces:** `PredicateNotFound`, `RuleAttemptFailed`, `EqualitySubstitution` proof rule variants explain why derivations fail
- **Argument-position indexing:** `(relation, position, value)` secondary index for efficient witness extraction
- **Predicate signature validation:** arity checking from PHF dictionary with permissive warnings
- **NAF visibility:** `has_naf_dependency()` on proof traces marks CWA-dependent conclusions
- **Interactive debugging:** `:trace`/`:untrace`/`:traces` REPL commands
- **WASM fuel limits:** configurable via `NIBLI_FUEL` or `:fuel` REPL command
- **WASM memory limits:** configurable via `NIBLI_MEMORY_MB` or `:memory` REPL command
- **Error types:** `nibli-error` variant (`syntax`/`semantic`/`reasoning`/`backend`) with line:column for parse errors
- **Batch loading:** `:load <filepath>` loads `.lojban` files; `#` lines are comments

---

## Development

| Command | Description |
|---------|-------------|
| `just run` | Full pipeline: build WASM component, launch REPL |
| `just check` | Fast type-check (`cargo check --workspace`) |
| `just test` | Run all 661 unit tests |
| `just test-engine` | Integration tests (full parse → compile → reason pipeline) |
| `just test-gerna` | Parser tests only |
| `just test-backend` | Python backend tests |
| `just test-all` | Every test suite |
| `just ui` | Standalone Transparency Triad web UI (port 8080) |
| `just backend` | Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with compute backend |
| `just run-persist` | Run with persistent Redb fact store |
| `just fuzz-parse [SECS]` | Fuzz the parser |
| `just fuzz-assert [SECS]` | Fuzz assertion pipeline |
| `just fuzz-query [SECS]` | Fuzz stateful KB queries |
| `just ci` | Full CI suite |
| `just clean` | `cargo clean` |

---

## License

See `LICENSE` for details.
