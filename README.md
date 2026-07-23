# Nibli

**A zero-hallucination symbolic reasoning engine.**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles **nibli KR** — a human-readable predicate-call knowledge-representation language (`dog(Adam).`, `animal(every dog).`) — into First-Order Logic and performs inference via demand-driven backward chaining over an indexed fact store. Every conclusion is a formal derivation — never a guess, never a generated step. (Lojban, nibli's original surface syntax, retired at THE DROP — the last dual-front-end engine is tagged `v0.1-lojban-final`, and the Lojban tooling was donated to a separate repo.)

> *nibli* (Lojban): x1 logically entails x2 under rules x3

---

## What "zero-hallucination" means here

Nibli derives every conclusion **from the facts and rules you assert**, under two explicit assumptions:

- **Closed world** — a fact you did not assert is taken to be *false*, not unknown.
- **Closed domain** — quantifiers range only over the entities the knowledge base knows.

Results from the **external compute backend** (`exponential`, `logarithm`, or any predicate you register) are a **trusted oracle**, not a derivation: a `true` reply is auto-asserted into the knowledge base as a ground fact mid-query, and downstream rules chain on it as if you had asserted it yourself. The backend is part of the *trusted computing base* — an axiom source — so any conclusion that passes through it is only as sound as that oracle. (Built-in arithmetic, `product`/`sum`/`quotient`, is computed locally — see [Compute Backend](#compute-backend).) So a verdict reads as:

- **`TRUE`** — a proof exists from those premises (your facts + rules + trusted backend results).
- **`FALSE`** — *not derivable* from those premises. This is **not** a proof of ¬P.
- **`UNKNOWN`** — the search could not decide: a cycle, incomplete knowledge, or a negation over an undecided sub-goal.

The guarantee is **soundness relative to what you asserted**, not omniscience — change the premises and the verdict can change. What Nibli rules out is *fabrication*: it never invents a fact, a rule, or a proof step.

---

## The nibli KR Language

nibli KR is a strict predicate-call surface for first-order claims: intuitive to read, but every semantic distinction stays visible in the spelling (the anti-silent-mistranslation design rule). One statement per line, ending with a period. Unknown predicate words are a **compile error**, never a guess — names resolve through the committed English corpus (~1,342 strongly-typed predicate entries, every place named), fail-closed; `a+b` compounds resolve only via committed compound entries.

| nibli KR | Reads as |
|-------|----------|
| `dog(Adam).` | Adam is a dog |
| `animal(every dog).` | every dog is an animal (a rule) |
| `~eats(Adam).` | Adam does not eat |
| `past eats(me, some food).` | I ate some food |
| `dog(Adam) & cat(Betis).` | conjunction (`\|` or, `->` if-then) |
| `goes(Adam, destination: some market).` | named argument places, Python-style |
| `beautiful(every person where ~cat).` | rule with a negated restrictor (negation-as-failure) |
| `Kim = Adam.` | identity — Kim and Adam are the same individual |
| `red(exactly 2 red).` | exact-count claim |
| `runs(some [big dog]).` | compound predicate: a big-dog kind of runner |
| `desires(desired: every teaches, desirer: event { studies() }).` | event abstraction |
| `all $x: dangerous($x) & uses(Adam, $x) -> warns($x).` | explicit prenex rule with variables |

The normative spec is **[NIBLI_KR.md](NIBLI_KR.md)** (v0.1 compat profile, implemented); the executable grammar is `nibli-kr/src/nibli_kr.pest` — the parser is generated from it, so the spec and the parser cannot drift. The front-end's independent oracle is the KR seam gate (`verify-nibli-kr-seam`: hand-verified FOL structural goldens + a construct-inventory sweep + metamorphic relations, in CI).

---

## Pipeline

```
nibli KR text ──> Front-end (nibli-kr) ──> Semantic Compiler (FOL IR) ──> Reasoning Engine
                        │                                   │                            │
              pest grammar → AST buffer               Skolemization              Backward chaining
             (fail-closed name resolution)          + event semantics         over indexed fact store
```

Both front-ends emit the same flat AST buffer, so everything downstream is shared. The pipeline stages are linked as internal Rust crate dependencies and compiled into a single WASM component:

| Crate | Name origin | Role |
|-------|---------------|------|
| **nibli-kr** | — | nibli KR text → AST → flat WIT buffer (pest grammar + fail-closed alias resolution + the canonical renderer) |
| **nibli-semantics** | — | AST buffer → FOL logic IR → flat WIT logic buffer |
| **nibli-reason** | — | FOL logic buffer → backward-chaining assertion, query, and proof |
| **nibli-pipeline** | — | Orchestrator: chains the front-end → nibli-semantics → nibli-reason into a single WASM component |
| **nibli-host** | — | Native Wasmtime host, REPL, and TCP compute backend client |

Supporting crates:

| Crate | Role |
|-------|------|
| **nibli-lexicon** | The committed English corpus — strongly-typed predicate + compound entries (name, named places, gloss, template, gismu provenance), const-validated; the single vocabulary source for every stage |
| **nibli-engine** | Native in-process embedding of the pipeline (used by tests and the store layer) |
| **nibli-ui** | Standalone Dioxus web UI — the engine is compiled in and runs fully in-browser |
| **nibli-wasm** | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo) |
| **nibli** | Native debug REPL and `nibli-validate` tooling |

The FOL IR in the middle of the pipeline — the `LogicBuffer` — is nibli's language-agnostic
seam and is publicly specified in **[LOGIC_IR.md](LOGIC_IR.md)** (node types, flat-buffer
layout, emitted-shape invariants, stable-vs-internal surface, and the entry points for
building alternative front-ends or consumers against it).

---

## Runtime Surfaces

**Canonical entrypoints:**

- **`nibli-host`** — Local REPL and operator runtime for the theorem prover. The main single-node runtime. Use `just run`.
- **`nibli-ui`** — Standalone browser frontend (Dioxus). The engine is compiled into the WASM bundle and runs fully in-browser — no server. Use `just ui`.

**Supporting surfaces:**

- **`nibli-engine`** — Shared native embedding library. Not a user-facing runtime.
- **`nibli-wasm`** — wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo at dhilipsiva.dev/nibli).
- **`nibli`** — Native direct-crate REPL and `nibli-validate`. Developer tooling, not the canonical production path.

Every surface speaks nibli KR — the single front-end since THE DROP.

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

# Run all unit tests
just test
```

> **Dictionary data.** The dictionary is COMMITTED Rust source: `nibli-lexicon/src/corpus/`
> holds ~1,342 strongly-typed predicate entries (every place named in English;
> `arity = places.len()` by construction) plus curated `a+b` compound entries, derived
> from the [lensisku](https://lensisku.lojban.org) Lojban dictionary (jbovlaste data,
> CC-BY-SA) and const-validated on every compile. There is ONE build mode — no JSON is
> read at build time, so `just run`/`just test`, CI, and the deployed site all carry the
> identical full vocabulary, fully offline. `dictionary-en.json` (gitignored; `just
> fetch-dict`) is only the input of the `tools/lexigen` regeneration tool
> (`just regen-lexicon`), which reports drift and candidate new entries but never
> rewrites committed rows.

### REPL Usage

```
~/nibli> big(some dog).
[Skolem] 3 variable(s) → _ev0 ↦ sk_2, _ev1 ↦ sk_1, _v0 ↦ sk_0
[Fact #0] Asserted.

~/nibli> animal(every dog).
[Skolem] 2 variable(s) → _ev0 ↦ sk_4(∀-dependent), _ev1 ↦ sk_3(∀-dependent)
[Rule] Compiled ∀_v0 to backward-chaining rule
[Fact #1] Asserted.

~/nibli> dog(Adam).
[Skolem] 1 variable(s) → _ev0 ↦ sk_7
[Fact #2] Asserted.

~/nibli> ? animal(Adam).
[Query] TRUE
[Why] Because adam is a dog, adam is an animal.
  ⊢ adam is an animal  [by the rule: every dog is an animal] -> TRUE
    ▣ adam is a dog  [given] -> TRUE

~/nibli> ?? dog($x).
[Find] _ev0 = sk_7, $x = adam
[Find] _ev0 = sk_1, $x = sk_0

~/nibli> :debug big(exactly 2 dog).
[Logic]
Count _v0 = 2:
  And:
    ∃ _ev1:
      And:
        And:
          dog(_ev1)
          dog_x1(_ev1, _v0)
        dog_x2(_ev1, something)
    ∃ _ev0:
      And:
        And:
          And:
            big(_ev0)
            big_x1(_ev0, _v0)
          big_x2(_ev0, something)
        big_x3(_ev0, something)

[English] Exactly 2 things are such that X is a dog and X is big.

~/nibli> :assert exponential 8 2 3
[Skolem] 1 variable(s) → _ev0 ↦ sk_8
[Fact #3] exponential(8, 2, 3) asserted.

~/nibli> :facts
[Facts] 4 active fact(s):
  #0: big(some dog). (1 root)
  #1: animal(every dog). (1 root)
  #2: dog(Adam). (1 root)
  #3: :assert exponential (1 root)

~/nibli> :retract 1
[Retract] Fact #1 retracted. KB rebuilt.

~/nibli> :load readme.nibli
[Fact #4] logical system(Nibli).
[Fact #5] certain system(Nibli).
...
[Load] Done: 71 asserted, 37 skipped, 4 errors

~/nibli> :reset
[Reset] Knowledge base cleared.
```

(The `:debug` view exposes the formal event-decomposed IR: nibli KR's `dog`/`big` compile to the English predicates `dog`/`big` plus their role predicates `dog_x1`/`big_x2`/… — no Lojban. The 4 `:load` errors are deliberate fail-closed rejections — bare negations and one non-flat rule conclusion ingest no facts rather than being silently misreported as asserted.)

Query results use a four-valued contract: `TRUE`, `FALSE`, `UNKNOWN` (with reason: cycle cut, incomplete knowledge, NAF dependence, backend unavailable, or non-finite numeric), or `RESOURCE_EXCEEDED` (depth, fuel, or memory limit hit). The engine never guesses.

You query by **stating the proposition you want checked**, not by asking a question. `? animal(Adam).` reads *"is `Adam is an animal` entailed?"* — and the verdict *is* the answer. The engine has no interrogative form: state `animal(Adam).` ("Adam is an animal"), never "Is Adam an animal?". The `?` prefix marks the line as a query; it is not a question mark on the claim.

### REPL Commands

| Command | Description |
|---------|-------------|
| `<statement>` | Assert a statement (nibli KR) as a fact or rule |
| `? <statement>` | Query with proof trace |
| `?? <statement>` | Witness extraction (find all satisfying bindings, `$x` variables) |
| `:debug <statement>` | Show compiled FOL logic |
| `:assert <rel> <args...>` | Assert a fact directly (bypasses text parsing) |
| `:retract <id>` | Retract a fact by ID and rebuild the KB |
| `:facts` | List all active facts |
| `:load <filepath>` | Batch-load a `.nibli` file |
| `:reset` | Clear the entire knowledge base |
| `:compute <predicate>` | Register a predicate for external compute dispatch |
| `:backend [host:port]` | Show or change the compute backend address |
| `:fuel [amount]` | Show or set the WASM fuel limit |
| `:memory [mb]` | Show or set the WASM memory limit |
| `:strict [on\|off]` | Show or set strict mode — reject arity/constraint violations instead of warn-and-insert (also `NIBLI_STRICT=1`) |
| `:existential-import [on\|off]` | Show or set xorlo witness minting (default ON) — off is the clean-core profile where a description universal (`animal(every dog).`) presupposes nothing, so `some` = plain ∃ (also `NIBLI_EXISTENTIAL_IMPORT=0`) |
| `:contradictions` | Scan the KB for contradictions |
| `:trace <predicate>` | Enable tracing for a predicate |
| `:untrace <predicate>` | Disable tracing for a predicate |
| `:traces` | List all active traces |

---

## Transparency Triad UI

Nibli includes a standalone web UI (Dioxus) — the full reasoning engine (nibli-kr → nibli-semantics → nibli-reason) is compiled into the WASM bundle and runs **entirely in the browser**. nibli has no server.

```bash
# Start the web UI (port 8080)
just ui
```

To build a release bundle (`just build-ui`) or self-host, see [`DEPLOY.md`](DEPLOY.md).

The three tabs are **Source** (plain English), **nibli KR** (the formal encoding), and **Back-translation** (the structure-exposing gloss). The reasoning is fully local; the **only** optional network call is **Formalize** on the Source tab — a *bring-your-own-key* LLM request sent **directly from your browser** to a provider you choose (Anthropic, OpenAI, OpenRouter, Google Gemini, or any OpenAI-compatible/local endpoint). Configure it via the gear button: the API key is held **in that tab's memory only** — never persisted to storage and never routed through any nibli server (there is none), and it is erased on tab close/reload.

Formalize runs the **agentic formalizer** (`nibli-formalize`) — "formalize", not "compile": the LLM step is interpretive and sits *outside* the reasoning firewall, behind deterministic gates. The LLM's draft is validated by the *real compilers* — the nibli-kr front-end (grammar + fail-closed name resolution) + nibli-semantics (semantics) + a canonical render **round-trip** check — and any compiler error is fed back for the model to self-correct, so what lands in the nibli KR tab already passes those gates. It is still a *draft* — you review the nibli KR (and its back-translation) before the deterministic engine reasons over it, and you can skip Formalize entirely and type nibli KR directly.

The header has an **example** dropdown that loads a preloaded, book-derived knowledge base into the triad — **Syllogism** (Ch 18), **GDPR compliance** (Ch 19), **Legal domain** (`utopia.nibli`), or **Drug interactions** (Ch 20). In an example the KB source is read-only, Formalize is disabled, and the query box becomes a dropdown of that example's preset queries (selecting one runs it immediately). The default, **Custom**, is the editable mode. The example corpora are the committed `gdpr.nibli` / `utopia.nibli` / `drug-interactions.nibli` files the engine's regression tests pin.

The UI uses a stateless KB model: every query builds a fresh engine, re-asserts the full KB tab as the knowledge base, then runs the query. The query bar is queries only (no assertions). The KB tab is the single source of truth.

As in the REPL, you **state the claim to check, not ask a question**: type `eats(Adam).` ("Adam eats"), not "Does Adam eat?". The query box shows a fixed `?` purely as a reading cue — it is never typed into the field and never reaches the engine; the verdict (`TRUE` / `FALSE` / `UNKNOWN`) is the answer.

```
animal(every dog).            # Every dog is an animal
eats(every animal).           # Every animal eats
dog(Adam).                    # Adam is a dog

Query: eats(Adam).            # state the claim -> TRUE + proof tree
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
:compute exponential                # Register exponential for external dispatch
exponential(8, 2, 3).               # Assert: 8 = 2^3
? exponential(8, 2, 3).             # Query: TRUE (computed by Python)
```

**Built-in arithmetic** (always local, no backend needed): `product` (multiply), `sum` (add), `quotient` (divide).

> **One deliberate approximation.** `product`/`sum`/`quotient` check `x1 = x2 ∘ x3` with **tolerant** float equality — `isclose` with relative tolerance `1e-9` (matching Python's `math.isclose`), i.e. `|a − b| ≤ 1e-9 · max(|a|, |b|)`. So `0.3 = 0.1 + 0.2` answers `TRUE` despite IEEE-754 rounding making the sum `0.30000000000000004`. That is a real, bounded approximation on the numeric result — the one place Nibli is not bit-exact. The exact-equality predicate **`num_equal` (`=`) is exact** (`==`, tolerates no rounding); `quotient`'s divide-by-zero check is likewise an exact guard. The single evaluator (`nibli-types/src/arithmetic.rs`) is shared by the in-WASM engine, the `nibli-host` host, and the Python reference backend, so all three agree.

**External predicates** (via backend): `exponential`, `logarithm`, and any custom predicates you add to the backend server.

> **Trust boundary.** An external predicate is a **trusted oracle**, not something Nibli proves. When the backend replies `true`, that result is auto-asserted into the knowledge base as a ground fact mid-query, and the reasoner's rules chain on it exactly like a premise you asserted. Nibli never re-derives or checks it — the backend (and whoever operates it) is part of the trusted computing base. A proof that passes through `exponential`/`logarithm` is sound only relative to that oracle.

Configure with `NIBLI_COMPUTE_ADDR=host:port` or `:backend host:port` in the REPL. Connection is lazy (connects on first dispatch) with auto-reconnect. The browser UI has no TCP, so external predicates resolve only in the `nibli-host` REPL; built-in arithmetic still works everywhere.

If an external predicate's backend is unreachable (or unconfigured), the query returns `UNKNOWN (backend-unavailable)` — never a definitive `FALSE`. A backend the engine cannot consult is genuinely undetermined, not a derived falsehood.

---

## Tech Stack

| Component | Technology |
|-----------|-----------|
| Language | Rust (stable, 1.94.0) |
| WASM target | WASI Preview 2 Component Model (cargo-component) |
| WASM runtime | Wasmtime |
| Reasoning | Demand-driven backward chaining over indexed fact store |
| Front-end parser | pest (nibli KR — the grammar file is the parser) |
| Dictionary | Compile-time perfect hash function (PHF) |
| Dev environment | Nix flake |
| Compute protocol | TCP + JSON Lines |
| Task runner | Just |
| Web UI | Dioxus (standalone — engine compiled into the WASM bundle) |

---

## Reasoning Engine

- **Backward chaining** over a typed, hash-indexed fact store with predicate-indexed lookup
- **Universal rules** compiled to backward-chaining templates (`UniversalRuleRecord`) at assertion time
- **Skolemization:** independent constants and dependent Skolem functions (`SkolemFn` + `DepPair` for multi-dependency)
- **Proof traces:** every query produces a proof tree (20 `ProofRule` variants) with DAG memoization via `ProofRef`
- **Witness extraction:** `query-find` returns all satisfying binding sets for existential variables
- **Belief revision:** retract-and-rebuild with monotonic fact IDs; `:retract <id>` and `:facts` REPL commands
- **Four-valued query result:** `TRUE`, `FALSE`, `UNKNOWN` (cycle cut / incomplete knowledge / NAF dependent / backend unavailable / non-finite), `RESOURCE_EXCEEDED` (depth / fuel / memory)
- **Temporal reasoning:** `Past`/`Present`/`Future` wrappers preserved end-to-end; timeless rules automatically derive tensed conclusions
- **Neo-Davidsonian event semantics:** every predication decomposes into event type + role predicates; compound predicates share event variables
- **Conjunction introduction:** `And(A, B)` verified recursively with mutual `InDomain` entities (bounded, no exponential blowup)
- **Numerical comparisons:** `greater` (>), `less` (<), `num_equal` (==) evaluated at query time on `Num` terms
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
- **KB import/export:** RDF Turtle parser, OWL class mapping via the `nibli-import` crate and CLI (`just import <file.ttl>`, with `--raw`/`--export`/`--lang`/`--query` flags)
- **Failure traces:** `PredicateNotFound`, `RuleAttemptFailed`, `EqualitySubstitution` proof rule variants explain why derivations fail
- **Argument-position indexing:** `(relation, position, value)` secondary index for efficient witness extraction
- **Predicate signature validation:** arity checking from PHF dictionary with permissive warnings
- **Closed-world visibility:** `naf_dependent` (a `na→True` NAF result) and its dual `cwa_false` (a `FALSE` that is closed-world — "not derivable", not a disproof — vs. a numeric FALSE that was decided) flag CWA-dependent conclusions on every proof trace; both render a closed-world caveat
- **Interactive debugging:** `:trace`/`:untrace`/`:traces` REPL commands
- **WASM fuel limits:** configurable via `NIBLI_FUEL` or `:fuel` REPL command
- **WASM memory limits:** configurable via `NIBLI_MEMORY_MB` or `:memory` REPL command
- **Error types:** `nibli-error` variant (`syntax`/`semantic`/`reasoning`/`backend`) with line:column for parse errors
- **Batch loading:** `:load <filepath>` loads `.nibli` files; `#` lines are comments

---

## Development

| Command | Description |
|---------|-------------|
| `just run` | Full pipeline: build WASM component, launch REPL |
| `just check` | Fast type-check (`cargo check --workspace`) |
| `just test` | Run all unit tests |
| `just test-engine` | Integration tests (full parse → compile → reason pipeline) |
| `just test-nibli-kr` | nibli KR front-end tests only |
| `just test-backend` | Python backend tests |
| `just test-all` | Every test suite |
| `just verify-nibli-kr-seam` | The KR seam gate (FOL structural goldens + construct sweep + metamorphics) |
| `just ui` | Standalone Transparency Triad web UI (port 8080) |
| `just backend` | Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with compute backend |
| `just run-persist` | Run with persistent Redb fact store |
| `just fuzz-nibli-kr [SECS]` | Fuzz the nibli KR front-end |
| `just fuzz-assert [SECS]` | Fuzz assertion pipeline |
| `just fuzz-query [SECS]` | Fuzz stateful KB queries |
| `just fuzz-ci [SECS]` | Time-boxed fuzz gate (all 3 targets, corpus-seeded) — runs in CI |
| `just ci` | Full CI suite |
| `just clean` | `cargo clean` |

---

## License

See `LICENSE` for details.
