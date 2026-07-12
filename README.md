# Nibli

**A zero-hallucination symbolic reasoning engine.**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles **Klaro** — a human-readable predicate-call knowledge-representation language (`dog(Adam).`, `animal(every dog).`) — into First-Order Logic and performs inference via demand-driven backward chaining over an indexed fact store. Every conclusion is a formal derivation — never a guess, never a generated step. Lojban, nibli's original surface syntax, remains fully supported as the [legacy front-end](#legacy-lojban-front-end); both compile to the identical logic.

> *nibli* (Lojban): x1 logically entails x2 under rules x3

---

## What "zero-hallucination" means here

Nibli derives every conclusion **from the facts and rules you assert**, under two explicit assumptions:

- **Closed world** — a fact you did not assert is taken to be *false*, not unknown.
- **Closed domain** — quantifiers range only over the entities the knowledge base knows.

Results from the **external compute backend** (`tenfa`, `dugri`, or any predicate you register) are a **trusted oracle**, not a derivation: a `true` reply is auto-asserted into the knowledge base as a ground fact mid-query, and downstream rules chain on it as if you had asserted it yourself. The backend is part of the *trusted computing base* — an axiom source — so any conclusion that passes through it is only as sound as that oracle. (Built-in arithmetic, `pilji`/`sumji`/`dilcu`, is computed locally — see [Compute Backend](#compute-backend).) So a verdict reads as:

- **`TRUE`** — a proof exists from those premises (your facts + rules + trusted backend results).
- **`FALSE`** — *not derivable* from those premises. This is **not** a proof of ¬P.
- **`UNKNOWN`** — the search could not decide: a cycle, incomplete knowledge, or a negation over an undecided sub-goal.

The guarantee is **soundness relative to what you asserted**, not omniscience — change the premises and the verdict can change. What Nibli rules out is *fabrication*: it never invents a fact, a rule, or a proof step.

---

## The Klaro Language

Klaro is a strict predicate-call surface for first-order claims: intuitive to read, but every semantic distinction stays visible in the spelling (the anti-silent-mistranslation design rule). One statement per line, ending with a period. Unknown predicate words are a **compile error**, never a guess — names resolve through a curated+generated English alias map (~1,341 aliases in a full build) down to the underlying formal vocabulary, fail-closed.

| Klaro | Reads as |
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
| `runs(some [big dog]).` | compound predicate (tanru): a big-dog kind of runner |
| `desires(desired: every teaches, desirer: event { studies() }).` | event abstraction |
| `all $x: dangerous($x) & uses(Adam, $x) -> warns($x).` | explicit prenex rule with variables |

The normative spec is **[SURFACE_SYNTAX.md](SURFACE_SYNTAX.md)** (v0.1 compat profile, implemented); the executable grammar is `klaro/src/klaro.pest` — the parser is generated from it, so the spec and the parser cannot drift. Klaro↔Lojban equivalence (identical compiled logic per statement) is enforced in CI by the `verify-klaro` / `verify-klaro-twins` gates.

---

## Pipeline

```
Klaro text ──> Front-end (klaro; legacy: gerna) ──> Semantic Compiler (FOL IR) ──> Reasoning Engine
                        │                                   │                            │
              pest grammar → AST buffer               Skolemization              Backward chaining
             (fail-closed name resolution)          + event semantics         over indexed fact store
```

Both front-ends emit the same flat AST buffer, so everything downstream is shared. The pipeline stages are linked as internal Rust crate dependencies and compiled into a single WASM component:

| Crate | Lojban meaning | Role |
|-------|---------------|------|
| **klaro** | clear (working name) | Klaro text → AST → flat WIT buffer (pest grammar + fail-closed alias resolution + the canonical renderer) |
| **gerna** | grammar | Legacy Lojban text → the same AST buffer |
| **smuni** | meaning | AST buffer → FOL logic IR → flat WIT logic buffer |
| **logji** | logic | FOL logic buffer → backward-chaining assertion, query, and proof |
| **lasna** | fasten | Orchestrator: chains the front-end → smuni → logji into a single WASM component |
| **gasnu** | agent | Native Wasmtime host, REPL, and TCP compute backend client |

Supporting crates:

| Crate | Role |
|-------|------|
| **klaro-dictionary** | Compile-time English-alias map for Klaro (alias → formal predicate + place labels) |
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

- **`gasnu`** — Local REPL and operator runtime for the theorem prover. The main single-node runtime. Use `just run`.
- **`nibli-ui`** — Standalone browser frontend (Dioxus). The engine is compiled into the WASM bundle and runs fully in-browser — no server. Use `just ui`.

**Supporting surfaces:**

- **`nibli-engine`** — Shared native embedding library. Not a user-facing runtime.
- **`nibli-wasm`** — wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo at dhilipsiva.dev/nibli).
- **`nibli`** — Native direct-crate REPL and `nibli-validate`. Developer tooling, not the canonical production path.

Every surface speaks Klaro by default and Lojban in legacy mode: the REPLs via `:lang` / `:klaro` / `:lojban`, the CLIs via `--lang klaro|lojban`, and all of them via the `NIBLI_LANG` environment variable.

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

> **Dictionary data.** The build reads `dictionary-en.json` at the repo root — the English
> bulk export from the [lensisku](https://lensisku.lojban.org) Lojban dictionary (jbovlaste
> data, CC-BY-SA). It is a compile-time input to BOTH dictionaries: the predicate
> arity/place-structure tables (smuni-dictionary) and the full ~1,341-word Klaro alias map
> (klaro-dictionary). It is gitignored; fetch it with `just fetch-dict` (lensisku's cached
> dumps are a public download, no login needed) or drop the file in manually. Without it the
> build falls back to the in-tree curated tables (~100 core aliases), so `just run`/`just
> test` and CI work fully offline — only the long-tail vocabulary differs.

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
[Find] _ev0 = sk_7, da = adam
[Find] _ev0 = sk_1, da = sk_0

~/nibli> :debug big(exactly 2 dog).
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
[Skolem] 1 variable(s) → _ev0 ↦ sk_8
[Fact #3] tenfa(8, 2, 3) asserted.

~/nibli> :facts
[Facts] 4 active fact(s):
  #0: big(some dog). (1 root)
  #1: animal(every dog). (1 root)
  #2: dog(Adam). (1 root)
  #3: :assert tenfa (1 root)

~/nibli> :retract 1
[Retract] Fact #1 retracted. KB rebuilt.

~/nibli> :load readme.klaro
[Fact #4] logical system(Nibli).
[Fact #5] certain system(Nibli).
...
[Load] Done: 71 asserted, 37 skipped, 4 errors

~/nibli> :reset
[Reset] Knowledge base cleared.
```

(The alias resolution is visible in `:debug`: Klaro's `dog`/`big` compile to the formal predicates `gerku`/`barda`, event-decomposed. The 4 `:load` errors are deliberate fail-closed rejections — bare negations and one non-flat rule conclusion ingest no facts rather than being silently misreported as asserted.)

Query results use a four-valued contract: `TRUE`, `FALSE`, `UNKNOWN` (with reason: cycle cut, incomplete knowledge, NAF dependence, backend unavailable, or non-finite numeric), or `RESOURCE_EXCEEDED` (depth, fuel, or memory limit hit). The engine never guesses.

You query by **stating the proposition you want checked**, not by asking a question. `? animal(Adam).` reads *"is `Adam is an animal` entailed?"* — and the verdict *is* the answer. The engine has no interrogative form: state `animal(Adam).` ("Adam is an animal"), never "Is Adam an animal?". The `?` prefix marks the line as a query; it is not a question mark on the claim.

### REPL Commands

| Command | Description |
|---------|-------------|
| `<statement>` | Assert a statement in the session language (Klaro by default) as a fact or rule |
| `? <statement>` | Query with proof trace |
| `?? <statement>` | Witness extraction (find all satisfying bindings, `$x` variables) |
| `:debug <statement>` | Show compiled FOL logic |
| `:lang [klaro\|lojban]` | Show or switch the session language (also `NIBLI_LANG` at startup) |
| `:klaro` / `:lojban` | Shorthand language switches |
| `:assert <rel> <args...>` | Assert a fact directly (bypasses text parsing) |
| `:retract <id>` | Retract a fact by ID and rebuild the KB |
| `:facts` | List all active facts |
| `:load <filepath>` | Batch-load a `.klaro` or `.lojban` file (front-end chosen by extension, file-scoped) |
| `:reset` | Clear the entire knowledge base |
| `:compute <predicate>` | Register a predicate for external compute dispatch |
| `:backend [host:port]` | Show or change the compute backend address |
| `:fuel [amount]` | Show or set the WASM fuel limit |
| `:memory [mb]` | Show or set the WASM memory limit |
| `:strict [on\|off]` | Show or set strict mode — reject arity/constraint violations instead of warn-and-insert (also `NIBLI_STRICT=1`) |
| `:contradictions` | Scan the KB for contradictions |
| `:trace <predicate>` | Enable tracing for a predicate |
| `:untrace <predicate>` | Disable tracing for a predicate |
| `:traces` | List all active traces |

---

## Transparency Triad UI

Nibli includes a standalone web UI (Dioxus) — the full reasoning engine (klaro/gerna → smuni → logji) is compiled into the WASM bundle and runs **entirely in the browser**. nibli has no server.

```bash
# Start the web UI (port 8080)
just ui
```

To build a release bundle (`just build-ui`) or self-host — plus the optional jbotci proxy — see [`DEPLOY.md`](DEPLOY.md).

The three tabs are **Source** (plain English), **Klaro** (the formal encoding; the tab follows the language mode), and **Back-translation** (the structure-exposing gloss). The reasoning is fully local; the **only** optional network call is **Formalize** on the Source tab — a *bring-your-own-key* LLM request sent **directly from your browser** to a provider you choose (Anthropic, OpenAI, OpenRouter, Google Gemini, or any OpenAI-compatible/local endpoint). Configure it via the gear button: the API key is held **in that tab's memory only** — never persisted to storage and never routed through any nibli server (there is none), and it is erased on tab close/reload.

Formalize runs the **agentic formalizer** (`nibli-fanva`) — "formalize", not "compile": the LLM step is interpretive and sits *outside* the reasoning firewall, behind deterministic gates. The LLM's draft is validated by the *real compilers* — the klaro front-end (grammar + fail-closed name resolution) + smuni (semantics) + a canonical render **round-trip** check — and any compiler error is fed back for the model to self-correct, so what lands in the Klaro tab already passes those gates. It is still a *draft* — you review the Klaro (and its back-translation) before the deterministic engine reasons over it, and you can skip Formalize entirely and type Klaro directly. In the legacy Lojban input mode (a settings toggle) the gates are gerna + smuni + the official **camxes** parser, and two Lojban-only extras become available: an app-owned **jbotci proxy** (`fanva-proxy/`) for dictionary/grammar tool-use while drafting, and jbotci's `tersmu` deep-meaning graph beside the local gloss.

The header has an **example** dropdown that loads a preloaded, book-derived knowledge base into the triad — **Syllogism** (Ch 19), **GDPR compliance** (Ch 20), or **Drug interactions** (Ch 21). In an example the KB source is read-only, Formalize is disabled, and the query box becomes a dropdown of that example's preset queries (selecting one runs it immediately). The default, **Custom**, is the editable mode. The example corpora are the committed `gdpr.klaro` / `drug-interactions.klaro` twins of the same `.lojban` files the engine's regression tests pin — per-line logical equality between twin corpora is itself CI-enforced (`verify-klaro-twins`).

The UI uses a stateless KB model: every query builds a fresh engine, re-asserts the full KB tab as the knowledge base, then runs the query. The query bar is queries only (no assertions). The KB tab is the single source of truth.

As in the REPL, you **state the claim to check, not ask a question**: type `eats(Adam).` ("Adam eats"), not "Does Adam eat?". The query box shows a fixed `?` purely as a reading cue (`xu` in legacy Lojban mode) — it is never typed into the field and never reaches the engine; the verdict (`TRUE` / `FALSE` / `UNKNOWN`) is the answer.

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
:compute tenfa                      # Register tenfa for external dispatch
tenfa(8, 2, 3).                     # Assert: 8 = 2^3
? tenfa(8, 2, 3).                   # Query: TRUE (computed by Python)
```

**Built-in arithmetic** (always local, no backend needed): `pilji` (multiply), `sumji` (add), `dilcu` (divide) — Klaro spellings `product`/`sum`/`quotient`.

> **One deliberate approximation.** `pilji`/`sumji`/`dilcu` check `x1 = x2 ∘ x3` with **tolerant** float equality — `isclose` with relative tolerance `1e-9` (matching Python's `math.isclose`), i.e. `|a − b| ≤ 1e-9 · max(|a|, |b|)`. So `0.3 = 0.1 + 0.2` answers `TRUE` despite IEEE-754 rounding making the sum `0.30000000000000004`. That is a real, bounded approximation on the numeric result — the one place Nibli is not bit-exact. The equality predicate **`dunli` (`=`) is exact** (`==`, tolerates no rounding); `dilcu`'s divide-by-zero check is likewise an exact guard. The single evaluator (`nibli-types/src/arithmetic.rs`) is shared by the in-WASM engine, the `gasnu` host, and the Python reference backend, so all three agree.

**External predicates** (via backend): `tenfa` (exponentiation), `dugri` (logarithm), and any custom predicates you add to the backend server.

> **Trust boundary.** An external predicate is a **trusted oracle**, not something Nibli proves. When the backend replies `true`, that result is auto-asserted into the knowledge base as a ground fact mid-query, and the reasoner's rules chain on it exactly like a premise you asserted. Nibli never re-derives or checks it — the backend (and whoever operates it) is part of the trusted computing base. A proof that passes through `tenfa`/`dugri` is sound only relative to that oracle.

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
| Front-end parsers | pest (Klaro — the grammar file is the parser) · Logos + recursive descent (legacy Lojban) |
| Dictionary | Compile-time perfect hash function (PHF) |
| Dev environment | Nix flake |
| Compute protocol | TCP + JSON Lines |
| Task runner | Just |
| Web UI | Dioxus (standalone — engine compiled into the WASM bundle) |

---

## Legacy Lojban Front-End

Lojban was nibli's original surface syntax and remains a fully supported **legacy front-end**: select it with `:lojban` / `:lang lojban` in the REPLs, `--lang lojban` on the CLIs, or `NIBLI_LANG=lojban` anywhere. Both front-ends compile to the identical `LogicBuffer` — the equivalence is not aspirational but CI-enforced, per construct (`verify-klaro`) and per corpus line (`verify-klaro-twins`), and the Lojban parser itself is differentially checked against the official grammar (`verify-parser` vs camxes). Feature-level status lives in [LOJBAN_COVERAGE.md](LOJBAN_COVERAGE.md); the engine-behavior contract in [GUARANTEES.md](GUARANTEES.md). The gerna parser retires only at the clean-core v2 milestone (SURFACE_SYNTAX.md §14).

The parser (`gerna`) accepts a practical subset of Lojban sufficient for formal encoding of domain rules:

- **Articles (gadri):** `lo` (existential: "something that is..."), `le` (descriptive: "the thing I have in mind"), `la` (name → constant)
- **Quantifiers:** `ro lo` / `ro le` (universal), `PA lo` / `PA le` (numeric), `su'o lo` (at least one)
- **Prenex:** `ro da [ro de ...] zo'u <body>` — multi-variable universally-quantified rules (lowers to nested `∀`). Firing is currently `members^dep_count`-expensive for two or more free join variables; see `todo.md`.
- **Place tags:** `fa`/`fe`/`fi`/`fo`/`fu` (explicit argument positions)
- **Modal tags:** BAI (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`) and `fi'o`...`fe'u`
- **Selbri (predicates):** root, tanru with Neo-Davidsonian event semantics (resolves the intersective fallacy), conversion (`se`/`te`/`ve`/`xe`), negation (`na`), grouping (`ke`...`ke'e`), compounds (`zei`), argument attachment (`be`...`bei`...`be'o`)
- **Relative clauses:** `poi`/`noi`/`voi` with `ke'a` bound variable and clause stacking. A **disjunctive** restrictor in a universal (`ro lo X poi P ja Q cu R`, also `ganai ga P gi Q gi R`) compiles to one backward-chaining rule per disjunct (DNF rule-splitting) and fires when either disjunct holds; `je` (AND) restrictors still require all conjuncts
- **Connectives:** sumti (`.e`/`.a`/`.o`/`.u` + `nai`), selbri (`je`/`ja`/`jo`/`ju` + the compound negated `jenai`/`janai`/`jonai`/`junai`; bare `na` after a connective is rejected, matching the official grammar), bridi-tail (GIhA: `gi'e`/`gi'a`/`gi'o`/`gi'u` + `nai` fused or spaced, each tail a full predication sharing the head terms, optional `na` per tail; **constant heads only** — a quantified or description head is rejected fail-closed rather than silently re-quantified per tail), sentence (forethought: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; afterthought: `.i je`/`ja`/`jo`/`ju` with `na`/`nai` — solid spellings `.ije`/`.ijenai`/`.inaja` etc. accepted too)
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
- **Four-valued query result:** `TRUE`, `FALSE`, `UNKNOWN` (cycle cut / incomplete knowledge / NAF dependent / backend unavailable / non-finite), `RESOURCE_EXCEEDED` (depth / fuel / memory)
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
- **KB import/export:** RDF Turtle parser, OWL class mapping via the `nibli-import` crate and CLI (`just import <file.ttl>`, with `--raw`/`--export`/`--lang`/`--query` flags)
- **Failure traces:** `PredicateNotFound`, `RuleAttemptFailed`, `EqualitySubstitution` proof rule variants explain why derivations fail
- **Argument-position indexing:** `(relation, position, value)` secondary index for efficient witness extraction
- **Predicate signature validation:** arity checking from PHF dictionary with permissive warnings
- **Closed-world visibility:** `naf_dependent` (a `na→True` NAF result) and its dual `cwa_false` (a `FALSE` that is closed-world — "not derivable", not a disproof — vs. a numeric FALSE that was decided) flag CWA-dependent conclusions on every proof trace; both render a closed-world caveat
- **Interactive debugging:** `:trace`/`:untrace`/`:traces` REPL commands
- **WASM fuel limits:** configurable via `NIBLI_FUEL` or `:fuel` REPL command
- **WASM memory limits:** configurable via `NIBLI_MEMORY_MB` or `:memory` REPL command
- **Error types:** `nibli-error` variant (`syntax`/`semantic`/`reasoning`/`backend`) with line:column for parse errors
- **Batch loading:** `:load <filepath>` loads `.klaro` / `.lojban` files (front-end by extension); `#` lines are comments

---

## Development

| Command | Description |
|---------|-------------|
| `just run` | Full pipeline: build WASM component, launch REPL |
| `just check` | Fast type-check (`cargo check --workspace`) |
| `just test` | Run all unit tests |
| `just test-engine` | Integration tests (full parse → compile → reason pipeline) |
| `just test-klaro` | Klaro front-end tests only |
| `just test-gerna` | Legacy Lojban parser tests only |
| `just test-backend` | Python backend tests |
| `just test-all` | Every test suite |
| `just verify-klaro` | Klaro conformance gates (construct sweep + Klaro↔Lojban translation battery) |
| `just ui` | Standalone Transparency Triad web UI (port 8080) |
| `just backend` | Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with compute backend |
| `just run-persist` | Run with persistent Redb fact store |
| `just fuzz-parse [SECS]` | Fuzz the legacy Lojban parser |
| `just fuzz-klaro [SECS]` | Fuzz the Klaro front-end |
| `just fuzz-assert [SECS]` | Fuzz assertion pipeline |
| `just fuzz-query [SECS]` | Fuzz stateful KB queries |
| `just fuzz-ci [SECS]` | Time-boxed fuzz gate (all 4 targets, corpus-seeded) — runs in CI |
| `just ci` | Full CI suite |
| `just clean` | `cargo clean` |

---

## License

See `LICENSE` for details.
