# Nibli

[![Release](https://img.shields.io/github/v/release/dhilipsiva/nibli)](https://github.com/dhilipsiva/nibli/releases/latest)
[![crates.io](https://img.shields.io/crates/v/nibli-engine)](https://crates.io/crates/nibli-engine)
[![Docs](https://img.shields.io/badge/docs-dhilipsiva.github.io%2Fnibli-blue)](https://dhilipsiva.github.io/nibli/)

**A zero-hallucination symbolic reasoning engine.**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles **nibli KR** — a human-readable predicate-call knowledge-representation language (`dog(Adam).`, `animal(every dog).`) — into First-Order Logic and performs inference via demand-driven backward chaining over an indexed fact store. Every conclusion is a formal derivation — never a guess, never a generated step. (Lojban, nibli's original surface syntax, retired at THE DROP — the last dual-front-end engine is tagged `v0.1-lojban-final`, and the Lojban tooling was donated to a separate repo.)

> *nibli* (Lojban): x1 logically entails x2 under rules x3

---

## What "zero-hallucination" means here

Nibli derives every conclusion **from the facts and rules you assert, plus any proof-local compute checks evaluated for that query**, under two explicit assumptions:

- **Closed world** — a fact you did not assert is taken to be *false*, not unknown.
- **Closed domain** — quantifiers range only over the entities the knowledge base knows.

Results from the **external compute backend** (`exponential`, `logarithm`, or an existing corpus relation registered for compute routing) are **trusted proof evidence**, not a derivation or a stored premise: a reply decides the current `ComputeCheck` only. The backend is part of the *trusted computing base* for that proof step, so any conclusion that depends on it is only as sound as that oracle. (Valid numeric `product`/`sum`/`quotient` calls are computed locally first; nonnumeric calls require the registered external path — see [Compute Backend](#compute-backend).) So a verdict reads as:

- **`TRUE`** — a proof exists from your facts and rules plus any trusted compute evidence used by this derivation.
- **`FALSE`** — *not derivable* from those premises. This is **not** a proof of ¬P.
- **`UNKNOWN`** — the search could not decide: a cycle, incomplete knowledge, or a negation over an undecided sub-goal.

The guarantee is **soundness relative to what you asserted and any trusted compute replies the proof used**, not omniscience — change those inputs and the verdict can change. What Nibli rules out is *fabrication*: it never invents a fact, a rule, or a proof step.

Native callers can use `KnowledgeBase::check_contradictions_report()` or
`NibliEngine::check_contradictions_report()` to scan represented integrity and
disjunctive constraints, explicit negative assertions, arity and equality
conflicts. Positive counterparts and constraint antecedents include derivation.
The report separates `violations` from `unresolved` checks; `is_clean()` requires
both to be empty. `UNKNOWN`, exhausted bounds, unsupported negation shapes and
evaluation errors never count as a clean scan. The native `:contradictions`
command displays both fields. The older findings-only `check_contradictions()`
remains available for compatibility but cannot establish scan completion.
This is a check of represented constraints, not unrestricted FOL consistency.

---

## The nibli KR Language

nibli KR is a strict predicate-call surface for first-order claims: intuitive to read, but every semantic distinction stays visible in the spelling (the anti-silent-mistranslation design rule). One statement per line, ending with a period. Unknown predicate words are a **compile error**, never a guess — names resolve through the committed English corpus (a four-figure set of strongly-typed predicate entries, every place named), fail-closed; `a+b` compounds resolve only via committed compound entries.

| nibli KR / REPL input | Reads as |
|-------|----------|
| `dog(Adam).` | Adam is a dog |
| `animal(every dog).` | every dog is an animal (a rule) |
| `~eats(Adam).` | Adam does not eat |
| `past eats(me, some food).` | I ate some food |
| `dog(Adam) & cat(Betis).` | conjunction (`->` if-then; `\|` or is queryable, but a *bare* disjunction cannot be asserted — it ingests no facts) |
| `goes(Adam, destination: some market).` | named argument places, Python-style |
| `beautiful(every person where ~cat).` | rule with a negated restrictor (negation-as-failure) |
| `Kim = Adam.` | identity — Kim and Adam are the same individual |
| `? red(exactly 2 red).` | REPL exact-count query over the current KB (`?` selects the query route; it is not KR grammar and the formula is not a persistent constraint) |
| `runs(some [big dog]).` | tanru — juxtaposed modifier, `[ ]` groups explicitly: a big-dog kind of runner (productive, unlike the fail-closed `a+b` compounds) |
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

The front-end emits a flat AST buffer, so everything downstream is shared — an alternative front-end only has to produce that buffer (see [LOGIC_IR.md](LOGIC_IR.md)). The pipeline stages are linked as internal Rust crate dependencies and compiled into a single WASM component:

| Crate | Name origin | Role |
|-------|---------------|------|
| **nibli-kr** | — | nibli KR text → flat AST buffer — the *internal* front-end↔compiler interchange, not a WIT boundary (pest grammar + fail-closed alias resolution + the canonical renderer) |
| **nibli-semantics** | — | AST buffer → FOL logic IR → flat WIT logic buffer |
| **nibli-reason** | — | FOL logic buffer → backward-chaining assertion, query, and proof |
| **nibli-pipeline** | — | Orchestrator: chains the front-end → nibli-semantics → nibli-reason into a single WASM component |
| **nibli-host** | — | Native Wasmtime host, REPL, and TCP compute backend client |

Supporting crates:

| Crate | Role |
|-------|------|
| **nibli-lexicon** | The committed English corpus — strongly-typed predicate + compound entries (name, named places, gloss, template, gismu provenance), const-validated; the single vocabulary source for every stage |
| **nibli-engine** | Native in-process embedding of the pipeline — **the crate to depend on when embedding nibli in Rust** ([Install](#install)) |
| **nibli-ui** | Standalone Dioxus web UI — the engine is compiled in and runs fully in-browser |
| **nibli-wasm** | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo) |
| **nibli** | Native debug REPL and the `nibli-validate` / `nibli-import` / `nibli-pin` tooling |

Everything above **except `nibli-pipeline`, `nibli-host`, `nibli-ui` and `nibli-wasm`** is published on crates.io at the workspace version — those four ship as the WASM component, the host binary and the hosted sites instead ([Install](#install)).

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

- **`nibli-engine`** — The native embedding library, published on crates.io: a library to build on rather than a runtime to launch ([Install](#install)).
- **`nibli-wasm`** — wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo at dhilipsiva.dev/nibli).
- **`nibli`** — Native direct-crate REPL and `nibli-validate`. Developer tooling, not the canonical production path.

Validation names have different scopes. `NibliEngine::validate` is parse+compile only:
it does not mutate the KB and accepts legal query-only IR such as exact counts and
compute formulas. Use `assert_text` for text assertion admission; raw-buffer callers can
run `KnowledgeBase::validate_assertion` as structural preflight before `assert_fact`.
The `nibli-validate` CLI is an assertion-admission reporter: it runs each input statement
through a fresh engine's `assert_text`, so it is per-statement admission rather than a
whole multi-statement KB consistency check.

Every surface speaks nibli KR — the single front-end since THE DROP.

---

## Documentation

Code-derived human docs live in **`mdbook/`** (mdBook). They are **not** the Orange AVA book manuscript (`book/` is a separate, private checkout).

| Surface | How |
|---------|-----|
| **Docs site** | https://dhilipsiva.github.io/nibli/ |
| Local | `just docs` / `just docs-serve` (http://127.0.0.1:3000) inside `nix develop` |
| Site integration (planned) | `dhilipsiva.dev/docs/nibli/` — pending the site-repo copy, see [`DEPLOY.md`](DEPLOY.md) §2b |
| Playground | https://dhilipsiva.dev/nibli-playground/ |
| Rust API | [docs.rs/nibli-engine](https://docs.rs/nibli-engine) — all published crates indexed in the [API index](https://dhilipsiva.github.io/nibli/api-index.html); locally `cargo doc -p <crate> --open` |
| Releasing | [`RELEASING.md`](RELEASING.md) · changes land in [`CHANGELOG.md`](CHANGELOG.md) first |
| Roadmap | [`TODO.md`](TODO.md) |

Root specs remain canonical: [`NIBLI_KR.md`](NIBLI_KR.md), [`LOGIC_IR.md`](LOGIC_IR.md), [`GUARANTEES.md`](GUARANTEES.md).

### Authorization

Built-in, zero-hallucination **authorization** (entailment of `authorized(...)` under a versioned KR policy):

| Piece | Location |
|-------|----------|
| Guide | [mdBook: Authorization](https://dhilipsiva.github.io/nibli/user/authorization.html) (or `just docs-serve`) |
| Rust crate | `nibli-auth` — `Authorizer`, `tls` (thread-local for async servers). Not on crates.io yet (`publish = false`) — use a git or path dependency |
| WIT | `nibli:engine@0.12.0` export `authorizer` (the version lives in `wit/world.wit`) |
| Python | `just build-auth-py` → `nibli_auth` / `nibli_auth_native` |
| Examples | `examples/auth-axum`, `examples/auth-fastapi` (same policy) |
| Tests | `just test-auth`; Python: `just test-auth-py` (maturin; gated by the `auth-py` CI job) |

Policy file: `nibli-auth/policy/auth-0.1.0.nibli`. Extism is **not** the primary interface (optional future PDK only).

## Install

All published crates share one version (workspace lockstep), dual-licensed `MIT OR Apache-2.0`.

> **0.x caveat.** Minor versions may break APIs; the embed surface (`nibli-engine`) is not
> yet declared stable. Every change is documented in [`CHANGELOG.md`](CHANGELOG.md) first.

### Embed the engine in Rust

```bash
cargo add nibli-engine
```

`nibli-engine` is the native in-process embedding — no Wasmtime, no server, no network:

```rust
use nibli_engine::{EngineError, NibliEngine, display_query_result, display_term};

// NOTE: EngineError does not implement std::error::Error, so main returns it
// directly rather than Box<dyn Error>.
fn main() -> Result<(), EngineError> {
    let engine = NibliEngine::new();

    // Assert facts and rules — one nibli KR statement per call.
    engine.assert_text("animal(every dog).")?;
    engine.assert_text("dog(Adam).")?;

    // A query STATES the claim to check; there is no interrogative form.
    let (verdict, proof, _json) = engine.query_text_with_proof("animal(Adam).")?;
    println!("{}", display_query_result(&verdict)); // TRUE
    print!("{proof}");

    // Witness extraction: every binding, or an error if any candidate leaf was
    // non-definitive (partial collections are never returned as complete).
    for bindings in engine.query_find_text("dog($x).")? {
        for b in bindings.iter().filter(|b| b.variable.starts_with('$')) {
            println!("{} = {} [{}]", b.variable, display_term(&b.term), b.origin.label());
        }
    }
    Ok(())
}
```

`NibliEngine::open(path)` swaps the in-memory store for a durable redb one; `query_holds`
returns just the verdict; `retract_fact(id)` retracts by the id `assert_text` minted.
`NibliEngine::validate` only parses and compiles; it does not perform assertion admission
or mutate the KB. Query-only IR can therefore validate successfully and still be rejected
by `assert_text`, which is the admission boundary.
The default profile is clean-core: universals mint no existential witnesses. Legacy
xorlo behavior is an explicit, fallible opt-in with
`engine.set_existential_import(true)?`; changing it transactionally rebuilds the active
KB, and `engine.is_existential_import()` reports the effective profile. Find bindings
and existential/universal proof payloads expose `knowledge-base`,
`generated-witness`, or `existential-import` origin;
count proof steps expose the `existential_imported` share of `actual`.
Full API: [docs.rs/nibli-engine](https://docs.rs/nibli-engine).

### Install the CLI (no Nix required)

```bash
cargo install nibli
```

Installs `nibli` (a native REPL that reasons in-process, so it needs no WASM component),
plus `nibli-validate`, `nibli-import` and `nibli-pin`.

### Prebuilt binaries

From the [latest release](https://github.com/dhilipsiva/nibli/releases/latest). **v0.1.0**
ships Linux x86-64 only, as raw binaries — `nibli-host-v0.1.0-x86_64-linux`,
`nibli-validate-v0.1.0-x86_64-linux`, `nibli-pipeline-v0.1.0.wasm`, and `SHA256SUMS`.

`nibli-host` is the Wasmtime host REPL; it loads the component from `NIBLI_WASM_PATH` and
otherwise looks for a source-tree path that will not exist beside a downloaded binary:

```bash
NIBLI_WASM_PATH=./nibli-pipeline-v0.1.0.wasm ./nibli-host-v0.1.0-x86_64-linux
```

> **The asset layout changes from 0.2.0.** Releases then ship one
> `nibli-<version>-<slug>.tar.gz` per platform (`x86_64-linux`, `aarch64-linux`,
> `aarch64-darwin`), each bundling `nibli-host`, `nibli`, `nibli-validate`, `nibli-pin`
> and the licenses, alongside the `.wasm` and `SHA256SUMS`. Read the asset table on the
> release page itself.

### Build from source

See [Getting Started](#getting-started) — Nix supplies the full toolchain
(cargo-component, wasmtime, just) needed for the WASM component, the UI, and the CI gates.

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
> holds a four-figure set of strongly-typed predicate entries (every place named in English;
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
[Find] _ev0 = sk_7 [generated-witness], $x = adam [knowledge-base]

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

~/nibli> :assert cat Mimi
[Skolem] 1 variable(s) → _ev0 ↦ sk_8
[Fact #3] cat(Mimi) asserted.

~/nibli> :facts
[Facts] 4 active fact(s):
  #0: big(some dog). (1 root)
  #1: animal(every dog). (1 root)
  #2: dog(Adam). (1 root)
  #3: :assert cat (1 root)

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

`exactly N` and `no` are query-only. For example, `? big(exactly 2 dog).`
counts the current matching entity classes; entering the same formula as a bare
assertion fails before a fact id is allocated. Nibli does not store persistent
cardinality constraints, and `exactly 0` is not a prohibition. Assert ordinary
facts, then re-run the count after additions, equality changes, or retractions.

Within one connected statement, a repeated named variable is one witness for both
assertion and query: `bite($x, Bel) & bite($x, Dana).` requires the same biter in
both clauses. Use different names for independent witnesses. Reusing one free name
across a negative, modal, quantified, anonymous-witness, or abstraction boundary is
rejected as scope-ambiguous; separate period-terminated statements are independent.

### REPL Commands

| Command | Description |
|---------|-------------|
| `<statement>` | Assert a statement (nibli KR) as a fact or rule |
| `? <statement>` | Query with proof trace |
| `?? <statement>` | Witness extraction (find all satisfying bindings, `$x` variables) |
| `:debug <statement>` | Show compiled FOL logic |
| `:assert <rel> <args...>` | Assert a fact directly (bypasses text parsing; a registered compute relation — or `exponential`/`logarithm`, registered or not — is rejected as query-only) |
| `:retract <id>` | Retract a fact by ID and rebuild the KB |
| `:facts` | List all active facts |
| `:load <filepath>` | Batch-load a `.nibli` file |
| `:reset` (alias `:r`) | Clear the entire knowledge base |
| `:compute [predicate]` | Show canonical compute relations (bare), or route an existing corpus predicate to external dispatch — this does not declare vocabulary or infer arity; registration is refused while live stored facts or rules reference the relation |
| `:backend [host:port]` (alias `:b`) | Show or change the compute backend address |
| `:fuel [amount]` (alias `:f`) | Show or set the WASM fuel limit |
| `:memory [mb]` (alias `:m`) | Show or set the WASM memory limit |
| `:strict [on\|off]` | Show or set strict mode — reject arity/constraint violations instead of warn-and-insert (also `NIBLI_STRICT=1`) |
| `:existential-import [on\|off]` | Show or set legacy xorlo witness minting (default OFF, clean-core) — explicit ON makes imported witnesses participate in ∃/∀/find/count/aggregate (also `NIBLI_EXISTENTIAL_IMPORT=1`) |
| `:materialize [on\|off]` | Show or set stratum-ordered materialisation (default ON) and print the cumulative query-cone report since the last KB mutation — completed relations and refusal reasons; it may be empty when an exact positive proof needed no saturation (also `NIBLI_MATERIALIZE=0`) |
| `:db` | Show the persistent store status (set `NIBLI_DB_PATH` to enable) |
| `:dump <filepath>` | Write every active fact's source text (label) to a plain file, one statement per line — works with or without the persistent store |
| `:export <redb-filepath>` | Export the persistent store to a redb file (requires `NIBLI_DB_PATH`) |
| `:proof-verbose <statement>` | Query with the full role-level proof trace instead of the collapsed one |
| `:certify <statement>` | Query and print the JSON `ProofEnvelope` — verdict (UNKNOWN reason / resource kind included), proof trace, session profile, and the lockstep engine version, bound into one independently-validatable certificate (document on stdout, validator verdict on stderr) |
| `:help` (alias `:h`) | Show the command list |
| `:quit` (alias `:q`) | Exit the REPL |

Environment: `NIBLI_WASM_PATH` (component path), `NIBLI_FUEL`, `NIBLI_MEMORY_MB`,
`NIBLI_COMPUTE_ADDR`, `NIBLI_DB_PATH`, `NIBLI_QUIET`, plus the mode flags above.

The host prints the active existential-import profile at startup and after a toggle;
the browser UI labels it too. A toggle replays the current assertion registry
transactionally, so already-asserted universals gain or lose their imported witnesses
immediately. `[Find]` marks imported bindings as `[existential-import]`; proof/count
metadata carries the same distinction structurally.

The `nibli` developer REPL (`just run-native`, or `cargo install nibli`) is a *different*
surface — it reasons in-process without Wasmtime and carries extra debugging commands
(`:trace` / `:untrace` / `:traces`) that `nibli-host` does not have.

---

## Transparency Triad UI

Nibli includes a standalone web UI (Dioxus) — the full reasoning engine (nibli-kr → nibli-semantics → nibli-reason) is compiled into the WASM bundle and runs **entirely in the browser**. nibli has no server.

```bash
# Start the web UI (port 8080)
just ui
```

To build a release bundle (`just build-ui`) or self-host, see [`DEPLOY.md`](DEPLOY.md).

The three tabs are **Source** (plain English), **nibli KR** (the formal encoding), and **Back-translation** (the structure-exposing gloss). The reasoning is fully local; the **only** optional network call is **Formalize** on the Source tab — a *bring-your-own-key* LLM request sent **directly from your browser** to a provider you choose (Anthropic, OpenAI, OpenRouter, Google Gemini, or any OpenAI-compatible/local endpoint). Configure it via the gear button: the API key is held **in that tab's memory only** — never persisted to storage and never routed through any nibli server (there is none), and it is erased on tab close/reload.

Formalize runs the **agentic formalizer** (`nibli-formalize`) — "formalize", not "compile": the LLM step is interpretive and sits *outside* the reasoning firewall, behind deterministic gates. The LLM's draft is validated by the *real compilers* — the nibli-kr front-end (grammar + fail-closed name resolution) + nibli-semantics (semantics) + a canonical render **round-trip** check — plus the KB-assertability guard that rejects query-only exact counts. Any gate error is fed back for the model to self-correct, so what lands in the nibli KR tab already passes those gates. It is still a *draft* — you review the nibli KR (and its back-translation) before the deterministic engine reasons over it, and you can skip Formalize entirely and type nibli KR directly.

The header has an **example** dropdown that loads a preloaded knowledge base into the triad — book case studies **Syllogism** (Ch 18), **GDPR compliance** (Ch 19), and **Drug interactions** (Ch 20), plus an optional extra playground corpus when shipped. In an example the KB source is read-only, Formalize is disabled, and the query box becomes a dropdown of that example's preset queries (selecting one runs it immediately). The default, **Custom**, is the editable mode. Book-facing corpora include the committed `gdpr.nibli` and `drug-interactions.nibli` files the engine's regression tests pin.

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
? exponential(8, 2, 3).             # Query: TRUE (computed by Python)
```

**Built-in arithmetic** (valid numeric calls are local, no backend needed): `product` (multiply), `sum` (add), `quotient` (divide). If one of those registered relations receives nonnumeric public terms, local arithmetic is inapplicable and the call follows the external-dispatch contract.

> **One deliberate approximation.** `product`/`sum`/`quotient` check `x1 = x2 ∘ x3` with **tolerant** float equality — `isclose` with relative tolerance `1e-9` (matching Python's `math.isclose`), i.e. `|a − b| ≤ 1e-9 · max(|a|, |b|)`. So `0.3 = 0.1 + 0.2` answers `TRUE` despite IEEE-754 rounding making the sum `0.30000000000000004`. That is a real, bounded approximation on the numeric result — the one place Nibli is not bit-exact. The exact-equality predicate **`num_equal` (`=`) is exact** (`==`, tolerates no rounding); `quotient`'s divide-by-zero check is likewise an exact guard. The single evaluator (`nibli-types/src/arithmetic.rs`) is shared by the in-WASM engine, the `nibli-host` host, and the Python reference backend, so all three agree.

> **Asserted numbers are quantifier-domain members.** A finite number appearing in anything you assert — a fact or a rule's operands, mirroring how constants are noted — is enumerated like any entity: with `big(5).` asserted, `sum(every big, 2, 3).` is `TRUE` because `5` was **checked** (not vacuously), the arithmetically false `sum(every big, 2, 2).` is `FALSE` with `5` as its counterexample, and `exactly N` / `no` / `some` all agree with the universal. Query-time compute never changes that domain. Non-finite values (NaN/±inf — never spellable in nibli KR's digits-only numbers, but injectable via RDF import, `:assert`, or the WIT term API) are skipped from the general quantifier-domain list; if an indexed candidate reaches non-finite arithmetic, witness collections refuse as incomplete rather than return an empty complete set. Exact `CountNode` remains domain-based, so a NaN-only stored extension can be found through an anchored existential while `exactly 0` is TRUE; this accepted candidate-source mismatch is pinned and disclosed in GUARANTEES §Disclosed Sharp Edges.

**External predicates** (via backend): `exponential`, `logarithm`, and any other committed-corpus relation you register for compute routing. Both reference names are query-only as assertions even before registration.

**Text registration is routing, not schema.** `register_compute_predicate(name)` / `:compute name` runs after fail-closed KR name resolution. It accepts corpus-resolvable surface spellings (converted aliases and committed `a+b` compounds included), normalizes them to the canonical relation emitted in IR, and preserves the corpus arity and named places. It rejects an unknown name immediately; it never guesses arity or makes that name legal in `query_holds`, `query-text`, `compile_debug`, or `validate`. To call an arbitrary backend relation today, a native embedder must construct an explicit `LogicNode::ComputeNode`—whose argument vector supplies the shape—and query it through `nibli_reason::KnowledgeBase`. Raw compute IR remains query-only. The shipping WIT component exports no raw-buffer query, so arbitrary component-side text names await the explicit vocabulary/schema extension specified (but not yet implemented) in NIBLI_KR §14.1, or a separately designed raw-query API. Adding a Python `HANDLERS` entry alone does not extend KR vocabulary.

> **Trust boundary.** An external predicate is a **trusted oracle**, not something Nibli proves. Its reply decides the current `ComputeCheck`, so the backend (and whoever operates it) is part of the trusted computing base for any proof that uses that step. Nibli does not independently verify the answer; a proof that passes through `exponential`/`logarithm` is sound only relative to that oracle.

### External compute admission policy

The stock `nibli-host` and `NibliEngine::enable_compute_backend` path is
deliberately **low-assurance**: plaintext, unauthenticated JSON Lines over TCP.
The wire protocol has no peer identity, confidentiality, cryptographic integrity
or request/response identifier, protocol/backend/schema version, nonce or
timestamp, freshness/expiry, replay/revocation check, or admission audit record.
A parseable `{"result": true|false}` received in stream order is trusted for that
proof-local check. A validly encoded reply that is forged, replayed, stale,
reordered, or supplied by a revoked peer is not detectable. Only an unconfigured
backend, connection/timeout failure, parse failure, or explicit backend error
becomes `UNKNOWN (backend-unavailable)`; this is not authentication.

Use the stock path only when the operator accepts the backend and network path as
part of the TCB—normally loopback or a controlled segment. Deployments needing
stronger admission can install a native `NibliEngine::set_compute_dispatch`
adapter, implement the WIT `compute-backend` import in a custom component host,
or provide an external secured transport. The stock `:backend` /
`NIBLI_COMPUTE_ADDR` configuration changes only the address; it has no TLS,
signature, or policy plug-in. The current proof schema identifies the backend
`ComputeCheck` but cannot carry backend identity, wire transcripts, timestamps,
nonces, or admission receipts. `nibli-auth` authorizes application actions; it
does not authenticate this compute socket.

> **Compute results are proof-local and query-only.** Built-in and external results are evidence for the current derivation only. They are never inserted into the typed fact store or fact registry, receive no fact id, do not appear in `:facts`, cannot be retracted, never join the quantifier domain, are not persisted or replayed, and trigger no forward chaining. Assertion ingress rejects executable compute atoms—including rule guards and conclusions—before allocating an id; opaque abstraction content remains quoted. Registration itself is guarded: unknown text names are refused because registration is not schema; `exponential`/`logarithm` are refused at assertion ingress registered or not; and registering a corpus relation while live stored facts or rules reference it is refused with the blocking ids named — retract first. Registration order can no longer strand a stored fact. Each top-level query recomputes locally or redispatches to the backend. Repeated identical external checks may share only a transient within-query memo so the verdict and proof cannot disagree; compiled corpus KR queries and native raw `ComputeNode` queries have the same proof-local/query-only lifecycle.

Configure `nibli-host` with `NIBLI_COMPUTE_ADDR=host:port` or `:backend host:port`. Native embedders can use `NibliEngine::enable_compute_backend` or `set_compute_dispatch`. Connections are lazy (connect on first dispatch) with auto-reconnect. The browser surfaces have no external dispatch; built-in arithmetic still works everywhere.

If an external predicate's backend is unreachable (or unconfigured), the query returns `UNKNOWN (backend-unavailable)` — never a definitive `FALSE`. This is uniform: an earlier successful call and an ordinary stored fact with the same tuple do not act as an outage cache or bypass dispatch. A backend the engine cannot consult is genuinely undetermined. The same fail-closed result applies when a call would expose an opaque internal witness to the string-only compute protocol; an equal-looking user constant such as `"sk_0"` remains ordinary data and is forwarded.

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
- **Skolemization:** independent and dependent generated witnesses have opaque,
  source-scoped typed identity (`Skolem` / `SkolemFn` + `DepPair` for
  multi-dependency); friendly `sk_N` text is display only and cannot alias a user
  constant
- **Proof traces:** every query produces a proof tree over the `ProofRule` taxonomy (`nibli-types/src/logic.rs`) with DAG memoization via `ProofRef`. Stored truth and source are separate: `Asserted` lists every active fact id/label, `Derived` cites stable assertion-local rule ids and grounded premises (including eagerly stored conclusions), and existential-import facts are `Presupposed`, never `[given]`
- **Witness extraction:** `query-find` returns all satisfying binding sets for existential variables, or a reasoning error if any evaluated candidate leaf is `UNKNOWN`/`RESOURCE_EXCEEDED`; it never returns a partial set as complete
- **Belief revision:** retract-and-rebuild with monotonic fact IDs; `:retract <id>` and `:facts` REPL commands
- **Four-valued query result:** `TRUE`, `FALSE`, `UNKNOWN` (cycle cut / incomplete knowledge / NAF dependent / backend unavailable / non-finite), `RESOURCE_EXCEEDED` (depth / fuel / memory)
- **Temporal reasoning:** `Past`/`Present`/`Future` wrappers are preserved end-to-end and ordinary predicate rule literals are flavor-exact. Bare rules are bare-only; write mappings explicitly (`all $x: past dog($x) -> past animal($x).`). One atom may have a temporal prefix or a deontic prefix, never both: mixed stacks fail at KR compilation, and manually nested raw-IR wrappers fail at engine ingress
- **Neo-Davidsonian event semantics:** every predication decomposes into event type + role predicates; compound predicates share event variables
- **Conjunction introduction:** `And(A, B)` verified recursively with mutual `InDomain` entities (bounded, no exponential blowup)
- **Numerical comparisons:** `greater` (>), `less` (<), `num_equal` (==) evaluated at query time on `Num` terms — deciding the verdict *and* filtering witnesses, so `quantity($x, $n) & greater($n, 15).` finds exactly the rows past the threshold. Query-time ONLY: a comparison whose operands could be numbers is refused at assertion ingress, in a ground fact and in every rule position alike, because a query computes it while a rule would look it up in a store that holds none. There is deliberately no numeric threshold RULE (GUARANTEES §Disclosed Sharp Edges records the decision and its re-open trigger). A comparison between non-numeric terms (`greater(Alis, Bob)`, "taller than") is an ordinary relational fact and asserts normally
- **Compute dispatch:** `compute-backend` WIT protocol with `ComputeNode` IR variant; results are proof-local and never stored as KB facts. Find/count/aggregate never dispatch, and any non-definitive compute leaf makes the collection incomplete rather than empty
- **Ground conjunction flattening:** top-level `And` trees flattened before assertion; ground material conditionals auto-registered as zero-variable rules for modus ponens
- **Equality reasoning:** the `=` identity builtin (compiled relation `equals`) with union-find congruence closure; proof substitution follows and cites actual stored equality edges rather than presenting a compressed class link as an asserted equality
- **Stratification enforcement:** predicate dependency graph analysis prevents unsound negative cycles
- **Query-cone-scoped stratum-ordered materialisation:** the stratification is also USED, not only checked — only a query-reachable cone that needs NAF completeness is saturated bottom-up, so `~p(x)` is a set-membership test rather than an exhaustive attempt to prove `p(x)` and fail. Purely positive entailment stays lazy unless exact reasoning remains non-definitive (for example at a depth or cycle cut); an exact single-positive rule antecedent may also request only its own cone after a depth cut, and find/count request their positive cone up front. Requested roots accumulate until mutation. Quoted abstraction bodies remain opaque, and unrelated recursive relations do no work. Fail-closed: tense/deontic flavours, `du` equivalence classes, compute conditions and non-projectable rules are refused and keep the ordinary backward-chaining path. `NIBLI_MATERIALIZE=0` turns it off
- **Integrity constraints:** `deny` rules enforce assertion-time invariants
- **Defeasible rules:** priority-ordered rule matching (`priority: u32`)
- **Sorted logic:** type hierarchy with subsort checking
- **Hypothetical reasoning:** `with_assumptions()` for clone-query-discard patterns
- **Selective forward chaining:** `forward: bool` on rules with `trigger_forward_rules`
- **Aggregation:** `count_witnesses`, `aggregate(Sum/Min/Max/Avg)`
- **Persistent fact store:** `FactStore` trait with in-memory (`InMemoryFactStore`) and redb (`RedbFactStore`) backends
- **Iterative deepening:** shallowest-proof guarantee
- **Tabling:** cached results with invalidation on mutations
- **KB import/export:** RDF Turtle parser, OWL class mapping, and fail-closed N-Triples export via the `nibli-import` crate and CLI (`just import <file.ttl>`, with `--raw`/`--export`/`--query` flags) — export emits real triples for the representable fragment and refuses everything else with a per-fact reason, pinned by an independent-parser round trip
- **Failure traces:** `PredicateNotFound`, `RuleAttemptFailed`, `EqualitySubstitution` proof rule variants explain why derivations fail
- **Argument-position indexing:** `(relation, position, value)` secondary index for efficient witness extraction
- **Predicate signature validation:** arity checking from PHF dictionary with permissive warnings
- **Closed-world visibility:** `naf_dependent` (a `na→True` NAF result) and its dual `cwa_false` (a `FALSE` that is closed-world — "not derivable", not a disproof — vs. a structurally compute-decided FALSE) flag CWA-dependent conclusions on every proof trace; both render a closed-world caveat
- **Interactive debugging:** `:debug <text>` in the `nibli-host` REPL; `:trace`/`:untrace`/`:traces` in the `nibli` developer REPL (`just run-native`)
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
| `just verify-soundness` | The differential soundness gate (Vampire + clingo oracles, plus the stratification/retraction/materialisation differentials) |
| `just verify-proofs` | Check the Lean 4 mechanized soundness proofs |
| `just verify-pins` | KB-level behavioural pins (`pins/*.nibli`) |
| `just release-check` | Release consistency gate (lockstep versions, publish flags, crates.io metadata) — part of `ci` |
| `just ci` | Fast native gate: fmt, clippy, all native test + verify gates (no WASM build) |
| `just ci-all` | Comprehensive gate — `ci` + the 16 WASM behavioural smokes. This is what GitHub CI runs |
| `just clean` | `cargo clean` |

---

## Releasing

Full runbook: **[`RELEASING.md`](RELEASING.md)** — it covers what is and is not reversible,
the yank policy, hotfixes, and partial-publish recovery. Changes land in
[`CHANGELOG.md`](CHANGELOG.md) first.

All publishable crates share one version (lockstep — there is no per-crate semver), and the
WIT ABI version (`nibli:engine@…`) moves independently of it.

| Command | Description |
|---------|-------------|
| `just release-prep X.Y.Z` | Bump the version, roll the CHANGELOG, refresh the lock — commits and tags nothing |
| `just release-verify X.Y.Z` | Is this tree exactly X.Y.Z and ready to ship? (release moment only) |

Pushing a `vX.Y.Z` tag runs [`.github/workflows/release.yml`](.github/workflows/release.yml):
preflight → gates + artifacts → **draft** GitHub Release → crates.io → undraft. The
irreversible step runs last, and the release stays a draft until it succeeds. Rehearse any
time via Actions → Release → *Run workflow*; a manual run is always a dry run.

---

## License

Dual-licensed under either [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your
option. See [`NOTICE`](NOTICE) for third-party attributions — the committed corpus derives
from lensisku/jbovlaste data under CC-BY-SA.
