# Nibli

A Zero-Hallucination Symbolic Reasoning Engine.

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via demand-driven backward-chaining over an indexed fact store. Every conclusion is a formal derivation from the facts + rules you assert, under a closed-world + closed-domain assumption (compute-backend results are trusted as axioms); nothing is fabricated. A `FALSE` verdict means "not derivable," not "proved ¬P". (README's "What zero-hallucination means here" has the full scoping.)

## Environment

- **OS:** Ubuntu on WSL2 (accessed from Windows via `\\wsl.localhost\Ubuntu\...`)
- **Dev shell:** Nix flake — all tools (rustc, cargo-component, wac, just, wasmtime) come from `flake.nix`
- **Enter dev shell:** `nix develop --extra-experimental-features nix-command --extra-experimental-features flakes`
- **Run commands from Windows side:** `wsl -d Ubuntu -e bash -lc "cd ~/projects/dhilipsiva/nibli && nix ... develop --command bash -c '<CMD>'"`
- **Set `CARGO_INCREMENTAL=0`** if running cargo from Windows side (filesystem lock issues)

## Build & Test

All commands must run inside the Nix dev shell. Use `just` as the primary task runner (see `Justfile`):

| Command | What it does |
|---------|-------------|
| `just run` | Full pipeline: clean WASM -> build lasna component -> launch REPL |
| `just check` | Fast type-check all workspace crates (`cargo check --workspace`) |
| `just test` | Run all unit tests (`cargo test --lib -- --nocapture --test-threads=1`) |
| `just test-engine` | Run nibli-engine integration tests (full pipeline: parse → compile → reason) |
| `just test-gerna` | Run gerna (parser) tests only |
| `just test-backend` | Run Python backend tests |
| `just test-gasnu` | Run gasnu host unit tests (trap classification, error/verdict formatting, arithmetic) |
| `just test-all` | Run every test suite (unit + integration + Python) |
| `just ci` | Fast native CI gate (fmt-check, clippy, all native test suites incl. `test-gasnu` + `verify-soundness`). No WASM build. |
| `just verify-soundness` | Differential soundness gate: nibli's verdict must agree with Vampire over the Horn/NAF-free corpus (needs `vampire`, provided by the Nix shell; skips if absent). Part of `ci`. |
| `just ci-wasm` | WASM behavioral gate: build the lasna component + run the six gasnu smokes (fuel exhaustion, post-trap recovery, go'i, persist-replay, NAF note, `:debug`) |
| `just ci-all` | Comprehensive pre-push / pre-release gate: `ci` + `ci-wasm` |
| `just build-wasm` | Build single lasna WASM component |
| `just build-gasnu` | Build native Wasmtime host gasnu (runner) |
| `just backend` | Start the Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with `NIBLI_COMPUTE_ADDR=127.0.0.1:5555` |
| `just ui` | Launch the standalone Transparency Triad web UI (Dioxus, port 8080) — engine runs fully in-browser |
| `just fetch-dict` | Download the lensisku English dictionary to `dictionary-en.json` (needs `LENSISKU_TOKEN`) — see Dictionary Data below |
| `just clean` | `cargo clean` |
| `just fuzz-parse [SECS]` | Fuzz gerna parser (requires `cargo +nightly`). Pass seconds to limit run time. |
| `just fuzz-assert [SECS]` | Fuzz nibli-engine assert_text (full pipeline) |
| `just fuzz-query [SECS]` | Fuzz nibli-engine assert + query (stateful KB) |

**Important:**
- Always use `cargo test --lib` (NOT `cargo test`) — cdylib linker chokes on WIT export symbols containing `@`
  - Exception: `gasnu` is a normal bin (no cdylib/WIT export), so `cargo test -p gasnu` (the `test-gasnu` recipe, gated by `ci`) links fine; the `@` issue only affects `lasna`/the component crates.
- `ci` is the fast native gate (no WASM build). The WASM component + gasnu fuel/memory/trap-recovery behavior is gated by `ci-wasm` (the six smokes); run `ci-all` (= `ci` + `ci-wasm`) as the comprehensive pre-push gate.
- **Regenerate WIT bindings:** `cargo component build` (bindings appear in each crate's `src/bindings.rs`)
  - Note: full build fails on `io-extras` crate (`#![feature]` on stable). Bindings still generate successfully before the failure.
- **REPL uses reedline** — does not work with piped stdin
- Logji (reasoning) tests require `--test-threads=1` (shared global state via RefCell). The Justfile handles this.

## Dictionary Data

`smuni-dictionary` (arity + English gloss + place-frame for every gismu/lujvo/cmavo) is built
at compile time by `smuni-dictionary/build.rs`, which parses **`dictionary-en.json`** at the
repo root — the **lensisku** English bulk export (`lojban/lensisku`,
`DictionaryEntry`: a JSON array, one canonical entry per word, with `word`, `word_type`,
`definition` (place structure as `$x_{N}$` markers), and `gloss_keywords`). This replaced the
legacy reCAPTCHA-gated `jbovlaste-en.xml`.

- The file is **gitignored** and bulk-download needs a login token, so it is NOT in the repo.
  Get it with **`just fetch-dict`** (`export LENSISKU_TOKEN=<bearer token from lensisku.lojban.org>`)
  or download `dictionary-en.json` manually and drop it at the repo root.
- **Without the file** the build falls back to the in-tree `FALLBACK_GISMU_ENTRIES` +
  gloss/cmavo override tables (~140 curated entries) — this is exactly what CI uses, so CI
  needs no network/token. With the file you get the full dictionary — 10,907 entries in
  the current export (1,338 gismu, 8,308 lujvo, 1,261 cmavo).
- Arity/gloss/template for all curated/corpus/test words come from the in-tree tables
  *before* the data file is consulted, so those are **identical with or without** the file;
  only the non-curated long tail differs.

## Compute Backend

The gasnu (runner) acts as a TCP client to an external compute backend server via JSON Lines protocol.

- **Env var:** `NIBLI_COMPUTE_ADDR=host:port` — configures the backend address at startup
- **REPL command:** `:backend [host:port]` — show or change backend address at runtime
- **Protocol:** One JSON object per line. Request: `{"relation":"tenfa","args":[{"type":"number","value":8.0},...]}`. Response: `{"result":true}` or `{"error":"..."}`.
- **Fallback:** Built-in arithmetic (pilji/sumji/dilcu) always handled locally. Unknown predicates forward to external backend. If no backend configured, returns error.
  - **Tolerant equality (disclosed):** pilji/sumji/dilcu compare the result with `isclose` (rel_tol `1e-9`, abs_tol `0`) — a deliberate float approximation so `0.3 = 0.1 + 0.2` is TRUE — in the single shared evaluator `nibli-types/src/arithmetic.rs` (logji guest + gasnu host + `nibli_backend.py` all mirror it). The equality predicate `dunli` is EXACT `==` (`logji/src/compute.rs`). README's "Compute Backend" discloses this to users.
- **Lazy connection:** TCP connects on first external dispatch, auto-reconnects on failure.
- **Trusted oracle (disclosed):** a backend `true` reply is AUTO-ASSERTED as a ground fact mid-query (`assert_typed_fact`), which downstream rules then chain on — the backend is part of the trusted computing base, an axiom source, NOT a derivation. See the TRUST BOUNDARY note at `logji/src/lib.rs` and `logji/src/compute.rs`. README's "What zero-hallucination means here" + "Compute Backend" disclose this to users.
- **Reference server:** `python/nibli_backend.py` — handles pilji, sumji, dilcu, tenfa (exponent), dugri (log). Extend via `HANDLERS` dict.

## Architecture

Core component crates + runtime surfaces:

| Crate | Lojban meaning | Role | Key files |
|-------|---------------|------|-----------|
| `gerna` | grammar | Lojban text -> AST -> flat WIT buffer; shared `go'i` pro-bridi resolver | `grammar.rs`, `ast.rs`, `lib.rs` (flattener), `lexer.rs`, `goi.rs` (`resolve_go_i`, shared by lasna + nibli-engine) |
| `smuni` | meaning | Flat AST buffer -> FOL logic IR -> flat WIT logic buffer | `semantic.rs`, `ir.rs`, `lib.rs` (flattener) |
| `logji` | logic | FOL logic buffer -> backward-chaining assert/query | `lib.rs` (single file, all logic) |
| `lasna` | fasten/connect | Glue: chains gerna -> smuni -> logji | `lib.rs` |
| `gasnu` | agent/doer | Native Wasmtime host, REPL, external compute backend TCP client | `main.rs` |
| `nibli-engine` | — | Native in-process embedding of the pipeline (used by tests + the store layer; no Wasmtime). Stateful prior-bridi snapshot resolves `go'i` identically to lasna (shared `gerna::goi`) | `lib.rs` |
| `nibli-ui` | — | Standalone Dioxus web UI (browser, port 8080) — gerna/smuni/logji compiled in, reasons fully in-browser; optional client-side BYO-key LLM Translate (Source→Lojban), key held in-tab-memory only, no server | `main.rs`, `llm.rs` |
| `nibli-wasm` | — | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo) | `lib.rs` |
| `nibli` | — | Native debug REPL and `nibli-validate` tooling | `main.rs`, `src/bin/validate.rs` |
| `nibli-verify` | — | Differential SOUNDNESS gate (Track A): exports the smuni FOL IR (`LogicBuffer`) of the Horn/NAF-free fragment to TPTP and checks nibli's verdict against the Vampire prover. Not a runtime surface — a CI gate | `lib.rs`, `tptp.rs`, `filter.rs`, `oracle.rs`, `corpus.rs` |
| `python/` | — | Reference compute backend server (TCP + JSON Lines) | `nibli_backend.py` |

- **WIT interfaces:** `wit/world.wit` defines only the SHIPPING component's boundary: `logic-types` (FOL IR), `error-types`, `compute-backend` (host import), `lasna` (session export). `cargo component build -p lasna` regenerates `lasna/src/bindings.rs` (the ONLY crate with WIT bindings; gerna/smuni/logji are plain Rust libs using `nibli-types` directly).
- **WIT worlds:** `lasna-pipeline` is the SOLE world — a single WASM component importing `compute-backend`, exporting `lasna`, with gerna/smuni/logji linked as internal Rust crate deps. (The legacy per-stage `gerna-component`/`smuni-component`/`logji-component` worlds + `gerna`/`smuni`/`logji`/`ast-types` interfaces were removed — they were never built and misled contributors into thinking a per-component architecture existed.)
- **Rust structs:** `LasnaPipeline` (the WASM component) is the only WIT-binding struct.
- **Boundary data:** Flat index-based arrays (`LogicBuffer` for `:debug`/proof output, `LogicalTerm` args) with `u32` indices cross the SINGLE host↔lasna WASM boundary — no heap pointers. The internal gerna→smuni→logji stages are Rust function calls (no WASM boundary), using `nibli-types` flat buffers directly.
- **Compute dispatch:** logji uses injectable function pointers (`logji::register_compute_dispatch`) instead of cfg-gated WIT imports. Lasna registers host-bridge functions at Session creation; native (nibli-engine) and in-browser (nibli-ui/nibli-wasm) modes leave dispatch unregistered — built-in arithmetic (pilji/sumji/dilcu) still resolves locally, external predicates (tenfa/dugri) return an error.

## Canonical Runtime Surfaces

Use these assumptions when selecting entrypoints:

- `gasnu` is the canonical local/operator runtime for the theorem prover. It is the main single-node REPL and the default way to exercise the WASM-hosted pipeline.
- `nibli-ui` is the canonical browser frontend — a standalone Dioxus app with the engine (gerna→smuni→logji) compiled into the WASM bundle. It reasons fully in-browser; there is no server. The one optional network call is the Source→Lojban **Translate** (`nibli-ui/src/llm.rs`): a bring-your-own-key request sent directly from the browser to a user-chosen LLM (Anthropic/OpenAI/OpenRouter/Gemini/Custom), with the key held in tab memory only.
  - **Query model (state, don't ask):** a query is an entailment check of a *proposition* — you state `la .adam. cu citka` ("Adam eats") and the engine returns `TRUE`/`FALSE`/`UNKNOWN`. There is no interrogative form: `xu`/"Does Adam eat?" is **not** a query (`xu la .adam. cu citka` is a parse error). The `xu` shown in the UI query box is a decorative reading cue — not part of `query_text`, never sent to the engine. Keep UI/docs/book copy phrased as "state a claim," never "ask a question."
  - **Example dropdown:** the header offers preloaded book KBs (`nibli-ui/src/examples.rs` — Syllogism/GDPR/Drug-interactions; GDPR+drug corpora `include_str!`-ed from the repo-root `*.lojban` files the `gdpr_*`/`ddi_*` tests pin). Selecting one is read-only (Translate disabled) and turns the query box into a preset-query dropdown that auto-runs; default **Custom** (`example == None`) is the editable mode. The `example` signal lives in `App` and is rendered *conditionally* — Custom buffers are never overwritten.
- `nibli-wasm` is the wasm-bindgen wrapper exposing the same in-browser pipeline to JS (powers the live demo at dhilipsiva.dev/nibli).
- `nibli-engine` is an internal native embedding library, not a user-facing runtime surface.
- `nibli` is developer tooling: a native direct-crate REPL and the `nibli-validate` binary used for validation/data-generation workflows. It is not the canonical production runtime.

## Code Conventions

- Gerna (parser) tests use `as_bridi(&r.sentences[0])` helper to unwrap `Sentence::Simple`
- Grammar tests use `parse_ok()` / `parse_err()` + token constructors `cmavo()`, `gismu()`
- Smuni (semantics) tests use `compile_one(selbris, sumtis, bridi)` helper returning `(LogicalForm, SemanticCompiler)`
- `resolve(&compiler, &spur)` helper to get string from interner in tests
- Connective enums (Je/Ja/Jo/Ju) are shared between selbri and sumti connectives
- BAI tags map to underlying gismu: ri'a->rinka, ni'i->nibli, mu'i->mukti, ki'u->krinu, pi'o->pilno, ba'i->basti

## Codebase Exclusions

When analyzing or searching the codebase:
- **Exclude `docs/` folder** — generated/reference documentation, not source
- **Exclude `**/bindings.rs`** — auto-generated by `cargo component build`, not hand-written

## Known Issues

- `cargo component build` fails on `io-extras` crate — pre-existing, unrelated to our changes. Bindings generate before the failure.
- **rustc ICE in `check_mod_deathness`** — `wasmtime::component::bindgen!` macro triggers compiler panic in library crates (not binary crates like gasnu). Workaround: `#![allow(dead_code)]` at crate root in nibli-engine. Fixed in rustc 1.94.0 (updated via flake).

## Roadmap

See `TODO.md` for the full phased roadmap (Phases 1-5), dependency graph, and technical debt tracker.

## Pre-commit Checklist

Before every commit, always:
1. Update `CLAUDE.md` — if required
2. Update `TODO.md` — remove completed tasks
3. Update `README.md` — if Lojban coverage or reasoning capabilities changed
4. Then commit all code + doc changes together
