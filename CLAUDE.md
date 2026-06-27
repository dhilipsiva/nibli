# Nibli

A Zero-Hallucination Symbolic Reasoning Engine.

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via demand-driven backward-chaining over an indexed fact store. Every conclusion is formally derived — no hallucination, no approximation.

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
| `just ci` | Fast native CI gate (fmt-check, clippy, all native test suites incl. `test-gasnu`). No WASM build. |
| `just ci-wasm` | WASM behavioral gate: build the lasna component + run the six gasnu smokes (fuel exhaustion, post-trap recovery, go'i, persist-replay, NAF note, `:debug`) |
| `just ci-all` | Comprehensive pre-push / pre-release gate: `ci` + `ci-wasm` |
| `just build-wasm` | Build single lasna WASM component |
| `just build-gasnu` | Build native Wasmtime host gasnu (runner) |
| `just backend` | Start the Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with `NIBLI_COMPUTE_ADDR=127.0.0.1:5555` |
| `just ui` | Launch the standalone Transparency Triad web UI (Dioxus, port 8080) — engine runs fully in-browser |
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

## Compute Backend

The gasnu (runner) acts as a TCP client to an external compute backend server via JSON Lines protocol.

- **Env var:** `NIBLI_COMPUTE_ADDR=host:port` — configures the backend address at startup
- **REPL command:** `:backend [host:port]` — show or change backend address at runtime
- **Protocol:** One JSON object per line. Request: `{"relation":"tenfa","args":[{"type":"number","value":8.0},...]}`. Response: `{"result":true}` or `{"error":"..."}`.
- **Fallback:** Built-in arithmetic (pilji/sumji/dilcu) always handled locally. Unknown predicates forward to external backend. If no backend configured, returns error.
- **Lazy connection:** TCP connects on first external dispatch, auto-reconnects on failure.
- **Reference server:** `python/nibli_backend.py` — handles pilji, sumji, dilcu, tenfa (exponent), dugri (log). Extend via `HANDLERS` dict.

## Architecture

Core component crates + runtime surfaces:

| Crate | Lojban meaning | Role | Key files |
|-------|---------------|------|-----------|
| `gerna` | grammar | Lojban text -> AST -> flat WIT buffer | `grammar.rs`, `ast.rs`, `lib.rs` (flattener), `lexer.rs` |
| `smuni` | meaning | Flat AST buffer -> FOL logic IR -> flat WIT logic buffer | `semantic.rs`, `ir.rs`, `lib.rs` (flattener) |
| `logji` | logic | FOL logic buffer -> backward-chaining assert/query | `lib.rs` (single file, all logic) |
| `lasna` | fasten/connect | Glue: chains gerna -> smuni -> logji | `lib.rs` |
| `gasnu` | agent/doer | Native Wasmtime host, REPL, external compute backend TCP client | `main.rs` |
| `nibli-engine` | — | Native in-process embedding of the pipeline (used by tests + the store layer; no Wasmtime) | `lib.rs` |
| `nibli-ui` | — | Standalone Dioxus web UI (browser, port 8080) — gerna/smuni/logji compiled in, reasons fully in-browser; optional client-side BYO-key LLM Translate (Source→Lojban), key held in-tab-memory only, no server | `main.rs`, `llm.rs` |
| `nibli-wasm` | — | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo) | `lib.rs` |
| `nibli` | — | Native debug REPL and `nibli-validate` tooling | `main.rs`, `src/bin/validate.rs` |
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
