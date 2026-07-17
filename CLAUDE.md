# Nibli

A Zero-Hallucination Symbolic Reasoning Engine.

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles nibli KR — the nibli knowledge-representation (KR) language, a human-readable predicate-call surface — into First-Order Logic and performs inference via demand-driven backward-chaining over an indexed fact store. Every conclusion is a formal derivation from the facts + rules you assert, under a closed-world + closed-domain assumption (compute-backend results are trusted as axioms); nothing is fabricated. A `FALSE` verdict means "not derivable," not "proved ¬P". (README's "What zero-hallucination means here" has the full scoping.)

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
| `just run` | Full pipeline: clean WASM -> build nibli-pipeline component -> launch REPL (KR-only since THE DROP, 2026-07-13) |
| `just check` | Fast type-check all workspace crates (`cargo check --workspace`) |
| `just test` | Run all unit tests (`cargo test --lib -- --nocapture --test-threads=1`) |
| `just test-engine` | Run nibli-engine integration tests (full pipeline: parse → compile → reason) |
| `just test-nibli-kr` | Run nibli-kr (surface-syntax front-end) tests only — dev loop; `just test` already sweeps them into `ci` |
| `just test-alias-map` | Run nibli-lexicon's unit tests only — the folded alias-map tests (alias/label/reserved) plus the forward-dict tests, one crate now — dev loop; `just test` already sweeps them into `ci` |
| `just verify-nibli-kr-seam` | The KR→nibli-semantics seam-conformance gate — the KR front-end's independent oracle (it OUTLIVED THE DROP as designed) (`nibli-verify/tests/nibli_kr_seam_gate.rs` + the `nibli_kr_seam` generator module): 14 hand-verified FOL structural goldens (event decomposition, ∀-implication vs ∃-conjunction shapes, converted-alias `ponse_x1/x2` routing, named-arg place routing, tense/deontic order incl. the re-hosted O3 pin, flat `du`, prenex implication, `__abs_` opacity, exact-count-0, `?`-vs-`$x $x` independence), the CONSTRUCT_INVENTORY acceptance sweep (every §3–§9 KR spelling compiles, per-section floors), KR-internal metamorphic relations (the O7 block-every ≡ prenex pin re-anchored KR≡KR + named≡positional + converted≡label-permuted + a 60-seed batch over three families: label permutation, `no`≡`exactly 0`, conjoined≡stacked clause bodies), and the re-homed `determinism_corpus_nibli_kr_native` leg. Curated-core vocabulary only — full-strength in BOTH dictionary modes, never skips. Part of `ci`. |
| `just verify-alias-map` | Alias-map differential gate: the SHIPPED nibli-lexicon alias map's intra-crate invariants — per-alias arity self-consistency against `nibli_lexicon::get_arity`, `GISMU_TO_ALIAS` round-trips (canonical alias unswapped), swap validity (`2..=arity`, involution, peels to a canonical alias), reserved-word exclusion + label integrity re-asserted from the shipped map, coverage floors, PLUS a behavioral battery: for EVERY shipped alias, `alias(A, B, …)` must compile canonically EQUAL to the raw-gismu spelling with explicitly permuted `xN` labels (the identity-passthrough twin — no other front-end involved). Dual-mode, never skips: full local build checks all ~1,341 aliases, CI fallback checks the curated core (FALLBACK MODE banner). Since the fold, alias↔dictionary arity agreement holds by construction (one crate, one parse). Part of `ci`. |
| `just test-backend` | Run Python backend tests |
| `just test-host` | Run nibli-host host unit tests (trap classification, error/verdict formatting, arithmetic) |
| `just test-formalize` | Run nibli-formalize native tests (agentic loop + history trim, the local gates incl. the render round-trip gate, the grounded-prompt guards — few-shots gate-valid + the assembled prompt embeds the pest grammar and the alias map, the semantic verification turn incl. the KR Genesis silent-mistranslation fixture, LLM request/response shapes). Part of `ci`. |
| `just test-ui` | Run nibli-ui's native tests — the shipped-examples guard (`shipped_examples_compile`): every example KB line + preset query compiles through the nibli KR front-end. Dual-mode: the CI fallback build vocab-skips "unknown predicate" long-tail KB lines (with a floor); preset QUERIES never skip — curated-core vocabulary by policy, so the dropdown works even in a fallback-built bundle. nibli-ui is bin-only, so `just test` (`--lib`) skips it — this gates it in `ci`. |
| `just test-all` | Run every test suite (unit + integration + Python) |
| `just ci` | Fast native CI gate (fmt-check, clippy, all native test suites incl. `test-host` + `test-ui` + `test-formalize` + `verify-soundness` + `verify-alias-map` + `verify-nibli-kr-seam` + `verify-dict` + `verify-proofs`). No WASM build. |
| `just verify-soundness` | Differential soundness gate (Track A), **two oracles** over KR-generated programs: **(1) Vampire** (classical FOL) over the Horn/NAF-free fragment — curated cases (incl. ground `=`-equality mapped to TPTP native `=`), a seeded batch of random Horn programs with mixed-in identity links (`NIBLI_VERIFY_RANDOM_COUNT`, default 200), the auto-extracted mappable slice of the `gdpr`/`ddi` corpora, and the **Predilex taxonomy leg** (`run_predilex_taxonomy`) — real-vocabulary rule programs from the vendored Predilex hypernym links, pre-filtered to words the fail-closed KR resolve accepts (dual-mode, non-vacuity floor); **(2) clingo** (ASP/Datalog) over the stratified-NAF + closed-world fragment — a curated NAF corpus (incl. the real GDPR deontic-NAF erasure rule and `=`×NAF cases) + random stratified-NAF programs (`NIBLI_VERIFY_NAF_RANDOM_COUNT`, default 100). Tense flavors (`past`/`now`/`future`) covered by both oracles via the flavorization pre-pass (`tense.rs`); exact-count queries as `#count` aggregates (`NIBLI_VERIFY_COUNT_RANDOM_COUNT`, default 100). Plus **(3) the non-stratified-rejection differential** (`strat_diff.rs`, `NIBLI_VERIFY_STRAT_RANDOM_COUNT`, default 300) with the post-rejection fresh-replay battery, and **(4) the retraction metamorphic differential** (`retract_diff.rs`, `NIBLI_VERIFY_RETRACT_RANDOM_COUNT`, default 200) — retract ≡ never-asserted on both the O(1) and rebuild paths; both native-only, never skip. Needs `vampire` + `clingo` for oracles (1)+(2) (Nix shell; each side skips if its solver is absent). Part of `ci`. |
| `just verify-dict` | Dictionary-arity differential gate: the shipped `nibli-lexicon` arities must COVER independent lower bounds derived from **Predilex** (CC0 thesaurus of sememes-as-predicates, vendored + SHA-pinned in `nibli-verify/vendor/predilex/`; the data rules live in `nibli-verify/src/predilex.rs`). Predilex sememes are systematically coarser than Lojban place structures, so the sound invariant is a LOWER BOUND: an undercount (dictionary arity < bound) flags a truncated place structure (its first run caught the `cusku` 3→4 override pin); overcounts pass as expected coarseness. `KNOWN_UNDERCOUNTS` allowlist (value-pinned, still-undercounting invariant) holds hand-verified lensisku definition-text gaps only. Dual-mode, never skips: full local build (`just fetch-dict`) checks ~198 words; the CI fallback build checks the curated core set (loud FALLBACK MODE banner). Part of `ci`. |
| `just verify-proofs` | Mechanized-proof gate (Track B): check the Lean 4 soundness proofs in `proofs/` (needs `lean`, provided by the Nix shell; skips if absent). Part of `ci`. |
| `just ci-wasm` | WASM behavioral gate: build the nibli-pipeline component + run the nibli-host smokes — all payloads KR (script, trap recovery, persist-replay, statement-split + buffer replay, NAF note, `:debug`, collapse, backend-unavailable via the `tenfa` identity spelling, quiet, strict). Determinism legs: `smoke-host-determinism` (the pinned `determinism-corpus.nibli` through the Wasmtime component) and `verify-wasm-node` (the same corpus through the wasm32-unknown-unknown build under node/V8; skips cleanly if wasm-pack is absent). The native leg is `determinism_corpus_nibli_kr_native` (`verify-nibli-kr-seam`). |
| `just ci-all` | Comprehensive pre-push / pre-release gate: `ci` + `ci-wasm` |
| `just build-wasm` | Build single nibli-pipeline WASM component |
| `just build-host` | Build native Wasmtime host nibli-host (runner) |
| `just backend` | Start the Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with `NIBLI_COMPUTE_ADDR=127.0.0.1:5555` |
| `just ui` | Launch the standalone Transparency Triad web UI (Dioxus, port 8080) — engine runs fully in-browser |
| `just build-ui` | Build the nibli-ui web bundle for release (`dx build --release` → `target/dx/nibli-ui/release/web/public/`) — a local preview / pre-merge sanity build; the PRODUCTION build runs in the external dhilipsiva.dev site repo (see `DEPLOY.md`) |
| `just fetch-dict` | Download the lensisku English dictionary to `dictionary-en.json` (public dump, no login) — see Dictionary Data below |
| `just import FILE [ARGS]` | Import an RDF Turtle / OWL file into a fresh KB via the `nibli-import` CLI (`--raw` skips OWL class handling, `--export` prints the round-trip view, `--query "<text>"` runs entailment checks — reaches only dictionary/alias-resolvable names, fail-closed; English/camelCase RDF predicates import as facts but await the v2 schema registry, NIBLI_KR §14.1). NOTE: just's variadic args lose shell quoting — run `./target/debug/nibli-import` directly for multi-word queries |
| `just bench-book` | Timing pins for the book's quoted figures (Ch 13 latency numbers, Ch 20 sequence): release-profile native bench over `gdpr.nibli` — corpus load / lawful-basis query / full Ch-20 sequence (load + query + consent retraction + 2 re-queries), min/median/max over `NIBLI_BENCH_RUNS` runs (default 10), every verdict asserted every run. The source for any latency figure the book quotes — never hand-write timings |
| `just verify-book-refs` | Book-reference conformance gate (detection only): every WIT name, REPL command (`nibli-host` + `nibli` debug REPL), Rust struct field, and notation form the book quotes must match the repo (`book/tools/verify_book_refs.py`, per-claim report). EXPECTED red until the book reconciliation pass; wiring into `ci` is a book-repo decision after that. Skips when `book/` is absent |
| `just count-tests` | Derive the current test-suite counts (unit + native integration/bin targets). The source for any doc that needs a figure — never hand-write test counts (pre-commit checklist) |
| `just clean` | `cargo clean` |
| `just fuzz-assert [SECS]` | Fuzz nibli-engine assert_text (full pipeline) |
| `just fuzz-query [SECS]` | Fuzz nibli-engine assert + query (stateful KB; split-half input: first half asserted, second half queried) |
| `just fuzz-nibli-kr [SECS]` | Fuzz the nibli KR front-end (parse → resolve → emit): any accepted input must compile through nibli-semantics WITHOUT a "corrupt AST buffer" rejection — a structurally invalid emitted buffer is a nibli-kr bug, surfaced as an oracle panic (plus the usual crash/leak detection) |
| `just fuzz-seed` | Seed `fuzz/corpus/` for the three targets from the shipped `.nibli` corpora + `nibli-kr/tests/acceptance.nibli` |
| `just fuzz-ci [SECS]` | Unattended fuzz gate: `fuzz-seed` + all three targets × SECS (default 120) each; non-zero on crash/OOM/leak. Runs as a parallel `fuzz` job in the GitHub workflow. |
| `just mutants [JOBS]` | Mutation-testing gate over the soundness paths (scope + per-mutant test set in `.cargo/mutants.toml`: nibli-reason/nibli-semantics/nibli-engine suites per mutant). Diffs survivors against `mutants-baseline.txt` (line:col-stripped): fails on any NEW survivor, prompts a shrink for killed ones. On-demand (~17 min full sweep), not in the per-push gate. Baseline + stats in GUARANTEES.md. |

**Important:**
- Always use `cargo test --lib` (NOT `cargo test`) — cdylib linker chokes on WIT export symbols containing `@`
  - Exception: `nibli-host` is a normal bin (no cdylib/WIT export), so `cargo test -p nibli-host` (the `test-host` recipe, gated by `ci`) links fine; the `@` issue only affects `nibli-pipeline`/the component crates.
- `ci` is the fast native gate (no WASM build). The WASM component + nibli-host fuel/memory/trap-recovery behavior is gated by `ci-wasm` (the six smokes); run `ci-all` (= `ci` + `ci-wasm`) as the comprehensive pre-push gate.
- **Regenerate WIT bindings:** `cargo component build` (bindings appear in each crate's `src/bindings.rs`)
  - Note: full build fails on `io-extras` crate (`#![feature]` on stable). Bindings still generate successfully before the failure.
- **REPL uses reedline** — does not work with piped stdin
- Logji (reasoning) tests require `--test-threads=1` (shared global state via RefCell). The Justfile handles this.

## Dictionary Data

`nibli-lexicon` (arity + English gloss + place-frame for every gismu/lujvo/cmavo) is built
at compile time by `nibli-lexicon/build.rs`, which parses **`dictionary-en.json`** at the
repo root — the **lensisku** English bulk export (`lojban/lensisku`,
`DictionaryEntry`: a JSON array, one canonical entry per word, with `word`, `word_type`,
`definition` (place structure as `$x_{N}$` markers), and `gloss_keywords`). This replaced the
legacy reCAPTCHA-gated `jbovlaste-en.xml`, which is now fully retired — nothing reads it
(the book's `verify_book.py` VOCAB check reads this JSON too, skipping cleanly when absent).

- The file is **gitignored**, so it is NOT in the repo. Get it with **`just fetch-dict`** —
  lensisku's nightly cached dumps are public (no login;
  `GET https://lensisku.lojban.org/api/export/cached/{lang}/{format}` — GET only, HEAD 401s) —
  or download `dictionary-en.json` manually and drop it at the repo root.
- **Without the file** the build falls back to the in-tree `FALLBACK_GISMU_ENTRIES` +
  gloss/cmavo override tables (~175 curated entries; every gismu the folded
  curated alias table references is included with its full-derivation arity — the
  `verify-alias-map` gate enforces this) — this is exactly what CI uses, so CI
  needs no network. With the file you get the full dictionary — the export carries
  ~17.5k entries across all word types; the build consumes the gismu/lujvo/cmavo types
  (1,338 gismu, 8,322 lujvo, 1,261 cmavo in the current export).
- Arity/gloss/template for all curated/corpus/test words come from the in-tree tables
  *before* the data file is consulted, so those are **identical with or without** the file;
  only the non-curated long tail differs.

## Compute Backend

The nibli-host (runner) acts as a TCP client to an external compute backend server via JSON Lines protocol.

- **Env var:** `NIBLI_COMPUTE_ADDR=host:port` — configures the backend address at startup
- **REPL command:** `:backend [host:port]` — show or change backend address at runtime
- **Protocol:** One JSON object per line, keyed on the ENGLISH relation name (the IR is Lojban-free since the predicate-name flip). Request: `{"relation":"exponential","args":[{"type":"number","value":8.0},...]}`. Response: `{"result":true}` or `{"error":"..."}`.
- **Fallback:** Built-in arithmetic (product/sum/quotient) always handled locally. Unknown predicates forward to external backend. If no backend configured, returns error.
  - **Tolerant equality (disclosed):** product/sum/quotient compare the result with `isclose` (rel_tol `1e-9`, abs_tol `0`) — a deliberate float approximation so `0.3 = 0.1 + 0.2` is TRUE — in the single shared evaluator `nibli-types/src/arithmetic.rs` (nibli-reason guest + nibli-host host + `nibli_backend.py` all mirror it). The exact-equality predicate `num_equal` is EXACT `==` (`nibli-reason/src/compute.rs`). README's "Compute Backend" discloses this to users.
- **Lazy connection:** TCP connects on first external dispatch, auto-reconnects on failure.
- **Trusted oracle (disclosed):** a backend `true` reply is AUTO-ASSERTED as a ground fact mid-query (`assert_typed_fact`), which downstream rules then chain on — the backend is part of the trusted computing base, an axiom source, NOT a derivation. See the TRUST BOUNDARY note at `nibli-reason/src/lib.rs` and `nibli-reason/src/compute.rs`. README's "What zero-hallucination means here" + "Compute Backend" disclose this to users.
- **Reference server:** `python/nibli_backend.py` — handles product, sum, quotient, exponential, logarithm (all keyed on the English relation name). Extend via `HANDLERS` dict.

## Architecture

Core component crates + runtime surfaces:

| Crate | Name origin | Role | Key files |
|-------|---------------|------|-----------|
| `nibli-semantics` | — | Flat AST buffer -> FOL logic IR -> flat WIT logic buffer | `semantic.rs`, `ir.rs`, `lib.rs` (flattener) |
| `nibli-reason` | — | FOL logic buffer -> backward-chaining assert/query | `lib.rs` (single file, all logic) |
| `nibli-pipeline` | — | Glue: chains nibli-kr -> nibli-semantics -> nibli-reason as the ONE WASM component. KR-only since THE DROP: `compile_pipeline` is `nibli_kr::parse_checked` → nibli-semantics → compute-marking; interactive text inputs emit the §12 lint notes as verbose-gated `[Note: …]` guest-stdout echoes (the `[Skolem]` precedent — `NIBLI_QUIET=1` suppresses; the replay path never lints) | `lib.rs` |
| `nibli-host` | — | Native Wasmtime host, REPL, external compute backend TCP client. KR-only since THE DROP (`:load`/`--script` load any file as KR text) | `main.rs` |
| `nibli-engine` | — | Native in-process embedding of the pipeline (used by tests + the store layer; no Wasmtime). `compile_text` is the sole text→AST seam (`nibli_kr::parse_checked` → nibli-semantics → compute-marking); buffer replay is text-free | `lib.rs` |
| `nibli-ui` | — | Standalone Dioxus web UI (browser, port 8080) — nibli-kr/nibli-semantics/nibli-reason compiled in, reasons fully in-browser; KR-only since THE DROP (preloaded examples and the Custom buffers all compile through nibli-kr). Optional client-side BYO-key LLM **Formalize** (Source→KB; "compile" stays reserved for the deterministic step): the agentic self-correcting loop (`nibli-formalize`) → the nibli-kr+nibli-semantics+round-trip gates (`GATE_ORDER` chips) → fresh-context semantic verification → feed errors back → retry, with a self-correction trace. The LLM client is single-sourced on `nibli_formalize::llm`; nibli-ui holds a thin `Settings { llm, max_attempts }` wrapper. Lint notes (§12 L1–L9) ride `nibli_protocol::LineResult::notes` (fresh `Linter` per query run — the stateless-KB model) and render as `[Note: …]` rows in the KB status bar. Native test: the `shipped_examples_compile` guard (`just test-ui`) | `main.rs`, `examples.rs` |
| `nibli-formalize` | translate (name predates THE DROP) | Agentic English→KR formalizer engine consumed by nibli-ui: a multi-turn LLM client (5 providers) with a `Chat` seam + wasm `HttpChat` transport; the local gates (`gates.rs`): `nibli_kr::parse_checked` + nibli-semantics + the **render round-trip gate** (`GateError::RoundTrip`: the candidate's canonical `nibli_kr::render` re-spelling must re-compile to the SAME `LogicBuffer` — nibli-kr's fixpoint contract as a per-candidate drift-catcher; native + wasm); the **grammar+dictionary-grounded system prompt** (`llm/system_prompt.rs`, assembled ONCE via `LazyLock` since the alias map is compile-time): the pest `nibli_kr::GRAMMAR` (in-sync by construction) + a distilled §4/§6/§7 semantics block + the FULL shipped `nibli_lexicon::ALIASES` map as `alias(places…) — predicate` lines + the few-shots — pinned by two guards (the few-shots stay gate-valid; the assembled prompt embeds the grammar + ≥65 alias lines — curated-core, so both hold in fallback builds); the `translate_agentic` loop (line-by-line KB validation, attempt cap, oscillation guard), and the **semantic verification turn** (`verify.rs`, int19h feedback): after the gates pass, a FRESH-context judge reads the overlay-free `nibli_render` back-translation of each KB line; MISMATCH retries as `GateError::Verification` — best-effort advisory. All logic native-tested (incl. the KR Genesis fixture); only the browser transport is wasm-only | `agent.rs`, `gates.rs`, `llm/` |
| `nibli-wasm` | — | wasm-bindgen wrapper exposing the in-browser pipeline (powers the live demo). KR-only since THE DROP; `set_language(&str)` survives as a DEPRECATED NO-OP shim (deployed-site JS compatibility — dies at the rename milestone), and `back_translate` (the Lojban word gloss) likewise. Native tests load the `.nibli` corpora with the vocab-skip discipline (fallback-build safe) | `lib.rs` |
| `nibli` | — | Native debug REPL and `nibli-validate` tooling (KR-only since THE DROP; `--lang`/`NIBLI_LANG` retired — `verify-book` is expected red until the book migrates or pins `v0.1-lojban-final`) | `main.rs`, `src/bin/validate.rs` |
| `nibli-types` | — | Shared flat WIT-compatible types used by every stage: `AstBuffer`, `LogicBuffer`/`LogicNode`, `NibliError`, and the single shared arithmetic evaluator (tolerant equality). The `LogicBuffer` IR is publicly specified in repo-root `LOGIC_IR.md` — keep that spec in sync when the IR or its emitted-shape invariants change | `ast.rs`, `logic.rs`, `error.rs`, `arithmetic.rs` |
| `nibli-lexicon` | — | Compile-time PHF dictionary built by `build.rs` from `dictionary-en.json` (SINGLE parse, in-tree curated fallback — see Dictionary Data below). TWO layers: the FORWARD dict (arity + gloss + place-frame per gismu/lujvo/cmavo — `get_arity`/`get_gloss`/`get_template`/`back_translate`) and, folded in from the former nibli-kr-dictionary crate, the ALIAS map for the nibli KR front-end (English alias → gismu + optional x1↔xN swap + per-place labels — `alias`/`canonical_alias`/`label_index`/`ALIASES`/`GISMU_TO_ALIAS`; `src/curated.rs` pin tables, `src/label.rs` prose-label heuristic, `src/reserved.rs` single-sources the nibli KR keyword list). Alias arity comes from the same in-`build.rs` parse (an in-loop `arity_map`), so alias↔dictionary agreement holds BY CONSTRUCTION; fail-closed build validation (unpinned collisions/keyword-hits/dictionary-shadows fail with the offender list); dual-mode (FULL ~1,338 gismu / curated FALLBACK, byte-identical curated tier) | `build.rs`, `lib.rs`, `src/curated.rs`, `src/label.rs`, `src/reserved.rs`, `src/arity.rs` |
| `nibli-kr` | — | The nibli KR surface-syntax front-end — **the ONLY front-end since THE DROP**; the v0.1 compat profile of `NIBLI_KR.md` is fully implemented, lint catalog included (`TODO.md` carries the rest of the nibli-KR program). Parses the predicate-call language (`goes(me, to: some market).`) into the `AstBuffer` nibli-semantics consumes. Parser tech = **pest**: `src/nibli_kr.pest` is the EXECUTABLE grammar (normative NIBLI_KR §15 — grammar↔parser drift impossible by construction; keyword rules self-guarded and pinned against nibli-lexicon's reserved list by a conformance test). The FULL v0.1 grammar surface + the resolve pass (`src/resolve.rs`: fail-closed name resolution alias→identity-gismu→COMPILE ERROR, place checks, `it`/`slot` position rules); the walker owns the §6/§7 errata as targeted positioned errors. `src/emit.rs` lowers the tree to the `AstBuffer` (aliases→their ENGLISH canonical name with `Converted` swaps, `$vars` preserved verbatim as the logic-variable sigil — no da/de/di pool, no 3-var cap, operators at sentence level; exactly/the blocks fail closed for now); **public `nibli_kr::parse_checked`** is the engine's sole text→AST seam. `src/render.rs` is the inverse (AstBuffer→nibli KR; PARITY LAYER 1: zero wildcard arms + `__ast_parity_guard`, so a new AST variant breaks the build; §10 constructs fail closed BY NAME; rel-clause bodies with an implicit bound entity render with an injected `it` + place-sorted positional args); `tests/acceptance.nibli` (30 stmts, honest-generic §16) is pinned by render∘parse fixpoint tests. `src/lint.rs` is the §12 LINT CATALOG (L1–L9): a data-returning pass (`nibli_kr::lint::Linter`, stateful per session; `reset()` rides KB resets) — non-blocking `[Note: …]` compile notes; `parse_checked` stays note-free, surfaces opt in | `src/nibli_kr.pest`, `src/parser.rs`, `src/resolve.rs`, `src/emit.rs`, `src/render.rs`, `src/lint.rs`, `src/ast.rs` |
| `nibli-protocol` | — | Shared wire-format proof-trace types: nibli-engine (native) serializes, nibli-ui/nibli-wasm (browser) deserialize | `lib.rs` |
| `nibli-store` | — | Persistent redb stores: `NibliStore` (durable fact registry — provenance, retraction tombstones, `:export`) and `RedbFactStore` (the KB's typed write-through mirror, schema-versioned, fail-closed decode) | `lib.rs`, `typed_store.rs` |
| `nibli-render` | — | Shared English rendering of proofs/verdicts (the collapsed `[Why]` narrative; `DomainGloss` overlays are curated-UI-example-only — overlay→dictionary→generic fallback, never CLI/book) | `lib.rs`, `corpus_overlay.rs` |
| `nibli-import` | — | RDF Turtle / OWL import + fact export, wired as the `nibli-import` CLI (`just import <file.ttl>`; `--raw/--export/--query` flags — KR queries reach only dictionary/alias-resolvable names, fail-closed) | `lib.rs`, `rdf.rs`, `owl.rs` |
| `nibli-verify` | — | Differential SOUNDNESS gate (Track A), two oracles over KR-generated programs: exports the nibli-semantics FOL IR (`LogicBuffer`) and checks nibli's verdict against (1) **Vampire** over the Horn/NAF-free fragment (TPTP), and (2) **clingo** over the stratified-NAF + closed-world fragment (ASP — the translator regroups the event decomposition back to function-free surface Datalog). Plus (3) the **KR→nibli-semantics seam gate** (`nibli_kr_seam.rs` + `tests/nibli_kr_seam_gate.rs`, `just verify-nibli-kr-seam`) — the front-end oracle: hand-verified FOL structural goldens + the CONSTRUCT_INVENTORY acceptance sweep + KR-internal metamorphic relations (3 seeded families) + the determinism native leg. Plus (4) the **alias-map differential** (`tests/alias_differential.rs`, `just verify-alias-map`) — the SHIPPED nibli-lexicon alias map's intra-crate invariants (arity self-consistency, round-trips, swap/label integrity, per-alias identity-passthrough behavioral twins; dual-mode). Both maps live in nibli-lexicon since the fold, so arity agreement is by construction. Plus (5) the **Predilex dictionary-arity differential** (`predilex.rs`, `just verify-dict`). Plus (6) the **stratification-rejection** and (7) **retraction metamorphic** differentials (`strat_diff.rs`/`retract_diff.rs`). Not a runtime surface — a CI gate | `lib.rs`, `tptp.rs`, `asp.rs`, `filter.rs`, `oracle.rs`, `oracle_asp.rs`, `seam.rs` (buffer probes), `nibli_kr_battery.rs`, `nibli_kr_seam.rs`, `strat_diff.rs`, `retract_diff.rs`, `tense.rs`, `corpus.rs`, `corpus_naf.rs` |
| `python/` | — | Reference compute backend server (TCP + JSON Lines) | `nibli_backend.py` |

- **WIT interfaces:** `wit/world.wit` defines only the SHIPPING component's boundary: `logic-types` (FOL IR), `error-types`, `compute-backend` (host import), `engine` (session export). Package `nibli:engine@0.2.0` (renamed from `lojban:nibli` at the crate purge; the 0.2.0 bump — the `set-language` ABI break — dates to THE DROP). `cargo component build -p nibli-pipeline` regenerates `nibli-pipeline/src/bindings.rs` (the ONLY crate with WIT bindings; nibli-kr/nibli-semantics/nibli-reason are plain Rust libs using `nibli-types` directly).
- **WIT worlds:** `nibli-pipeline` is the SOLE world — a single WASM component importing `compute-backend`, exporting `nibli-pipeline`, with nibli-kr/nibli-semantics/nibli-reason linked as internal Rust crate deps. (The legacy per-stage `nibli-kr-component`/`nibli-semantics-component`/`nibli-reason-component` worlds + `nibli-kr`/`nibli-semantics`/`nibli-reason`/`ast-types` interfaces were removed — they were never built and misled contributors into thinking a per-component architecture existed.)
- **Rust structs:** `NibliPipeline` (the WASM component) is the only WIT-binding struct.
- **Boundary data:** Flat index-based arrays (`LogicBuffer` for `:debug`/proof output, `LogicalTerm` args) with `u32` indices cross the SINGLE host↔nibli-pipeline WASM boundary — no heap pointers. The internal nibli-kr→nibli-semantics→nibli-reason stages are Rust function calls (no WASM boundary), using `nibli-types` flat buffers directly.
- **Compute dispatch:** nibli-reason uses injectable function pointers (`nibli_reason::KnowledgeBase::set_compute_dispatch`) instead of cfg-gated WIT imports. Lasna registers host-bridge functions at Session creation; native (nibli-engine) and in-browser (nibli-ui/nibli-wasm) modes leave dispatch unregistered — built-in arithmetic (product/sum/quotient) still resolves locally, external predicates (exponential/logarithm) return an error.

## Canonical Runtime Surfaces

Use these assumptions when selecting entrypoints:

- `nibli-host` is the canonical local/operator runtime for the theorem prover. It is the main single-node REPL and the default way to exercise the WASM-hosted pipeline. KR-only since THE DROP (the book capture harness must pin the `v0.1-lojban-final` tag until the book migrates).
  - **Strict mode:** `NIBLI_STRICT=1` (or `:strict on|off` at runtime) makes arity mismatches and integrity-constraint violations REJECT the offending fact and fail the assertion atomically, instead of the default permissive warn-and-insert (GUARANTEES §Predicate Validation / §Integrity Constraints). Plumbing pinned by the `smoke-host-strict` gate (in `ci-wasm`); rejection behavior pinned at the nibli-reason level.
  - **Quiet mode:** `NIBLI_QUIET=1` suppresses the per-assertion bookkeeping echoes — `[Fact #N] …` (host) plus `[Skolem]`/`[Rule]`/`[Constraint]` (guest; nibli-host forwards the flag into the component's WASI env, since `nibli-pipeline::Session::new` reads it to decide `kb.set_verbose`). The verdict, `[Why]`, proof trace, `[Find]`, `[Note: …]`, `[Retract]`, and `:facts` output are unaffected. Opt-in — a live `just run` REPL stays verbose. The book's capture harness (`book/tools/capture_book.py`) sets it by default for clean transcripts; the `smoke-host-quiet` gate (in `ci-wasm`) pins both directions.
- `nibli-ui` is the canonical browser frontend — a standalone Dioxus app with the engine (nibli-kr→nibli-semantics→nibli-reason) compiled into the WASM bundle, KR-only since THE DROP. It reasons fully in-browser; there is no server. The one optional network call is the Source→KB **Formalize** (renamed from Translate 2026-07-12 — the LLM step is interpretive formalization behind gates; NEVER label it "Compile") — the agentic self-correcting loop in `nibli-formalize` (LLM client single-sourced on `nibli_formalize::llm`): a bring-your-own-key request sent directly from the browser to a user-chosen LLM (Anthropic/OpenAI/OpenRouter/Gemini/Custom), with the key held in tab memory only. **Hosting:** the site is rebuilt by the external `dhilipsiva.dev` repo, pinged by `.github/workflows/redeploy-site.yml` on push to `main` — its `build_nibli.sh` must fetch `dictionary-en.json` before building so the deployed bundle ships the FULL alias map (fallback would break the nibli KR examples' long-tail vocabulary; see DEPLOY.md); `just build-ui` produces a local release bundle. See `DEPLOY.md`.
  - **Query model (state, don't ask):** a query is an entailment check of a *proposition* — you state `eats(Adam).` ("Adam eats") and the engine returns `TRUE`/`FALSE`/`UNKNOWN`. There is no interrogative form. The "?" affix shown in the UI query box is a decorative reading cue: not part of `query_text`, never sent to the engine. Keep UI/docs/book copy phrased as "state a claim," never "ask a question."
  - **Example dropdown:** the header offers preloaded book KBs (`nibli-ui/src/examples.rs` — Syllogism/GDPR/Drug-interactions; GDPR+drug corpora `include_str!`-ed from the SAME repo-root `*.nibli` files the engine's regression tests pin; every KB line + preset query additionally pinned by `just test-ui`). Selecting one is read-only (Formalize disabled) and turns the query box into a preset-query dropdown that auto-runs; default **Custom** (`example == None`) is the editable mode. The `example` signal lives in `App` and is rendered *conditionally* — Custom buffers are never overwritten. Keep the `name`/`label` strings byte-stable (book Ch 19 quotes them; no gate catches a desync).
- `nibli-wasm` is the wasm-bindgen wrapper exposing the same in-browser pipeline to JS (powers the live demo at dhilipsiva.dev/nibli).
- `nibli-engine` is an internal native embedding library, not a user-facing runtime surface.
- `nibli` is developer tooling: a native direct-crate REPL and the `nibli-validate` binary used for validation/data-generation workflows. It is not the canonical production runtime.

## Code Conventions

- Semantic-compiler tests use `compile_one(predicates, arguments, proposition)` helper returning `(LogicalForm, SemanticCompiler)`
- `resolve(&compiler, &spur)` helper to get string from interner in tests
- The `Connective` enum (`And`/`Or`/`Iff`/`Whether`) is used only at the sentence level (`SentenceConnective::Afterthought`) — the argument/predicate connective variants were removed (dead capacity no emitter produced)
- `via` modals carry the target predicate directly (`ModalTag::Custom`) — there is no fixed modal-tag table
- **Test discipline — flat vs surface (nibli-reason):** nibli-reason's flat `make_*` test helpers hand-build bare `LogicBuffer`s and skip nibli-semantics's event decomposition + `transform_compute_nodes`, so they match the shipped pipeline on *verdicts* but NOT on shape-dependent behavior (`cwa_false`/`naf_dependent` flags, the `ComputeCheck` step, witness/Skolem shape). For anything shape-dependent, build the buffer the real way via `compile_surface("<kr text>")` (a nibli-reason test helper = `nibli_kr::parse_checked` → `nibli_semantics::compile_from_ast` → `transform_compute_nodes`), or use the `make_decomposed_*` helpers, or write a `nibli-engine` integration test — never assert those on a bare flat buffer. `nibli-reason/src/tests.rs`'s `mod flat_vs_surface` is a metamorphic guard that keeps every behavior class' flat verdict == the surface verdict; keep it green. (See the header comment above the flat helpers in `nibli-reason/src/tests.rs`.)

## Codebase Exclusions

When analyzing or searching the codebase:
- **Exclude `docs/` folder** — generated/reference documentation, not source
- **Exclude `**/bindings.rs`** — auto-generated by `cargo component build`, not hand-written
- **`proofs/`** is Lean 4, not Rust — the mechanized soundness proofs (Track B; `proofs/README.md`). Each `.lean` mirrors a Rust component and is kept in lock-step with an exhaustive Rust conformance test. Checked by `just verify-proofs`.

## Known Issues

- `cargo component build` fails on `io-extras` crate — pre-existing, unrelated to our changes. Bindings generate before the failure.
- **rustc ICE in `check_mod_deathness`** — `wasmtime::component::bindgen!` macro triggers compiler panic in library crates (not binary crates like nibli-host). Workaround: `#![allow(dead_code)]` at crate root in nibli-engine. Fixed in rustc 1.94.0 (updated via flake).
## Roadmap

The **soundness-by-proof frontier is complete** (P1–P4 gaps cleared; P5 done): Track A ships two
differential gates — **Vampire** (classical FOL, Horn/NAF-free) and **clingo** (ASP, stratified-NAF
+ closed-world, incl. the GDPR deontic-NAF erasure rule) — and Track B ships **six mechanized Lean 4
proofs** of the soundness-critical core (combiner, stratification criterion, SCC decomposition,
unifier, rule firing, and the capstone *trace ⇒ perfect-model* theorem), each bridged to the engine
by a conformance test (`proofs/README.md`; `just verify-soundness` + `just verify-proofs`). The
**nibli KR v0.1 program is complete** (2026-07-12): the language shipped as the default front-end on
every surface, lint catalog included. THE PIVOT (2026-07-12, second decision round — `TODO.md`
is the tracker): Lojban is DROPPED entirely — **THE DROP landed 2026-07-13** (single surface;
nibli-kr + the agentic Lojban translator live on in the donation repo, github.com/dhilipsiva/fanva;
the last dual-front-end engine is tagged `v0.1-lojban-final`). The nibli KR rename and the total
Lojban naming purge (crates, WIT package, vocabulary — only the word `nibli` survives) have
landed, and — with the predicate-name bullet — the canonical predicate + variable namespace has
flipped from gismu to English, so **proof traces and all user-facing output contain no Lojban**:
content, arithmetic/comparison, `equals` (the du identity), `something` (zo'e), `$var` names, the
abstraction type names, the pronoun constants (`me`/`you`/`this`/`it_a`… — with a fail-closed
guard rejecting a capitalized Name like `Me` that would co-refer with a pronoun), and the L4 lint
(now a converted-alias-only English note, `metabolized_by ↦ cuts⟨x1↔x2⟩`) are all English. The
remaining ceiling is **adoption** — chiefly a reproducible non-expert authoring study (round-trip
fidelity + silent-mistranslation rate), which belongs to the book/UX track.

## Pre-commit Checklist

Before every commit, always:
1. Update `CLAUDE.md` — if required
2. Update `README.md` — if language coverage or reasoning capabilities changed
3. **Never hand-write test counts (or other derivable figures) into docs.** If a figure is needed, derive it at writing time with `just count-tests` — stale hard-coded counts in GUARANTEES.md were an audit finding; prefer floor phrases ("a four-figure suite") that survive growth
4. Then commit all code + doc changes together
