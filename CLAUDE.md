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
| `just run` | Full pipeline: clean WASM -> build components -> fuse with wac -> launch REPL |
| `just check` | Fast type-check all workspace crates (`cargo check --workspace`) |
| `just test` | Run all unit tests (`cargo test --lib -- --nocapture --test-threads=1`) |
| `just test-engine` | Run nibli-engine integration tests (full pipeline: parse → compile → reason) |
| `just test-gerna` | Run gerna (parser) tests only |
| `just test-backend` | Run Python backend tests |
| `just test-tavla` | Run tavla gossip tests |
| `just test-all` | Run every test suite (unit + integration + Python + tavla) |
| `just build-wasm` | Build WASM components + fuse with wac |
| `just build-gasnu` | Build native Wasmtime host gasnu (runner) |
| `just backend` | Start the Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with `NIBLI_COMPUTE_ADDR=127.0.0.1:5555` |
| `just server` | Start GraphQL API server for Transparency Triad (port 8081) |
| `just ui` | Launch Transparency Triad web UI dev server (Dioxus, port 8080) |
| `just clean` | `cargo clean` |

**Important:**
- Always use `cargo test --lib` (NOT `cargo test`) — cdylib linker chokes on WIT export symbols containing `@`
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
| `nibli-engine` | — | Wasmtime engine wrapper library (shared by nibli-server, tavla) | `lib.rs` |
| `nibli-server` | — | GraphQL API server (async-graphql + axum, port 8081) | `main.rs` |
| `nibli-ui` | — | Dioxus web UI for Transparency Triad (browser, port 8080) | `main.rs` |
| `tavla` | talk | Gossip daemon: federated knowledge propagation over TCP/WebRTC | `lib.rs`, `main.rs` |
| `nibli-agent` | — | LLM-driven gossip peer that connects to `tavla` | `main.rs` |
| `nibli` | — | Native debug REPL and `nibli-validate` tooling | `main.rs`, `src/bin/validate.rs` |
| `python/` | — | Reference compute backend server (TCP + JSON Lines) | `nibli_backend.py` |

- **WIT interfaces:** `wit/world.wit` defines `ast-types` (gerna output), `logic-types` (FOL IR), `gerna`, `smuni`, `logji`, `compute-backend`, `lasna`. `wit/gossip.wit` defines gossip protocol types (agent identity, vector clocks, envelopes, trust, transport). `cargo component build` regenerates `src/bindings.rs` in each crate.
- **WIT worlds:** `gerna-component`, `smuni-component`, `logji-component`, `lasna-pipeline`.
- **Rust structs:** `GernaComponent`, `SmuniComponent`, `LogjiComponent`, `LasnaPipeline`.
- **Cross-component data:** Flat index-based arrays (`AstBuffer`, `LogicBuffer`) with `u32` indices — no pointers across WASM boundaries.

## Canonical Runtime Surfaces

Use these assumptions when selecting entrypoints:

- `gasnu` is the canonical local/operator runtime for the theorem prover. It is the main single-node REPL and the default way to exercise the WASM-hosted pipeline.
- `nibli-server` is the canonical API/runtime for the Transparency Triad stack. `nibli-ui` is the canonical browser frontend for that server.
- `tavla` is the canonical gossip transport/runtime. It owns peer transport, sync, and hub-style deployment. The server can attach to a `tavla` peer; it is not the transport owner.
- `nibli-engine` is an internal embedding library, not a user-facing runtime surface.
- `nibli` is developer tooling: a native direct-crate REPL and the `nibli-validate` binary used for validation/data-generation workflows. It is not the canonical production runtime.
- `nibli-agent` is a specialized LLM gossip peer built on the canonical `tavla` network. Treat it as an integration/demo runtime, not the base theorem-prover runtime.

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

See `todo.md` for the full phased roadmap (Phases 1-5), dependency graph, and technical debt tracker.

## Pre-commit Checklist

Before every commit, always:
1. Update `CLAUDE.md` — bump Current Status if a roadmap phase was completed
2. Update `todo.md` — remove completed tasks
3. Update `README.md` — if Lojban coverage or reasoning capabilities changed
4. Then commit all code + doc changes together

## Current Status

Roadmap status: Phase 1, Phase 2, and Phase 3 are complete. `todo.md` no longer contains open roadmap blockers; remaining work is deferred or incremental rather than required for production-readiness alignment.

Completed through all Tier 1 items + full Tier 2 + full Tier 3 + full Tier 4 (production reasoning features: conjunction introduction, fuel limits, error variants, WASI sandboxing, clone-free connectives, arena allocator) + C2 (non-monotonic reasoning / belief revision) + C3 (temporal reasoning) + C4 (event semantics — Neo-Davidsonian) + C5 (description term opacity — `le` vs `lo`) + SkolemFn multi-dependency + event-decomposed universal rule compilation fix (condition-side ∃ as pattern variables) + proof trace memoization (DAG deduplication via ProofRef) + **egglog removal** (replaced egglog equality saturation with demand-driven backward-chaining over indexed fact store).

**Implemented features:**
- Lexer + recursive-descent gerna/parser (gismu, cmavo, cmevla, lujvo)
- Gadri descriptions (lo/le/la), universal (ro lo/ro le), numeric quantifiers (PA lo/le, su'o lo); description selbri supports se-conversion (`lo se krinu`), tanru (`lo sutra gerku`), and na negation (`lo na se curmi`)
- Place tags (fa/fe/fi/fo/fu), BAI modal tags (ri'a, ni'i, mu'i, ki'u, pi'o, ba'i), fi'o...fe'u
- Selbri: root, tanru (Neo-Davidsonian event decomposition — shared event variable resolves intersective fallacy), conversion (se/te/ve/xe — works both at selbri level and within tanru units for tight binding: `menli se ponse`), negation (na), grouping (ke...ke'e), compounds (zei), be...bei...be'o
- Relative clauses (poi/noi/voi) with ke'a, implicit variable injection (ambiguous cases with nested descriptions rejected as error — requires explicit ke'a), clause stacking
- Sumti connectives (.e/.a/.o/.u + nai), selbri connectives (je/ja/jo/ju + na negation on right operand: `je na se fanta`)
- Sentence connectives (forethought: ge...gi, ga...gi, ganai...gi; afterthought: .i je/ja/jo/ju with na/nai)
- Abstractions (nu, du'u, ka with ce'u, ni, si'o)
- Tense (pu/ca/ba), deontic attitudinals (ei/e'e)
- Quoted literals (lu...li'u), number sumti (li + PA)
- Skolemization (independent + dependent under ∀ via SkolemFn)
- All universals compile to backward-chaining rule templates (UniversalRuleRecord) + xorlo presupposition Skolems (restrictor domain guaranteed non-empty)
- SkolemFn constructor for dependent Skolems with multi-dependency support: single dep `(SkolemFn "sk_N" dep)`, multi-dep via `DepPair` nesting `(SkolemFn "sk_N" (DepPair dep0 dep1))` — handles `∀x.∀y. → ∃z.` patterns
- Demand-driven backward-chaining reasoning engine (replaced egglog): indexed fact store (asserted_sexps HashSet) + UniversalRuleRecord templates for backward-chaining; ground material conditionals (Or(Not(P),Q)) auto-registered as zero-variable rules for modus ponens
- Count quantifier (exactly N) for numeric descriptions
- da/de/di existential quantifier closure (bare logic variables now properly wrapped in ∃)
- Host-managed WIT resources: `resource knowledge-base` (logji) + `resource session` (lasna interface)
- KnowledgeBase uses `RefCell` (not `Mutex`) — single-threaded WASI, no global state in logji
- Numerical comparison predicates: zmadu (>), mleca (<), dunli (==) evaluated at query time on Num terms
- Computation dispatch WIT protocol: `compute-backend` interface, `ComputeNode` IR variant, predicate registry in lasna
- Built-in arithmetic evaluation: pilji (multiply), sumji (add), dilcu (divide) with query-time dispatch fallback chain
- Host-provided compute backend with wasmtime linker integration in gasnu
- Generic external compute backend: TCP + JSON Lines client in gasnu, lazy connect, auto-reconnect
- Python reference backend server: pilji, sumji, dilcu, tenfa (exponentiation), dugri (logarithm)
- Compute result auto-ingestion: successful compute dispatch results automatically asserted into KB fact store as ground predicates
- Direct fact assertion: `assert-fact` WIT method on session resource bypasses Lojban parsing for trusted programmatic injection
- REPL `:assert` command: `:assert <relation> <arg1> <arg2> ...` for direct fact injection (numbers auto-detected, else constant)
- Deontic predicates: bilga (obligation), curmi (permission), nitcu (necessity) — standard gismu, work through full pipeline
- Bidirectional material conditional rewrite enables modus ponens/tollens on sentence connectives (ganai...gi)
- Deontic attitudinals: ei (obligation/should), e'e (competence/permission/may) — sentence-level modifiers, transparent wrapper nodes in reasoning
- Lujvo morphological recognition: Logos regex `[a-z']{5}[a-z']*[aeiou]` captures 6+ char brivla; longest-match prevents cmavo prefix theft; PHF dictionary handles arity lookup
- Observative sentences & go'i pro-bridi: gerna accepts sentences without explicit selbri (inserts implicit `go'i`), lasna resolves go'i via `SelbriSnapshot` deep-clone preserving full selbri structure (negation, conversion, tanru, be/bei args, abstractions) across calls
- Metalinguistic `sa` construct-class erasure: proper selma'o classification (28 classes) with backward-walk to matching grammatical class; graceful fallback to single-word erase for unclassified cmavo
- Existential witness extraction: `query-find` WIT method + `find_witnesses` logji function returns all satisfying binding sets for existential variables; `ma` question pro-sumti compiles to existential variable (like da/de/di); REPL `??` prefix for find queries
- Proof trace generation: `check_formula_holds_traced` builds proof tree as it recurses, recording which rule/axiom was applied at each step (15 proof rule variants); `query-entailment-with-proof` / `query-text-with-proof` WIT methods; REPL `?` now always returns the traced query result with indented proof output
- Multi-hop derivation provenance: backward-chaining traces derived facts through universal rule chains (e.g., `gerku(alis) → danlu(alis) → xanlu(alis)`); `UniversalRuleRecord` captures rule templates at compilation time; s-expression pattern matching unifies conclusion templates against queried facts; `Asserted(sexp)` leaf nodes distinguish ground truths from `Derived(label, sexp)` nodes with recursive children; depth-limited (10) with graceful fallback to opaque `PredicateCheck`
- Gerna error recovery: per-sentence recovery (skip to next `.i` on parse failure, continue parsing remaining sentences); `ParseResult` carries both partial results and errors; exact line:column reporting via pointer arithmetic on token `&str` slices; WIT `parse-error` and `parse-result` types; lasna surfaces parse warnings
- WASM fuel limits: Wasmtime fuel-based execution limits prevent unbounded computation; per-command refuel in REPL; configurable via `NIBLI_FUEL` env var or `:fuel` REPL command; friendly `[Limit]` message on fuel exhaustion
- WASM memory limits: Wasmtime `StoreLimits` caps WASM linear memory growth; configurable via `NIBLI_MEMORY_MB` env var (default 512 MB) or `:memory` REPL command; prevents adversarial fact store growth from crashing host
- Run bound configuration (legacy WIT API preserved): `set-run-bound`/`get-run-bound` WIT methods on KB and session resources; `:saturate` REPL command; `NIBLI_RUN_BOUND` env var (default 100); run bound preserved across KB reset/rebuild. Note: with demand-driven backward-chaining, eager saturation is no longer performed; the run bound field is retained for WIT API compatibility
- Conjunction evaluation: `And(A, B)` checked by recursively verifying both conjuncts hold individually via backward-chaining; no eager materialisation of And terms; event Skolem constants (`_ev*`) tracked in separate `known_event_entities` set — visible for witness search and proof tracing but NOT registered in InDomain
- WIT typed error variants: shared `nibli-error` variant (syntax/semantic/reasoning/backend) replaces `Result<_, String>` across all 14 WIT functions; `syntax-detail` record carries line:column; lasna propagates via `?`; gasnu pattern-matches for structured `[Syntax Error]`/`[Semantic Error]`/`[Reasoning Error]`/`[Backend Error]` REPL output
- WASI capability sandboxing: replaced `inherit_stdio()` with `inherit_stdout().inherit_stderr()` — WASM components get only stdout/stderr (for diagnostic prints), no stdin, no filesystem, no network, no env vars
- Clone-free Jo/Ju connectives: added `Biconditional` and `Xor` variants to `LogicalForm` IR — each operand stored once, expansion to And/Or/Not happens during flattening where operands are u32 indices (zero-cost copy); eliminated 6 deep `.clone()` calls across 3 compilation sites
- Arena-allocated gerna AST: bumpalo `Bump` arena replaces all `Box<T>` with `&'arena T` in AST types; 24 heap allocations per parse batched into contiguous arena chunks; arena created per `parse_text()` call, freed in one shot after flattening; enables memory reuse via `Bump::reset()` for batch corpus processing
- Non-monotonic reasoning / belief revision: fact registry with per-assertion FactId (u64), FactRecord stores cloned LogicBuffer + label + retracted flag; retraction marks fact withdrawn then rebuilds fact store from surviving base facts (sound because backward-chaining re-derives on demand); `retract-fact` and `list-facts` WIT methods on both `knowledge-base` and `session` resources; REPL `:retract <id>` and `:facts` commands; idempotent retraction; `rebuilding` flag suppresses diagnostic prints during replay
- Temporal reasoning: `Past`/`Present`/`Future` tense wrappers in s-expression fact store; tense wrappers preserved end-to-end (assertion, query, rule compilation, proof tracing, witness extraction); tense conjunction elimination rules; temporal entity extraction for conjunction introduction; temporal lifting of universal rules (timeless rules automatically fire on tensed premises to derive tensed conclusions via backward-chaining); tense-aware backward-chaining provenance; strict tense discrimination (Past != Future != bare)

- Neo-Davidsonian event semantics: every predication decomposes into event type predicate + Lojban-native role predicates (`klama(e) ∧ klama_x1(e, alis) ∧ klama_x2(e, paris)`); fresh `_ev0`, `_ev1` event variables separate from entity `_v0` variables; tanru share event variable between modifier and head (`sutra gerku` → `∃e. gerku(e) ∧ gerku_x1(e, x) ∧ sutra_x1(e, x)`), resolving the intersective fallacy; `event_decompose()` method on SemanticCompiler produces `∃e. type(e) ∧ role_x1(e, a1) ∧ ...`; all role predicates emitted (including Unspecified/zo'e) for inject_variable compatibility; `inject_variable` and `count_unspecified_predicates` updated to only target `_x1` role predicates; recursive selbri (Converted/Negated/Grouped/Connected/WithArgs) get event decomposition automatically via delegation; abstraction inner forms (`nu`/`du'u`/`ka`/`ni`/`si'o`) event-decomposed naturally through `compile_sentence`

- Description term opacity (`le` vs `lo`): `la` gadri now compiles to `Constant` (like proper names), `le` stays as opaque `Description` rigid designator; `Description` terms tracked via `known_descriptions` in logji engine, enabling conjunction introduction and universal rule participation; `ro le` uses opaque `le_domain_{name}` restrictor (distinct from veridical `gerku` restrictor of `ro lo`); `PA le` similarly uses opaque domain restrictor; all three query functions (entailment check, proof trace, witness extraction) enumerate both `Const` and `Desc` domain members; `QuantifierKind::UniversalLe` and `ExactCountLe` variants preserve gadri distinction through quantifier closure

- Event-decomposed universal rule compilation: condition-side existential variables (from Neo-Davidsonian event decomposition in universal rule antecedents) are compiled as pattern variables in backward-chaining rule templates instead of dependent Skolem functions; `collect_condition_exists` identifies condition-side ∃ variables after `decompose_implication`; `flatten_conjuncts_through_exists` strips Exists wrappers to expose individual predicate atoms for pattern matching; conclusion-side ∃ variables correctly remain as `SkolemFn` for canonical witness creation; xorlo presupposition generates fresh Skolem constants for event variables; backward-chaining provenance enumerates domain member witnesses for unbound event pattern variables in condition templates; enables multi-hop temporal reasoning with event semantics (e.g., `pu gerku(alis) + ∀gerku→danlu + ∀danlu→jmive` derives `pu jmive(alis)`)

- Proof trace memoization: `HashMap<String, u32>` memo table threaded through `trace_predicate_provenance`, `try_backward_chain_traced`, and `check_formula_holds_traced` deduplicates repeated sub-proof derivations; when the same predicate sexp has already been proved, subsequent requests emit a lightweight `ProofRef(sexp)` WIT variant instead of re-expanding the full derivation tree; `proof-ref` variant added to WIT `proof-rule`; gasnu displays `(proved above): <sexp>` for memoized references; memo created fresh per `query_entailment_with_proof_inner` call (no cross-query leakage)
- Proof trace short-circuit AND + step cleanup: `check_formula_holds_traced` AND handler short-circuits on left failure (matching `check_formula_holds` which uses Rust `&&`), preventing exponential blowup when nested existential witness search tries many candidate bindings; ∃ witness loop truncates `steps` vector on failed candidates (checkpoint/rollback) to prevent orphaned step accumulation; reduces worst-case from O(M^D) to O(M×D) where M=domain members, D=∃ nesting depth
- Ground conjunction flattening: `process_assertion()` flattens top-level And trees before asserting — each leaf predicate is asserted individually into the fact store. `collect_ground_leaves()` helper follows And nodes, Skolemized Exists, tense wrappers, and deontic wrappers to extract leaf node IDs with tense context. Ground material conditionals (Or(Not(P), Q) patterns from sentence connectives) are auto-registered as zero-variable UniversalRuleRecord entries for backward-chaining modus ponens.

- REPL `:load <filepath>` command: batch-loads a `.lojban` file into the knowledge base; reads file line by line, skips blank lines and `#` comment lines, asserts each remaining line via `call_assert_text`; per-line refueling prevents fuel exhaustion on large files; reports per-line fact IDs or errors with line numbers; final summary shows asserted/skipped/errors counts; use with `readme.lojban` ontological prelude to bootstrap the KB

**Transparency Triad UI (Steps 1-10 of 10 complete):**
- Step 1: Workspace scaffolding + Dioxus web app (nibli-ui crate, dx serve)
- Step 2: Two-row layout with tabs (Source/Lojban/Back-translation) + query bar + proof panel
- Step 3: GraphQL backend server (nibli-server + nibli-engine, native Rust — no WASM)
- Step 4: Assert/query commands via query bar (unified proof-query only, no separate simple query)
- Step 5: smuni-dictionary crate with PHF glosses + robotic back-translation (10,521 entries)
- Step 6: Ollama integration — English→Lojban translation via server proxy (qwen3-coder:30b default)
- Step 7: Proof trace visualization with human-readable s-expression formatting
- Step 8: Fact management — KB status bar with per-line validation, .lojban file loading, clear button; Ollama temperature fixed to 0.0
- Step 9: UI polish — keyboard shortcuts (Ctrl+L/K/O plus Ctrl+Enter in the Source tab), loading spinners, structured error display, output log improvements (cap/clear/auto-scroll), proof tree connectors, default example syllogism; unified query/proof across entire stack (engine, server, REPL, UI)
- Step 10: Integration tests (16 tests via nibli-engine), Justfile targets (check, test-engine, test-all), README documentation (updated REPL examples, added Transparency Triad UI section)

**UI query semantics:** Every query resets the engine, re-asserts the full Lojban tab text as the KB, then runs the query. The query bar is pure queries only (no assertions). The Lojban tab is the single source of truth.

**Gossip Network Integration (Prompts 7-10):**
- Prompt 7: Training data pipeline — `nibli-validate` binary for batch Lojban validation; `generate_training_data.py` (5 balanced domains, Anthropic API, gerna gate); `training_stats.py` (pass rate analysis, HuggingFace export)
- Prompt 8: Fine-tuning pipeline — `nibli_model.py` (QLoRA on Qwen2.5-7B, train/eval/refine/push commands)
- Prompt 9: LLM gossip agent — `nibli_agent.py` (TCP JSON Lines client for tavla, Claude API / local model, gerna gate with 3 retries, auto-gossip mode, epistemic stances)
- Prompt 10: Network visualization — gossip types in nibli-protocol; nibli-server embeds GossipNode with GraphQL queries (networkSnapshot, agentEnvelopes, envelopeDetail, gossipEvents) and mutations (gossipAssert, gossipRetract, resolveContradiction), plus `/healthz`, `/readyz`, and `/metrics`; nibli-ui Network tab with agent cards (stance distribution bars), envelope list, event feed, contradictions panel, gossip assertion bar with stance selector, and a status badge driven by `/readyz`; auto-refresh every 3 seconds. Retraction is still API-level, not yet a dedicated UI control.

**Server hardening:** nibli-server has request timeouts (default 30s, `NIBLI_SERVER_REQUEST_TIMEOUT_SECS`) and rate limiting (default 50 req/s, `NIBLI_SERVER_RATE_LIMIT_RPS`) on GraphQL endpoints. Health/readiness/metrics endpoints are not rate limited. Rate limit rejections return HTTP 429. Timeouts return HTTP 408.

All crates compile cleanly with rustc 1.94.0. All 30 tavla tests pass.

**Next up:** Deferred items remain outside the closed roadmap: async compute backend follow-up work, richer browser-side transport/UI controls, and book-polish passes tracked in their local notes.
