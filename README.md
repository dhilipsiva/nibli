# Nibli

**A zero-hallucination symbolic reasoning engine.**

Nibli is a deterministic theorem prover compiled to WebAssembly (WASI P2). It compiles Lojban natural language syntax into First-Order Logic and performs inference via demand-driven backward chaining over an indexed fact store. Every conclusion has a formal derivation. No hallucination. No approximation.

> *nibli* (Lojban): x1 logically entails x2 under rules x3

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
| **nibli-engine** | Wasmtime engine wrapper library (shared by server, tests, store) |
| **nibli-server** | GraphQL API server for the Transparency Triad (async-graphql + axum) |
| **nibli-ui** | Dioxus web UI for the Transparency Triad |
| **tavla** | Gossip daemon: federated knowledge propagation over TCP/WebRTC |
| **nibli-agent** | LLM-driven gossip peer that connects to tavla |
| **nibli** | Native debug REPL and `nibli-validate` tooling |

---

## Runtime Surfaces

**Canonical entrypoints:**

- **`gasnu`** — Local REPL and operator runtime for the theorem prover. The main single-node runtime. Use `just run`.
- **`nibli-server`** — GraphQL API for the Transparency Triad stack. Use `just server`.
- **`nibli-ui`** — Browser frontend (Dioxus). Client of nibli-server. Use `just ui`.
- **`tavla`** — Gossip and federation runtime. Owns TCP/WebRTC peer transport, sync, and hub deployment. Use `just gossip-hub`.

**Supporting surfaces:**

- **`nibli-engine`** — Shared embedding library. Not a user-facing runtime.
- **`nibli`** — Native direct-crate REPL and `nibli-validate`. Developer tooling, not the canonical production path.
- **`nibli-agent`** — LLM gossip peer for agent demos and domain peers.

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
[Logic] (Count "_v0" 2 (And (Pred "gerku" ...) (Pred "barda" ...)))

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

Nibli includes a web UI (Dioxus) with a GraphQL backend for the Transparency Triad workflow:

```bash
# Terminal 1: Start the GraphQL server (127.0.0.1:8081)
just server

# Terminal 2: Start the web UI (port 8080)
just ui
```

The UI uses a stateless KB model: every query resets the engine, re-asserts the full Lojban tab as the knowledge base, then runs the query. The query bar is queries only (no assertions). The Lojban tab is the single source of truth.

```
ro lo gerku cu danlu          # Every dog is an animal
ro lo danlu cu citka          # Every animal eats
la .adam. cu gerku            # Adam is a dog

Query: la .adam. cu citka     # -> TRUE + proof tree
```

The UI includes a Network tab showing gossip state: agent cards, envelope list, contradiction panel, and gossip assertion bar.

---

## Gossip Network

Nibli supports federated knowledge propagation via the `tavla` gossip daemon, using OR-Set CRDTs with vector clocks:

```bash
# Start a gossip hub
just gossip-hub

# Start LLM gossip agents (connect via tavla)
just agent-fitness
just agent-nutrition
just agent-rights
```

Envelopes are signed with ed25519 (ephemeral keypair per node). Forged envelopes are rejected before trust evaluation. Signature policy is configurable (`AcceptUnsigned` default, `RequireSigned` for strict mode).

---

## `nibli-server` Configuration

The server defaults to local-only development settings:

- **Bind:** `127.0.0.1:8081`
- **GraphQL playground:** enabled only on loopback
- **CORS:** local allowlist only (no wildcard)
- **Request body limit:** 1 MB
- **Request timeout:** 30s (configurable via `NIBLI_SERVER_REQUEST_TIMEOUT_SECS`)
- **Rate limit:** 50 req/s (configurable via `NIBLI_SERVER_RATE_LIMIT_RPS`)

**Operational endpoints:**

| Endpoint | Purpose |
|----------|---------|
| `GET /healthz` | Process liveness |
| `GET /readyz` | Readiness (includes optional gossip-peer check) |
| `GET /metrics` | Prometheus-style counters and gauges |
| `POST /graphql` | GraphQL API |
| `GET /graphql` | GraphQL playground (when enabled) |

**Environment variables:**

| Variable | Default | Description |
|----------|---------|-------------|
| `NIBLI_SERVER_BIND` | `127.0.0.1:8081` | Bind address |
| `NIBLI_SERVER_ENABLE_PLAYGROUND` | loopback only | Force playground on/off |
| `NIBLI_SERVER_CORS_ALLOW_ORIGINS` | local allowlist | Explicit CORS origins |
| `NIBLI_SERVER_MAX_REQUEST_BYTES` | `1048576` | Request body cap |
| `NIBLI_SERVER_MAX_GOSSIP_EVENTS` | `500` | In-memory gossip event cap |
| `NIBLI_SERVER_REQUIRE_GOSSIP_PEER` | `false` | Fail readiness until a gossip peer connects |
| `NIBLI_SERVER_REQUEST_TIMEOUT_SECS` | `30` | Per-request timeout |
| `NIBLI_SERVER_RATE_LIMIT_RPS` | `50` | Rate limit (requests per second) |
| `NIBLI_SERVER_LOG` | `info,tower_http=info` | Tracing filter |
| `NIBLI_SERVER_LOG_FORMAT` | `pretty` | Log format (`pretty` or `json`) |
| `NIBLI_GOSSIP_HUB` | unset | Attach server to a tavla gossip hub |

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

**External predicates** (via backend): `tenfa` (exponentiation), `dugri` (logarithm), and any custom predicates you add to the backend server.

Configure with `NIBLI_COMPUTE_ADDR=host:port` or `:backend host:port` in the REPL. Connection is lazy (connects on first dispatch) with auto-reconnect.

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
| Web UI | Dioxus |
| API server | async-graphql + axum |
| Gossip | OR-Set CRDT + vector clocks + ed25519 signatures |

---

## Lojban Coverage

The parser (`gerna`) accepts a practical subset of Lojban sufficient for formal encoding of domain rules:

- **Articles (gadri):** `lo` (existential: "something that is..."), `le` (descriptive: "the thing I have in mind"), `la` (name → constant)
- **Quantifiers:** `ro lo` / `ro le` (universal), `PA lo` / `PA le` (numeric), `su'o lo` (at least one)
- **Place tags:** `fa`/`fe`/`fi`/`fo`/`fu` (explicit argument positions)
- **Modal tags:** BAI (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`) and `fi'o`...`fe'u`
- **Selbri (predicates):** root, tanru with Neo-Davidsonian event semantics (resolves the intersective fallacy), conversion (`se`/`te`/`ve`/`xe`), negation (`na`), grouping (`ke`...`ke'e`), compounds (`zei`), argument attachment (`be`...`bei`...`be'o`)
- **Relative clauses:** `poi`/`noi`/`voi` with `ke'a` bound variable and clause stacking
- **Connectives:** sumti (`.e`/`.a`/`.o`/`.u` + `nai`), selbri (`je`/`ja`/`jo`/`ju`), sentence (forethought: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; afterthought: `.i je`/`ja`/`jo`/`ju` with `na`/`nai`)
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
| `just test-tavla` | Gossip tests |
| `just test-backend` | Python backend tests |
| `just test-all` | Every test suite |
| `just server` | GraphQL API server (port 8081) |
| `just ui` | Transparency Triad web UI (port 8080) |
| `just backend` | Python reference compute backend (port 5555) |
| `just run-with-backend` | Build + run with compute backend |
| `just gossip-hub` | Start gossip hub |
| `just run-persist` | Run with persistent Redb fact store |
| `just fuzz-parse [SECS]` | Fuzz the parser |
| `just fuzz-assert [SECS]` | Fuzz assertion pipeline |
| `just fuzz-query [SECS]` | Fuzz stateful KB queries |
| `just ci` | Full CI suite |
| `just clean` | `cargo clean` |

---

## License

See `LICENSE` for details.
