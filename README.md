# nibli

**lo na xanri ke logji birti ciste**

ni'o la .nibli. cu logji birti ciste noi se zbasu fi lo ueb.asemblii. (WASI P2) .i la .nibli. cu fanva lo lojbo se cusku fi lo pamoi mekso logji .ije cu logji jalge fi lo se nitcu ke jersi sisku ciste .i ro jalge cu se krinu lo logji — noda se xanri .i noda se jibni

> *nibli* (lojbo): x1 logji nibli lo du'u x2 kei fi lo javni be x3

## ni'o lo pruce

```
lo lojbo cusku ──→ lo valsi cpacu ──→ lo gerna ciste (AST) ──→ lo smuni ciste (FOL IR) ──→ lo logji ciste (jersi sisku)
                        │                   │                         │                            │
                      logos              ke'a jmina               Skolem se cuxna          se nitcu jersi sisku
                    pagbu cpana        gerna tcidu             SkolemFn se birti        fatci vlaste + javni
```

ni'o mu lo ueb.asemblii. pagbu cu se lasna fi lo WIT jupku'a .ije se zbasu fi lo pa jukpa fasnu:

| pagbu | se zukte |
|-------|----------|
| **gerna** | lo lojbo cusku → AST → WIT pagbu kampu |
| **smuni** | lo AST pagbu kampu → FOL logji pagbu kampu |
| **logji** | lo FOL logji pagbu → se nitcu jersi sisku .e se jivna |
| **lasna** | lasna: gerna → smuni → logji |
| **gasnu** | lo samciste Wasmtime .e lo REPL .e lo TCP jikca ciste |

## Canonical runtime surfaces

Treat these as the supported top-level entrypoints:

- `gasnu`: canonical local REPL / operator runtime for the theorem prover. This is the main single-node runtime. Use `just run`, `just run-with-backend`, or `just run-persist`.
- `nibli-server`: canonical API runtime for the Transparency Triad. It serves GraphQL and can optionally join a `tavla` gossip network through `NIBLI_GOSSIP_HUB`. Use `just server` or `just server-gossip`.
- `nibli-ui`: canonical browser frontend. It is a client of `nibli-server`, not a separate reasoning runtime. Use `just ui`.
- `tavla`: canonical gossip and federation runtime. It owns TCP/WebRTC peer transport, sync, and hub-style deployment. Use `just gossip-hub` and the `gossip-*` targets.

Supporting and non-canonical surfaces:

- `nibli-engine`: shared embedding library used by the server, store-backed nodes, and tests. It is not a user-facing CLI/runtime.
- `nibli`: native direct-crate REPL plus `nibli-validate`. Useful for debugging, validation, and dataset tooling, but not the canonical production/runtime path.
- `nibli-agent`: specialized LLM-driven gossip peer that talks to `tavla`. Use it for agent demos and domain peers, not as the base runtime.

## ni'o lo cfari

### se nitcu

- [Nix](https://nixos.org/download.html) (ro tutci — rustc, cargo-component, wac, just, wasmtime — se zbasu fi lo `flake.nix`)

### zbasu je gasnu

```bash
# ko nerkla lo tutci canlu
nix --extra-experimental-features 'nix-command flakes' develop

# ko zbasu ro pagbu .ije lasna .ije cfari lo REPL
just run

# ko troci ro cipra
just test
```

### lo REPL se pilno

```
~/nibli〉lo gerku cu barda
[Fact #1] Asserted.

~/nibli〉? lo gerku cu barda
[Query] TRUE
  Asserted: gerku(sk_0) & barda(sk_0) → TRUE

~/nibli〉ro lo gerku cu danlu
[Fact #2] Asserted.

~/nibli〉la .adam. cu gerku
[Fact #3] Asserted.

~/nibli〉? la .adam. cu danlu
[Query] TRUE
  Derived (gerku → danlu): danlu(adam) → TRUE
    Asserted: gerku(adam) → TRUE

~/nibli〉?? da gerku
[Witnesses] da = adam

~/nibli〉:debug re lo gerku cu barda
[Logic] (Count "_v0" 2 (And (Pred "gerku" ...) (Pred "barda" ...)))

~/nibli〉:assert tenfa 8 2 3
[Fact #4] tenfa(8, 2, 3) asserted.

~/nibli〉:facts
[Facts] 4 active fact(s):
  #1: lo gerku cu barda (1 root(s))
  #2: ro lo gerku cu danlu (1 root(s))
  #3: la .adam. cu gerku (1 root(s))
  #4: :assert tenfa (1 root(s))

~/nibli〉:retract 1
[Retract] Fact #1 retracted. KB rebuilt.

~/nibli〉:load readme.lojban
[Fact #1] la .nibli. cu logji ciste
[Fact #2] la .nibli. cu birti ciste
...
[Load] Done: 82 asserted, 31 skipped, 0 errors

~/nibli〉:reset
[Reset] Knowledge base cleared.
```

### lo Transparency Triad UI

ni'o la .nibli. cu se pilno lo ueb. tcana noi se zbasu fi la Dioxus .ije lo GraphQL jikca:

```bash
# lo pamoi skami canlu: ko cfari lo GraphQL jikca (loopback 127.0.0.1:8081 by default)
just server

# lo remoi skami canlu: ko cfari lo ueb. tcana (port 8080)
just ui
```

ni'o lo ueb. tcana cu se pilno lo stateless KB: ro preti cu ri zbasu lo KB fi lo Lojban tcita .ije cu preti. lo munje se cusku:

```
ro lo gerku cu danlu          # ro da poi gerku cu danlu
ro lo danlu cu citka          # ro da poi danlu cu citka
la .adam. cu gerku            # la .adam. cu gerku

preti: la .adam. cu citka     # → JETNU (TRUE) + krinu tricu (proof tree)
```

ni'o lo UI status tcita cu se ciksi fi lo `GET /readyz` endpoint .i ri na'e troci lo GraphQL query pe'o lo nu cipra lo server ka canci .i lo Network tab cu jarco lo gossip state, cu curmi lo nu jmina lo gossip assertion, .e cu curmi lo nu sidju lo se cinri na mapti kei (resolve contradiction) .i lo `gossipRetract` mutce cu zvati lo GraphQL API ku'i na se pilno sepi'o lo tcana ca'o

### `nibli-server` guardrails

`nibli-server` now defaults to local-only development settings unless you opt into wider exposure:

- default bind: `127.0.0.1:8081`
- default GraphQL playground: enabled only on loopback binds
- default CORS: no permissive wildcard; loopback binds get a small local allowlist (`localhost:3000`, `localhost:4173`, `localhost:8080`, `localhost:8081`, plus `127.0.0.1` equivalents)
- request body limit: `1048576` bytes by default
- gossip event buffer: bounded in memory; default cap `500`

Operational endpoints:

- `GET /healthz` — process liveness
- `GET /readyz` — readiness, including optional gossip-peer requirement
- `GET /metrics` — Prometheus-style counters and gauges
- `POST /graphql` — GraphQL API
- `GET /graphql` — GraphQL playground, only when enabled

Useful environment variables:

- `NIBLI_SERVER_BIND=host:port` — override the bind address
- `NIBLI_SERVER_ENABLE_PLAYGROUND=true|false` — force playground on or off
- `NIBLI_SERVER_CORS_ALLOW_ORIGINS=http://localhost:3000,...` — explicit CORS allowlist
- `NIBLI_SERVER_MAX_REQUEST_BYTES=1048576` — request body cap
- `NIBLI_SERVER_MAX_GOSSIP_EVENTS=500` — in-memory gossip event cap
- `NIBLI_SERVER_REQUIRE_GOSSIP_PEER=true|false` — make readiness fail until at least one gossip peer is connected
- `NIBLI_SERVER_LOG=info,tower_http=info` — tracing filter
- `NIBLI_SERVER_LOG_FORMAT=pretty|json` — log output format
- `NIBLI_GOSSIP_HUB=host:port` — attach the server to a `tavla` peer/hub

For a network-facing deployment, set `NIBLI_SERVER_BIND` explicitly, set a real CORS allowlist, and disable the playground unless you want it exposed.

### lo tavla ke fatri ciste (gossip network)

ni'o la .nibli. cu se pilno lo fatri ke logji ciste noi se pilno lo OR-Set CRDT joi lo vector clock:

```bash
# ko cfari lo tavla nolraitcu (hub) fi lo TCP
just gossip-hub

# ko cfari lo LLM tavla agent (se jikca fi la Claude)
just agent-fitness
just agent-nutrition
just agent-rights
```

ni'o lo ueb. tcana cu se pilno lo Network tcita noi se jarco lo tavla ciste: lo agent jenmi, lo se cusku liste, lo na mapti liste (contradictions), lo nu cusku fi lo gossip network.

## ni'o lo skami tutci

- **bangu:** Rust (stabli)
- **ueb.asemblii.:** WASI Preview 2 Component Model (cargo-component + wac)
- **se gasnu:** Wasmtime
- **logji ciste:** se nitcu jersi sisku (backward-chaining) joi fatci vlaste (fact index)
- **valsi cpacu:** Logos
- **vlaste:** Perfect Hash Function (PHF) noi se zbasu nenri lo fasnu
- **tutci canlu:** Nix flake
- **skami jikca:** TCP + JSON Lines (sampu protokol, ro bangu ka'e pilno)
- **fasnu gasnu:** Just

## ni'o lo lojbo se smuni

- lo gadri ke se smuni: `lo` (fatci da poi), `le` (lo se smuni poi mi jinvi), `la` (cmene → Constant); `ro lo` / `ro le` (ro da poi); `PA lo` / `PA le` / `su'o lo`
- lo sumti stuzi cmavo (`fa`/`fe`/`fi`/`fo`/`fu`), BAI tcita (`ri'a`, `ni'i`, `mu'i`, `ki'u`, `pi'o`, `ba'i`), `fi'o`...`fe'u`
- lo selbri: jicmu, tanru (Neo-Davidsonian nu'i ciste — lo nu fasnu ka'e se pilno fi lo ka cpacu lo drata intersektiv xlali), nunfanva (`se`/`te`/`ve`/`xe`), natfe (`na`), girzu (`ke`...`ke'e`), lujvo (`zei`), `be`...`bei`...`be'o`
- lo poi/noi/voi ke'a pe lo sumti, joi lo ka jmina lo se smuni
- lo sumti jo'u (`.e`/`.a`/`.o`/`.u` + `nai`), lo selbri jo'u (`je`/`ja`/`jo`/`ju`)
- lo bridi jo'u (lidne: `ge`...`gi`, `ga`...`gi`, `ganai`...`gi`; jersi: `.i je`/`ja`/`jo`/`ju` joi `na`/`nai`)
- lo nu'a (`nu`, `du'u`, `ka` joi `ce'u`, `ni`, `si'o`)
- lo tcika (`pu`/`ca`/`ba`) joi lo dunli satci ke tcika javni, lo ei/e'e ke deontic cinmo
- lo na se cusku bridi (zilkai `go'i`), lo go'i selbri
- lo `ma` preti sumti — se fanva fi lo da poi se jivna
- lo lu...li'u se cusku, lo li + PA namcu sumti

## ni'o lo logji ciste

- Skolem nunfanva (zilkai + se nitcu poi se jibni lo `ro` fi la SkolemFn + DepPair)
- ro lo `ro` javni cu se fanva fi lo jersi sisku javni (UniversalRuleRecord)
- se nitcu jersi sisku ciste joi lo fatci vlaste (typed_facts) joi lo javni se sisku
- lo namcu jivna: `zmadu` (>), `mleca` (<), `dunli` (==) fi lo `Num`
- lo skami jikca: `compute-backend` WIT protokol, `ComputeNode` IR klesi
- lo slabu namcu: `pilji` (pi'i), `sumji` (su'i), `dilcu` (fe'i) joi lo skami jikca
- lo TCP jikca: sampu JSON Lines protokol, lazni jikca, ri jikca
- lo skami jalge se jmina: lo jalge cu se jmina fi lo se slabu fatci (se krinu → skami → se krinu pruce)
- lo fatci se jmina: `assert-fact` WIT fasnu + `:assert` REPL fasnu
- lo na monotoni logji: lo fatci se vimcu fi lo fatci liste + ri zbasu; `:retract <id>` .e `:facts` REPL fasnu
- lo se birti se sisku: `query-find` cu se benji ro lo se birti sumti (`??` REPL lidne)
- lo krinu ciste: `query-entailment-with-proof` cu se benji lo krinu tricu (15 krinu klesi) — `?` REPL lidne
- lo krefu nibli krinu: lo krinu tricu cu ri sisku fi lo `ro` javni; `Asserted` ke jicmu fatci cu se jinvi drata lo `Derived` ke se nibli jalge
- lo gerna ri zbasu: lo bridi poi se fliba cu se srera .ije cfari lo jersi bridi; lo se srera cu se cusku lo rajypau linsi stuzi
- lo tcika logji: `Past`/`Present`/`Future` fi lo fatci vlaste; lo tcika javni cu jmina lo tcika fi lo jicmu javni
- lo Neo-Davidsonian nu'i smuni: ro bridi cu se pagbu fi lo nu fasnu klesi + lo se zukte sumti; lo tanru cu te pilno lo nu fasnu ka'e
- lo junri je se jmina: `And(A, B)` se nibli ze'a lo re bridi cu pilno lo simxu `InDomain` sumti (se fanta lo cmalu explosi)
- lo WIT srera klesi: `nibli-error` (`syntax`/`semantic`/`reasoning`/`backend`); lo gerna srera cu se cusku lo linsi stuzi
- lo WASM se banro: lo REPL fasnu se banro; `NIBLI_FUEL` .e `:fuel` REPL fasnu
- lo satci se banro: `NIBLI_RUN_BOUND` (100 zilkai) .e `:saturate` REPL fasnu (WIT API se ponse)
- lo tcana se samtci: `:load <datnyvei>` cu jmina ro bridi fi lo `.lojban` datnyvei; lo `#` lerpoi cu se vimcu

## ni'o lo skami jikca

ni'o la .nibli. cu jikca lo drata skami jikca fi lo TCP joi JSON Lines protokol .i ro pruce (Python, Node.js, Rust, drata) ka'e se pilno

```bash
# lo pamoi skami canlu: ko cfari lo Python jikca
just backend

# lo remoi skami canlu: ko cfari la .nibli. joi lo jikca
just run-with-backend

# lo REPL nenri:
:compute tenfa                      # ko jmina lo tenfa fi lo skami jikca
li bi tenfa li re li ci             # ko cusku: 8 = 2^3
? li bi tenfa li re li ci           # ko preti: JETNU (se skami fi lo Python)
```

ni'o ko se pilno lo `NIBLI_COMPUTE_ADDR=host:port` a lo `:backend host:port` fi lo REPL .i vi lo na jikca lo slabu namcu ciste cu se pilno

## ni'o lo midju platu

ni'o ko viska lo `todo.md` fi lo roldza platu (pagbu 1-5) .e lo se zukte .e lo skami srera liste

## ni'o lo javni se curmi

ni'o ko viska lo `LICENSE` fi lo se cusku
