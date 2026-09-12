# WASM, host & compute

How the engine ships: one WASM component, a native Wasmtime host, an optional
external compute backend, and two browser surfaces that skip WASI entirely.

**Sources:** `nibli-host/src/main.rs`, `nibli-protocol/src/compute_client.rs`,
`python/nibli_backend.py`,
[DEPLOY.md](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md).

## One component, four runtimes

`nibli-pipeline` is the **single** WASM component (WIT world `nibli-pipeline`):
nibli-kr / nibli-semantics / nibli-reason are internal Rust crate dependencies,
not separate components. It imports `compute-backend` from the host and exports
the `engine` + `authorizer` interfaces ([WIT surface](wit-surface.md)).

| Runtime | What runs | Compute dispatch |
|---------|-----------|------------------|
| `nibli-host` (Wasmtime, WASI P2) | loads `nibli.wasm`; the canonical operator REPL | The component registers dispatch at Session creation, bridging to the host's `compute-backend` implementation |
| `nibli-engine` (native, in-process) | the same crates as plain Rust | Opt-in: `enable_compute_backend(addr)` wires the native TCP client; otherwise external dispatch stays unwired |
| `nibli-wasm` / `nibli-ui` (browser, wasm32-unknown-unknown) | the same crates via wasm-bindgen / Dioxus | No external dispatch or registration surface (no TCP in the browser); built-in arithmetic still resolves in-engine |

All four wrap the same `nibli_session::CoreSession`, so they agree by
construction. The dispatch **hook** is per-KB-instance function pointers
(`KnowledgeBase::set_compute_dispatch`) — nibli-reason itself holds no
thread-locals or globals, which is what lets multithreaded embedders register
it at all. The native TCP client those pointers call into does live per-thread
in the embedder (`nibli-engine/src/compute_client.rs`), so a multithreaded
native embedder calls `enable_compute_backend` on each worker thread that
reasons.

## nibli-host mechanics

`just run` builds the component and launches the host
(`NIBLI_WASM_PATH=target/wasm32-wasip2/debug/nibli.wasm` by default).

**Environment variables** (read at startup):

| Var | Default | Effect |
|-----|---------|--------|
| `NIBLI_WASM_PATH` | `target/wasm32-wasip2/debug/nibli.wasm` | Component location |
| `NIBLI_MAX_CHAIN_DEPTH` | `10` | Positive u32 reasoning and generated-witness dependency depth; invalid values reject startup |
| `NIBLI_FUEL` | `50_000_000_000` | Wasmtime fuel budget **per command** (debug WASM is ~6× hungrier than release; `~1.5e11` covers the heaviest demo corpus on debug) |
| `NIBLI_MEMORY_MB` | `512` | Guest memory cap (`trap_on_grow_failure`) |
| `NIBLI_COMPUTE_ADDR` | unset | External backend `host:port`; unset = built-in arithmetic only |
| `NIBLI_DB_PATH` | unset | Optional persistent redb store (migrated + replayed fail-closed at startup) |
| `NIBLI_QUIET` | off | `=1` suppresses the `[Fact #N]` / `[Skolem]` / `[Rule]` bookkeeping echoes (forwarded into the guest's WASI env) |
| `NIBLI_STRICT` | off | `=1` makes arity/integrity violations reject atomically instead of warn-and-insert |
| `NIBLI_EXISTENTIAL_IMPORT` | off | `=1` opts into legacy xorlo witnesses; imported witnesses participate in ∃/∀/find/count/aggregate |
| `NIBLI_MATERIALIZE` | on | `=0` opts out of NAF saturation, sending every NAF check back through backward chaining |

Runtime toggles: `:depth [n]`, `:fuel [n]`, `:memory [mb]`, `:backend [addr]`,
`:strict on|off`, `:existential-import on|off`, `:materialize on|off` (bare
`:materialize` prints the saturation report). Script mode (`--script <file>`
or piped stdin) captures transcripts byte-faithfully.

The host prints the effective existential-import profile at startup and after a
toggle. Changing it is a fallible transactional replay of the active assertion
registry, so existing universals gain or lose imported witnesses immediately;
find/proof/count results carry structured import provenance. The browser UI
labels the same clean-core vs legacy-import profile.

**Resource traps don't brick the session.** Fuel exhaustion
(`wasmtime::Trap::OutOfFuel`) and memory-grow denials are classified and — for
queries — synthesized into a `RESOURCE_EXCEEDED (fuel|memory)` verdict with a
remediation hint. A trap poisons the component instance, so the host keeps a
**journal** of every successful KB mutation and lazily rebuilds a
byte-identical session on the next call (the engine is deterministic:
identical fact ids and Skolem numbering). The journal records successful strict,
import and depth changes in order. A replacement component is published only
after complete replay. Failed replay leaves the session unavailable; raising
`:fuel` or `:memory` lets the next dependent command retry once. An uncertain
durable commit requires reopening the saved database. Depth limits are
engine-level, never a trap.

## The compute backend

An external process the reasoner can consult for computed predicates —
**JSON Lines over TCP**, one object per line:

```json
{"relation": "exponential", "args": [{"type": "number", "value": 8.0}, {"type": "number", "value": 2.0}, {"type": "number", "value": 3.0}]}
{"result": true}
```

Responses are `{"result": true|false}` or `{"error": "..."}`. Argument tags:
`variable`, `constant`, `description`, `unspecified`, `number`.

- **Built-in vs forwarded:** `product` / `sum` / `quotient` with fully
  numeric arguments evaluate locally (the shared
  `nibli_types::eval_arithmetic`); a call whose arguments don't resolve to
  numbers falls through to the backend — which is why the reference server
  implements all three too. Any other corpus relation successfully registered
  via `:compute <name>` forwards. Registration normalizes aliases and committed
  compounds to their canonical compiled relation and is refused while live
  stored facts or rules reference that relation (retract first); bare
  `:compute` reports the canonical registry.
- **Text name boundary:** registration runs after fail-closed KR compilation.
  It does not declare vocabulary or infer arity, so an unknown name is refused
  and remains an unknown text predicate. Native BYO-IR callers can query an
  arbitrary relation by constructing `ComputeNode(name, args)` directly—its
  argument vector supplies the raw shape and no registration is needed. The
  shipping component exposes no raw-buffer query or vocabulary/schema method;
  implementing `compute-backend` or adding a server handler alone cannot add a
  component text predicate.
- **Tolerant equality (disclosed):** arithmetic equality is `isclose` with
  `rel_tol 1e-9, abs_tol 0` — `0.3 = 0.1 + 0.2` is TRUE. The comparison
  predicate `num_equal` is exact `==`. Non-finite operands yield
  `UNKNOWN (non-finite)`; find/count/aggregate then refuse the incomplete
  collection rather than return empty/zero/None.
- **Comparisons are query-only, and that is decided:** `greater` / `less` /
  `num_equal` over operands that could be numbers are refused at assertion
  ingress in facts and in every rule position, so there is no numeric threshold
  rule. On the query side they decide a verdict and also filter witnesses in
  `find` / `count_witnesses` / `aggregate`.
- **Witness enumeration never dispatches:** `find` / `count_witnesses` /
  `aggregate` run the same group recogniser the verdict path does, so anything
  definitively decidable locally — a comparison, or finite built-in arithmetic
  over resolved operands — filters rows. A locally detected non-finite operand
  or overflow is also non-definitive and makes the collection incomplete.
  Anything whose routing would reach the backend is
  refused at the dispatch choke point with a budget of ZERO calls, and the
  enumeration is reported incomplete. Any final `UNKNOWN` or
  `RESOURCE_EXCEEDED` leaf has the same complete-or-error collection behavior.
  `UNKNOWN (backend-unavailable)` there means the engine declined to call out,
  not that the backend failed.
- **Admission policy (explicitly low-assurance):** an external reply is trusted
  evidence for the current `ComputeCheck`. The stock client is plaintext and
  unauthenticated, with no peer identity, confidentiality, integrity or
  request/response ID, protocol/backend/schema version, nonce/timestamp,
  freshness/expiry, replay/revocation check, or admission receipt. Scalar
  replies bind to the next line and batch replies bind by input order. Any
  parseable Boolean is trusted, so a valid forged, replayed, stale, reordered,
  or revoked-peer reply is not detectable. Use the stock path only on loopback
  or a segment whose backend and path the operator accepts as TCB.
- **Custom admission:** native embedders can replace the client with
  `NibliEngine::set_compute_dispatch`; component embedders can implement the WIT
  `compute-backend` import; an operator can also supply an external secured
  transport. The stock `nibli-host` has no admission plug-in—`:backend` and
  `NIBLI_COMPUTE_ADDR` select only an address. A rejected custom call becomes
  `UNKNOWN (backend-unavailable)`, and the current proof schema cannot carry an
  identity, wire transcript, timestamp/nonce, or policy receipt. This is an
  admission hook, not a guest vocabulary/schema hook.
- **Proof-local lifecycle:** built-in and external results are never inserted
  into the typed fact store or assertion registry. They receive no fact id, do
  not appear in `:facts`, cannot be retracted, never change the quantifier
  domain, are not persisted or journaled, and trigger no forward chaining.
  Compute atoms are query-only: executable `ComputeNode`s in assertions or any
  rule position fail before id allocation — as are the reference external names
  (`exponential`/`logarithm`) even when unregistered, so registration order
  cannot strand a stored fact; opaque abstraction bodies remain quoted. Each top-level query recomputes or redispatches. Repeated identical
  external checks may share a transient within-query memo to keep the verdict
  and trace consistent; the memo never survives into another query. Compiled
  KR and raw flat `ComputeNode` buffers follow the same lifecycle, although only
  the native raw-IR path can name a relation outside the text corpus.
- **No backend configured?** A registered external predicate answers
  `UNKNOWN (backend-unavailable)` — an outage is never a derived falsehood
  (pinned by the `smoke-host-backend-unavailable` gate). The result remains
  `UNKNOWN` after an earlier success and despite any matching ordinary fact;
  there is no compute-result outage cache or fact-store fallback.
- **Opaque generated argument?** Internal `Skolem`/`SkolemFn` identity has no
  lossless representation in this string-only protocol. Dispatch therefore
  fails closed as `UNKNOWN (backend-unavailable)` before the host callback runs.
  A user constant whose literal text is `sk_0` is not internal and is forwarded.
- **Client behavior:** lazy connect, reused connection (idle reap after 300 s,
  read timeout 10 s, write 5 s — `NIBLI_BACKEND_*` env overrides), and a batch
  path that pipelines requests and associates replies by order. Scalar dispatch
  drops the connection and retries once after any failed attempt; batch dispatch
  retries the whole batch after a connect/write/read failure. Because a first
  write or partial batch may already have executed, stock backends must be pure
  and idempotent; custom scalar/batch dispatchers must also agree on ordering and
  cardinality.

The reference server is `python/nibli_backend.py` (`just backend`, port 5555):
handlers `product`, `sum`, `quotient`, `exponential`, `logarithm` in a
`HANDLERS` dict. Adding a handler extends what the transport can answer; it does
not add a KR text name. A new arbitrary name additionally requires a native raw
`ComputeNode` query today, or a future explicit vocabulary/schema extension.
`just run-with-backend` wires host + backend together.

## Browser surfaces

No WASI, no component, no server: `nibli-wasm` (wasm-bindgen `Session` for JS;
powers the live demo) and `nibli-ui` (the Dioxus playground) compile the
engine crates straight into the browser bundle. `nibli-wasm` keeps two
deprecated no-op shims (`set_language`, `back_translate`) for deployed-site
compatibility until the site migration lands; the live back-translation is
IR-driven (`back_translate_ir`).

## Ship paths

| Target | What | How |
|--------|------|-----|
| `dhilipsiva.dev/nibli-playground` | nibli-ui bundle | Built by the external `dhilipsiva.dev` site repo; this repo pings it via `redeploy-site.yml` (`repository_dispatch: nibli-updated`) on every push to main — self-skips until the `SITE_DISPATCH_TOKEN` secret exists |
| `dhilipsiva.dev/nibli` | nibli-wasm live demo | Same site repo |
| `dhilipsiva.github.io/nibli/` | this docs site (mirror) | `docs-pages.yml`: `just docs /nibli/` → GitHub Pages, on any `mdbook/**` / `Justfile` / flake push |
| `dhilipsiva.dev/docs/nibli/` | this docs site (primary, pending) | Site repo copies the default `just docs` build (DEPLOY.md §2b) |

`just build-ui` produces the exact shipping bundle locally
(`target/dx/nibli-ui/release/web/public/`) as a pre-merge sanity check — the
production build runs in the site repo. Since the committed corpus, **no build
needs a dictionary fetch** — the full vocabulary is compiled in (the site
repo's leftover fetch step is obsolete and unread; see DEPLOY.md).
