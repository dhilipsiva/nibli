# WIT surface

The component boundary, as declared in
[`wit/world.wit`](https://github.com/dhilipsiva/nibli/blob/main/wit/world.wit)
— package **`nibli:engine@0.12.0`**, world **`nibli-pipeline`**:

```wit
world nibli-pipeline {
    import compute-backend;
    export engine;
    export authorizer;
}
```

One component, one world. The WIT package version is **independent of crate
semver** (a locked decision of record). Only flat, `u32`-indexed data crosses
the boundary — no heap pointers.

## Interfaces

### `error-types`

`variant nibli-error` identifies the pipeline stage that failed:
`syntax(syntax-detail)` (with `message` + 1-based `line`/`column`),
`semantic(string)`, `reasoning(string)`, `backend(tuple<string, string>)`.

### `logic-types`

The IR and verdict types ([Pipeline & IR](pipeline-and-ir.md)):

- `logical-term` (5 cases) and `logic-node` (13 cases) mirror
  `nibli_types::logic` exactly — kebab-case names, identical declaration order
  (the component-model discriminant is positional).
- `logic-buffer { nodes, roots }`.
- `count-node` remains part of the shared formula IR for query/proof input.
  Assertion and replay methods reject it in asserted position, while opaque
  abstraction content remains quoted; the WIT has no persistent
  cardinality-constraint type.
- `query-result`: `true` | `false` | `unknown(unknown-reason)` |
  `resource-exceeded(resource-kind)`, with `unknown-reason` ∈ {`cycle-cut`,
  `incomplete-knowledge`, `naf-dependent`, `backend-unavailable`,
  `non-finite`} and `resource-kind` ∈ {`depth`, `fuel`, `memory`}.
- `witness-origin`: `knowledge-base` | `generated-witness` | `existential-import`;
  `witness-binding { variable, term, origin }`, `fact-id` (u64),
  `fact-summary { id, label, root-count }`.
- `proof-rule` (20 cases) + 16 named-field payload records (WIT variant cases
  hold at most one payload type, so each data-carrying case gets a record —
  the interface self-documents instead of using positional tuples);
  `exists-witness-rule` carries `origin`, while `count-result-rule` carries
  `existential-imported` alongside `expected` and `actual`. `asserted-rule`
  lists every active assertion citation, `derived-rule` lists stable
  assertion-local rule citations, and `presupposed-rule` keeps
  existential-import evidence distinct from user-given facts;
  `proof-step { rule, holds, children }`;
  `proof-trace { steps, root, naf-dependent, cwa-false }` — the NAF/CWA flags
  are computed once in the engine and carried across so consumers never
  recompute them.
- `materialization-report { complete, refused }` — cumulative requested query
  cones since the last KB mutation: completed relations and one-line refusal
  reasons. It may remain empty when an exact positive proof needed no saturation.

### `compute-backend` (the host import)

- `evaluate(relation, args) -> result<bool, nibli-error>`
- `evaluate-batch(requests) -> list<compute-result>` — one boundary crossing
  for N requests; results in input order, one failure never poisons the batch.

The engine calls this for predicates registered for compute dispatch; the host
answers built-in arithmetic locally and forwards the rest over TCP
([WASM, host & compute](wasm-host-compute.md)).

The import transports relation calls; it does not declare guest KR vocabulary
or arity. The exported session resolves text through the committed corpus before
compute marking, and this WIT version has neither a raw-buffer query nor a
vocabulary/schema method. A custom host implementation therefore cannot make an
arbitrary relation name usable through `query-text` merely by accepting it.

Results are query-local. Neither `evaluate` nor `evaluate-batch` creates a KB
fact, fact id, registry row, or replay entry, and a later backend error is
`UNKNOWN (backend-unavailable)` even if the same request succeeded earlier.

This import is also the component's admission boundary. The WIT contract is
transport-neutral and carries relation, arguments, and Boolean/error results—not
peer identity, signatures, request IDs, versions, timestamps/nonces, or policy
receipts. The component trusts an `ok(bool)` from its host. The stock
`nibli-host` implementation forwards over deliberately unauthenticated JSONL/TCP;
a custom host may authenticate or otherwise admit calls before returning, but
its policy metadata is outside the current proof schema.

### `engine` (export) — the `session` resource

| Method | Contract |
|--------|----------|
| `constructor()` | Fresh KB |
| `assert-text(input)` | → `list<(fact-id, logic-buffer)>` — multi-statement input splits into one independent fact per root (a connective stays one compound fact); each pair carries the compiled buffer so a persisting host can replay without recompiling. `CountNode` and executable `ComputeNode` formulas in asserted position fail as query-only before an id is allocated; opaque quoted content remains inert |
| `query-text(input)` | → `query-result`; names and arities must resolve through the committed corpus before compute routing is applied |
| `query-text-with-proof(input)` | → `(query-result, proof-trace)` under the same fail-closed text contract |
| `query-find-text(input)` | → complete witness binding sets under the same fail-closed text contract; any non-definitive candidate leaf returns `nibli-error` instead of partial rows |
| `compile-debug(input)` | Compile-only: enforces corpus vocabulary/arity, but does not assert or check assertion admission; the host renders the buffer |
| `assert-fact(relation, args)` / `assert-fact-with-id(…)` | Ground fact, bypassing text parsing; the `-with-id` form takes a caller-chosen id for restart replay. A relation already registered for compute is rejected as query-only rather than stored as a shadow fact; the reference external names are rejected even when unregistered |
| `assert-buffer-with-id(buffer, label, id)` | **The** recompile-free replay primitive (the legacy `assert-text-with-id` was removed at 0.5.0 with store schema v3). Legacy count or executable-compute assertion rows fail closed rather than regenerating witnesses or premises; the buffer is re-marked against the live compute registry, so an out-of-order replay of a registered name fails closed too |
| `retract-fact(id)` / `list-facts()` / `reset-kb()` | Fallible KB management; `list-facts` remains active-only |
| `list-assertion-records()` / `restore-withdrawn-assertion(id, label)` | Retained active/withdrawn identities; trusted metadata replay reserves withdrawn IDs without decoding old payloads |
| `set-max-chain-depth(u32)` / `max-chain-depth()` | Checked positive reasoning/witness depth, default 10; zero is rejected |
| `register-compute-predicate(name)` | Post-compile routing for an existing corpus spelling or canonical relation; aliases/committed compounds normalize to the canonical IR name. It declares no vocabulary or arity, so an unknown name is refused. Also refused while live stored facts or rules reference the canonical relation (blocking ids in the message; retract first). The reference external names are query-only at assertion ingress regardless |
| `compute-predicates()` | Sorted canonical compiled-relation registry snapshot, built-ins included — the bare `:compute` report's source |
| `set-strict(bool)` | Off = permissive warn-and-insert; on = arity/integrity violations reject atomically |
| `set-existential-import(bool)` / `existential-import-enabled()` | Default OFF = clean-core classical ∃. Explicit ON enables legacy xorlo witnesses, which participate in ∃/∀/find/count/aggregate. The setter returns `result` because it transactionally rebuilds the active KB; the getter reports the effective profile |
| `set-materialization(bool)` / `materialization-report()` | Query-cone materialisation toggle + its fallible cumulative-since-mutation report — added in 0.7.0 because the optimisation is invisible when it fails: without the report, a KB whose `~p(x)` stays slow has no way to learn which requested relation fell out of the materialisable fragment, or why. Purely positive entailment stays lazy unless exact reasoning remains non-definitive; find/count request complete positive cones. A definitive TRUE/FALSE can never flip (the `materialize_diff` gate enforces it); a non-definitive OFF verdict may become definitive under ON — the deliberate completeness gain |

### `authorizer` (export)

The built-in authorization surface (logical auth v0.1), wrapping the same
policy as the native `nibli-auth` crate. Types: `decision { allowed, verdict,
reason, fields }` (`allowed` is true **only** on entailment TRUE) and
`explained { decision, proof-json }`. Session methods: `load-policy`,
`assert-facts`, `retract`, `can`, `can-any` (batch), `allowed-fields`,
`explain`, `policy-version`, `clear-ephemeral`. Two conventions worth knowing:
the protected-resource parameter is named `object` (WIT reserves the keyword
`resource`), and error results are plain `string`, not `nibli-error`.

## Bindings: the types ARE `nibli_types`

`nibli-pipeline` is the only crate with WIT bindings, regenerated by
`cargo component build -p nibli-pipeline` (the `just build-wasm` recipe, which
also `cargo fmt`s the output; `src/bindings.rs` is gitignored — CI regenerates
it on every run).

`[package.metadata.component.bindings.with]` remaps the **eleven** ABI-matching
boundary types onto the canonical `nibli_types` definitions —
`logical-term`, `logic-node`, `logic-buffer`, `query-result`,
`unknown-reason`, `resource-kind`, `witness-origin`, `witness-binding`, `fact-summary`, `assertion-status`, `assertion-record-summary` from
`logic-types`, plus `nibli-error` and `syntax-detail` from `error-types` — so
the guest passes the canonical types straight through instead of maintaining a
mirror-conversion layer.

The one exception is the proof trio: `proof-rule` is named-field in Rust but
wit-bindgen emits only tuple/newtype variants, so it keeps the single
hand-written `convert_proof_rule` bridge in `nibli-pipeline/src/lib.rs`
(`proof-step`/`proof-trace` reference it and stay generated too).

**Version-bump checklist:** the remap keys pin the interface version
(`nibli:engine/logic-types@0.12.0/…`). Any WIT version change must bump **all
thirteen keys** — a missed key silently stops remapping and resurrects the mirror
types.

## Version history

| WIT | Change |
|-----|--------|
| 0.12.0 | Checked depth controls, retained active/withdrawn assertion records, trusted metadata replay, and fallible materialization reports |
| 0.11.0 | Fallible `register-compute-predicate` (refused over live references, ids named) + the `compute-predicates` getter; reference external compute names refused at assertion ingress regardless of registration |
| 0.10.0 | Added stable assertion/rule citations to proof facts and a distinct `presupposed` case; eager rule conclusions and imported witnesses can no longer cross the component boundary as user-given facts |
| 0.9.0 | Added `generated-witness` origin and changed universal proof payloads from bare terms to origin-bearing witness bindings, separating reasoner-minted witnesses from user constants at every public result/proof surface |
| 0.8.0 | Witness origin on find/exists proofs, imported contribution on count proofs, fallible `set-existential-import`, and `existential-import-enabled` |
| 0.7.0 | `set-materialization` + `materialization-report` |
| 0.6.0 | `export authorizer` (wrapping native `nibli-auth`) |
| 0.5.0 | Removed legacy `assert-text-with-id` (store schema v3) |
| 0.4.0 | `set-existential-import` |
| 0.3.0 | Named-field `proof-rule` payload records |
| 0.2.0 | `set-language` (no longer present in the current WIT — the Lojban front-end retired at THE DROP) |

The 2026-08-13 text-contract reconciliation narrowed registration to existing
corpus relations without changing these WIT method shapes or the 0.11.0 package
ABI. The table records when each ABI member was introduced, not every later
semantic clarification.
