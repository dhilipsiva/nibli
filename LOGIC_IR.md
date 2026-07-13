# The nibli logic IR (`LogicBuffer`) — a consumable format

This is the specification of nibli's first-order-logic intermediate representation: the
`LogicBuffer` that the KR front-end compiles into and the reasoner consumes. It exists as a
public document because three independent parties asked for the same thing — a shared logic
representation to target from ontology tooling, from other loglang front-ends (Toaq / Xextan /
Eberban), and as a JSON translation-pivot between languages ("Predilog"). **The IR is nibli's
language-agnostic seam**: only the parser (`gerna`) and the word dictionary (`smuni-dictionary`)
are front-end-specific; the IR, the backward-chaining reasoner (`logji`), the Vampire/clingo
differential gates, and the Lean 4 soundness proofs all operate on or below this format.

Everything in this document is derived from source; file pointers are given so a claim can be
re-verified. The single source of truth for the types is
[`nibli-types/src/logic.rs`](nibli-types/src/logic.rs) — one canonical definition shared by every
crate (no per-crate mirrors).

## Where the IR sits

```
KR text ──nibli-kr──▶ AST ──smuni──▶ LogicBuffer ──logji──▶ TRUE / FALSE / UNKNOWN + ProofTrace
                                          │
                                          ├──▶ TPTP (Vampire oracle, nibli-verify/src/tptp.rs)
                                          ├──▶ ASP  (clingo oracle,  nibli-verify/src/asp.rs)
                                          └──▶ English rendering    (nibli-render)
```

A `LogicBuffer` is what you get from compiling text (`compile_debug` on the native engine and
the WIT session), what you assert into the knowledge base, what a query is compiled to (queries
and assertions use the *same* compiler — there is no separate query syntax at this level), and
what the differential oracles translate outward.

## The flat buffer

```rust
pub struct LogicBuffer {
    pub nodes: Vec<LogicNode>,   // all nodes of the formula(s)
    pub roots: Vec<u32>,         // indices of top-level formula nodes
}
```

Exactly two fields; there is **no version field** (see *Versioning*, below). Nodes reference
children by `u32` index into `nodes` — no pointers, which is what lets the same shape cross the
WASM component boundary unchanged. Structural guarantees:

- **Post-order layout.** The flattener pushes children before parents, so every node's child
  indices are strictly less than its own index.
- **DAG, never cyclic — by construction, for front-end-produced buffers.** Shared subtree
  indices are legal (the flattener deliberately shares subtrees when expanding derived
  connectives); the post-order emission makes cycles impossible. Buffers you build yourself get
  **bounds checking** from the reasoner (out-of-range indices return descriptive errors, never
  panics) but no up-front cycle validation — acyclicity is the producer's responsibility.
- **Root granularity is fact granularity.** The front-end emits *one root per statement
  sentence*, but a *single* root for logical connectives (`.ije`/`.ija`/`ge…gi` compile to one
  `AndNode`/`OrNode` root). `LogicBuffer::split_roots()`
  ([logic.rs](nibli-types/src/logic.rs)) splits a multi-root buffer into independently
  assertable/retractable single-root buffers by sharing the whole `nodes` arena and exposing one
  root each — no index remapping. Sibling-root nodes left in the arena are inert: every consumer
  traverses only from `roots`.

## Node inventory (`LogicNode`, 13 variants)

| Variant | Payload | Meaning |
|---|---|---|
| `Predicate` | `(String, Vec<LogicalTerm>)` | Atom: relation name + argument terms |
| `ComputeNode` | `(String, Vec<LogicalTerm>)` | An atom dispatched to a compute backend instead of the fact store (see *Compute*) |
| `AndNode` | `(u32, u32)` | Conjunction (left, right node ids) |
| `OrNode` | `(u32, u32)` | Disjunction (left, right node ids) |
| `NotNode` | `u32` | Negation of the inner node |
| `ExistsNode` | `(String, u32)` | ∃ variable-name over the body node |
| `ForAllNode` | `(String, u32)` | ∀ variable-name over the body node |
| `PastNode` / `PresentNode` / `FutureNode` | `u32` | Tense wrappers (`pu`/`ca`/`ba`) around the inner node |
| `ObligatoryNode` / `PermittedNode` | `u32` | Deontic wrappers (`ei`/`e'e`) around the inner node |
| `CountNode` | `(String, u32, u32)` | "Exactly N": (variable-name, **count**, body node id) |

⚠ `CountNode`'s **middle field is a count, not a node index** — the only place a `u32` in a
payload is not an index into `nodes`.

There are deliberately no `Biconditional`/`Xor` node kinds: the compiler's internal tree IR has
them, but the flattener expands `A ↔ B` to `(¬A ∨ B) ∧ (¬B ∨ A)` and `A ⊕ B` to
`(A ∨ B) ∧ ¬(A ∧ B)` (sharing subtree indices) before the buffer exists
([smuni/src/lib.rs](smuni/src/lib.rs)). Consumers never see them.

### Terms (`LogicalTerm`, 5 variants)

| Variant | Payload | Source |
|---|---|---|
| `Variable` | `String` | Bound/free variables (quantified vars, Skolem vars) |
| `Constant` | `String` | Ground entities (from `la` names) |
| `Description` | `String` | Opaque description reference (from `le`) |
| `Unspecified` | — | `zo'e`, the unspecified-argument placeholder |
| `Number` | `f64` | Numeric literal (`li` + digits) |

All names in the flat IR are owned `String`s — the compiler's internal interner (`lasso::Spur`)
never crosses the flatten boundary.

## What the KR front-end emits (invariants a consumer can rely on)

These shapes are pinned by the compiler-seam conformance gate (hand-verified structural golden
cases in `nibli-verify/tests/differential_gate.rs` + `nibli-verify/src/seam.rs`), so they are
contract, not accident:

- **Neo-Davidsonian event decomposition.** `la .adam. cu gerku` compiles to
  `∃ev. gerku(ev) ∧ gerku_x1(ev, adam) ∧ …` — a unary *type* predicate over a fresh event
  variable, plus one binary *role* predicate `relation_x{i}(ev, arg)` per place (1-indexed),
  left-folded with `And`, existentially closed over the event variable. Unfilled places are
  padded with `Unspecified` up to the dictionary arity, so role predicates for a given relation
  always have consistent arity.
- **Quantifiers.** `lo broda` (xorlo existential) → `Exists(v, And(restrictor, body))` —
  existential import. `ro lo broda` (description universal) →
  `ForAll(v, Or(Not(restrictor), body))` — the material-implication arrow (`ro le` is the same
  shape over an opaque `le_domain_<name>` restrictor). `PA lo broda` (exact count) →
  `CountNode(v, N, And(restrictor, body))`. Prenex `ro da … zo'u BODY` → nested `ForAll`
  wrapping the compiled body **directly** — no restrictor, no arrow — so a `ForAllNode` body is
  the implication shape for description universals but not for prenex ones. Bare `da/de/di`
  close as `Exists` with the literal variable names `"da"/"de"/"di"`.
- **Connectives.** Sentence/selbri/sumti conjunction → `AndNode`, disjunction → `OrNode`,
  `ganai…gi` (conditional) → `Or(Not(left), right)`; biconditional/xor arrive pre-expanded as
  above.
- **Tense and deontics** wrap the whole predication: `PastNode`/`PresentNode`/`FutureNode` and
  `ObligatoryNode`/`PermittedNode` around the compiled form. (`se bilga`/`se curmi` are plain
  predicates, not deontic nodes.)
- **Abstractions are opaque.** `nu`/`du'u`/`ka`/`ni`/`si'o` bodies compile to
  `And(type_pred, And(__abs_<hash>(referent), body))` where `__abs_<hash>` is a content-hashed
  unary marker predicate. The reasoner *matches* the marker (same content unifies) but *skips*
  the body behind it — asserting `mi krici lo du'u P` never makes a bare query `P` true.
  Consumers should key on the `__abs_` prefix; the hash digits are an internal identity with
  only intra-process stability.
- **Not every atom is event-decomposed.** Four flat-atom families exist alongside the
  Neo-Davidsonian groups: `du` (equality) stays a flat two-argument `du(x1, x2)` atom because
  the reasoner's union-find ingestion matches exactly that shape; BAI/`fi'o` **modal tags**
  emit their underlying gismu as a flat n-ary atom conjoined into the matrix (`ri'a X` yields a
  flat `rinka(…)` — so the same relation name can appear both flat and event-decomposed across
  buffers); `ro le`/`PA le` emit a flat unary `le_domain_<name>` restrictor atom; and
  abstraction *type* predicates (`nu`/`duhu`/`ka`/`ni`/`siho`) and `__abs_` markers are flat
  unary. Main-bridi predications are always event-decomposed.
- **Queries compile identically to assertions.** The divergence between asserting and querying
  is entirely post-buffer.

### Compute predicates

The front-end never emits `ComputeNode` — it always emits `Predicate`. The rewrite
`logji::transform_compute_nodes(&mut buf, &preds)` converts `Predicate` → `ComputeNode` (same
payload) for every relation name in the set; `logji::default_compute_predicates()` is
`{pilji, sumji, dilcu}` (×, +, ÷). Every first-party embedder runs this immediately after
compilation. **If you build buffers yourself and want compute dispatch, you must run it too** —
`assert_fact`/`query_entailment` do not call it internally, and a compute relation left as a
plain `Predicate` is treated as an ordinary fact predicate. A backend `true` reply is
auto-asserted as a ground fact — the backend is a trusted axiom source, disclosed in README's
"What zero-hallucination means here".

### What `NotNode` means

Structurally, `NotNode` is plain ¬. The closed-world reading ("FALSE means *not derivable*, not
*proved ¬P*"; negation-as-failure for stratified rules) is a **reasoner** property, not a buffer
property — the verdict side carries it in `ProofTrace.naf_dependent` and `ProofTrace.cwa_false`.
Note also that a universal's implication arrow flattens to the same `NotNode` as a genuine `na`,
so "does this formula use real negation" is not decidable from the buffer alone (nibli-verify's
fragment filter scans source tokens for exactly this reason). Scope details live in
[GUARANTEES.md](GUARANTEES.md).

## Serialization

- **serde/JSON** exists but is **feature-gated**: `nibli-types` derives
  `Serialize`/`Deserialize` for the IR types behind the off-by-default `serde` cargo feature.
  `LogicalTerm` serializes externally-tagged snake_case (`{"constant":"adam"}`,
  `"unspecified"`, `{"number":2.0}`); `LogicNode`/`LogicBuffer` use serde's default external
  tagging with the PascalCase Rust variant names.
- **The proof trace is the battle-tested JSON wire.** `ProofRule` (19 variants, internally
  tagged `#[serde(tag = "type")]` with explicit snake_case tags and named fields),
  `ProofStep { rule, holds, children }`, and
  `ProofTrace { steps, root, naf_dependent, cwa_false }` are the canonical serde types, defined
  in the same file with the note *"the serde attributes are the JSON contract — do not rename a
  field or tag."* `nibli-protocol` re-exports them and owns the helpers `proof_trace_to_json` /
  `proof_trace_from_json`; byte-stability tests pin the encoding.
- **Persistence** uses postcard (binary) over the same serde derives — `nibli-engine` stores
  each asserted root's `LogicBuffer` verbatim; a round-trip test covers every node and term
  variant.
- **WIT** ([wit/world.wit](wit/world.wit), package `lojban:nibli@0.2.0` — the package NAME rename rides the identifier-purge milestone) declares a 1:1 mirror
  of the same types for the WASM component boundary: kebab-case variant names
  (`for-all-node` ↔ `ForAllNode`), identical declaration order (the component-model discriminant
  is positional), tuple-shaped payloads.

## Entry points today

**Produce a buffer** (text → IR): `compile_debug(text)` on the two surfaces that expose it —
native (`nibli_engine::NibliEngine::compile_debug`) and the WIT session
(`compile-debug: func(input: string) -> result<logic-buffer, nibli-error>`) — or directly via
`smuni::compile_from_gerna_ast` (remember `transform_compute_nodes` afterward; the browser
`Session` does not export a compile-only method). Programmatic
single facts: `smuni::compile_injected_fact(relation, args)` — event-decomposes and arity-pads
exactly like surface text (with the flat-`du` exception).

**Consume/reason over a buffer** (the BYO-IR surface, `logji::KnowledgeBase`):
`assert_fact(buffer, label) -> u64`, `query_entailment(buffer)`,
`query_entailment_with_proof(buffer)`, `query_find(buffer)` (witness bindings),
`count_witnesses(buffer)`, `aggregate(buffer, var, op)`, `with_assumptions(&[buffer], f)`
(hypothetical reasoning on a clone), `retract_fact(id)`, plus
`set_compute_dispatch(eval, batch_eval)` for wiring a compute backend.

**The three packaged surfaces**, for integrators who want "does this KB entail that claim"
without touching the IR:

| Surface | Shape | Notes |
|---|---|---|
| `nibli_engine::NibliEngine` (native Rust) | `assert_text -> Vec<u64>`, `query_text_with_proof`, `query_find_text`, `retract_fact`, `compile_debug`, optional redb persistence | Splits roots: a bare-`.i` multi-sentence text becomes N independent facts |
| `nibli-wasm` `Session` (browser JS) | `assert_text -> Vec<u64>`, `query_with_proof -> JSON string`, `list_facts -> JSON`, `retract_fact`, `reset` | The query JSON has keys `status`, `detail`, `naf_dependent`, `cwa_false`, `proof_text`, `why`, `proof` (the full `ProofTrace`) |
| `lasna` WASM component (WIT world `lasna-pipeline`) | `assert-text -> list<(fact-id, logic-buffer)>`, `assert-buffer-with-id` (recompile-free replay), `query-text-with-proof -> (query-result, proof-trace)`, `compile-debug -> logic-buffer`, `assert-fact`, `set-strict`, … | Imports `compute-backend` from the host. Splits roots like the native surfaces; each pair carries the root's compiled buffer so a persisting host (gasnu) stores the FACT itself. `assert-text-with-id` remains as a legacy replay path for pre-buffer text-payload store rows |

Verdicts everywhere are `QueryResult`: `True`, `False`, `Unknown(reason)` (cycle-cut /
incomplete-knowledge / naf-dependent / backend-unavailable / non-finite), or
`ResourceExceeded(kind)` (depth / fuel / memory).

## Writing a new consumer or producer

The two shipped external consumers are the templates, and they also define the de-facto
"mappable" fragments:

- [`nibli-verify/src/tptp.rs`](nibli-verify/src/tptp.rs) (→ Vampire): classical Horn/NAF-free
  fragment — walks `Predicate`/`And`/`Or`/`Not`/`Exists`/`ForAll`, maps 2-arg `du` to TPTP
  native `=`, maps `Unspecified` to a rigid shared constant, renames variables per-formula, and
  **hard-errors on any other node kind** rather than mistranslating.
- [`nibli-verify/src/asp.rs`](nibli-verify/src/asp.rs) (→ clingo): stratified-Datalog+NAF
  fragment — regroups the event decomposition back to surface atoms
  (`∃ev. rel(ev) ∧ rel_x1(ev,a1) ∧ …` collapses to `rel(a1,…,aN)`), accepts `NotNode` (NAF) and
  abstraction markers (as opaque constants), canonicalizes `du` classes.
- [`nibli-verify/src/filter.rs`](nibli-verify/src/filter.rs) documents the fragment criteria
  both rely on.

A **producer** (an alternative front-end) must emit the invariant shapes above — most importantly
the event decomposition with consistent role arities, the ∀-as-implication arrow, and flat
2-arg `du` — and hand the buffer to the `logji` entry points (running
`transform_compute_nodes` if it uses compute relations). The reasoner rejects non-stratifiable
rule sets at assert time (the stratification criterion is Lean-proved and
differentially tested), so a producer gets soundness checking for free.

## Stable vs. internal

**Stable (safe to depend on):**
- The 13 `LogicNode` + 5 `LogicalTerm` variants, payload shapes, and declaration order; the
  two-field `LogicBuffer`; post-order child layout; root-per-sentence granularity and
  `split_roots` semantics.
- The emitted-shape invariants in this document — pinned by the compiler-seam gate's
  hand-verified structural cases (the shape authority). The three-way determinism corpus and
  the Lean conformance tests guard adjacent layers (cross-runtime verdicts and reasoner-side
  artifacts respectively), not emitted shapes.
- The `ProofRule`/`ProofStep`/`ProofTrace` JSON contract, and the `[Syntax Error]` /
  `[Semantic Error]` / `[Reasoning Error]` / `[Backend Error]` prefixes of `NibliError`'s
  `Display` (documented in-source as a formal cross-consumer contract).
- The WIT `logic-types` interface (`lojban:nibli@0.2.0`).

**Internal (may change without notice):**
- Variable naming (`_v0…`, `_ev0…`), Skolem names (`sk_N` — minted by the reasoner, never in a
  compiled buffer), the `__abs_` hash digits, `__neg_ev*` pattern variables (reasoner-internal),
  node ordering beyond the post-order guarantee, and concrete index values.
- The compiler's internal tree IR (`smuni::ir::LogicalForm`, `Spur`-interned, with
  `Biconditional`/`Xor`), `logji`'s stored-fact forms, and the `nibli-store` on-disk mirrors.
- `AggregateOp` and the compute wire structs are Rust-side auxiliaries, not buffer types.

**Versioning:** the buffer itself carries no version field. The WIT package version
(`lojban:nibli@0.2.0`) and the persistence layers' fail-closed schema versions (`nibli-store`)
are the only version markers; adding a `LogicNode`/`LogicalTerm` variant is a breaking change
across every conversion site (an in-source exhaustiveness guard enumerates them). Treat the
format as pre-1.0: pin a commit if you build against it, and expect additive evolution.

## Non-goals (today)

- **No alternative front-end ships in this repo** — this document exists so one *could* be built
  against a specified target.
- **No standalone versioned serialization standard.** The JSON that exists (proof traces,
  feature-gated type serde) is documented above as-is; a "Predilog"-style standalone pivot
  format with its own versioning would be a future item.
- **This is not a semantics document.** What TRUE/FALSE/UNKNOWN *mean* is specified elsewhere
  and governs where the documents overlap: closed-world negation-as-failure, the query-result
  contract, and resource bounds in [GUARANTEES.md](GUARANTEES.md); the closed-domain assumption
  and the trusted compute oracle in README's "What zero-hallucination means here".
