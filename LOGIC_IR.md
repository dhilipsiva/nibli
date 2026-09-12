# The nibli logic IR (`LogicBuffer`) — a consumable format

This is the specification of nibli's first-order-logic intermediate representation: the
`LogicBuffer` that the KR front-end compiles into and the reasoner consumes. It exists as a
public document because three independent parties asked for the same thing — a shared logic
representation to target from ontology tooling, from other loglang front-ends (Toaq / Xextan /
Eberban), and as a JSON translation-pivot between languages ("Predilog"). **The IR is nibli's
language-agnostic seam**: only the parser (`nibli-kr`) and the word dictionary (`nibli-lexicon`)
are front-end-specific; the IR, the backward-chaining reasoner (`nibli-reason`), the Vampire/clingo
differential gates, and the Lean 4 soundness proofs all operate on or below this format.

Everything in this document is derived from source; file pointers are given so a claim can be
re-verified. The single source of truth for the types is
[`nibli-types/src/logic.rs`](nibli-types/src/logic.rs) — one canonical definition shared by every
crate (no per-crate mirrors).

## Where the IR sits

```
KR text ──nibli-kr──▶ AST ──nibli-semantics──▶ LogicBuffer ──nibli-reason──▶ TRUE / FALSE / UNKNOWN + ProofTrace
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
  sentence*, but a *single* root for logical connectives (a sentence-level `&`/`|` compiles
  to one `AndNode`/`OrNode` root). `LogicBuffer::split_roots()`
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
| `CountNode` | `(String, u32, u32)` | Query-only "Exactly N": (variable-name, **count**, body node id) |

⚠ `CountNode`'s **middle field is a count, not a node index** — the only place a `u32` in a
payload is not an index into `nodes`.

`CountNode` is a formula/IR shape, not a persistent constraint record. Query
entry points evaluate it against the current closed domain; assertion,
assumption, and preassigned/replay entry points reject any asserted count before
allocating an id or mutating the KB. Opaque abstraction bodies are quoted
content and are not traversed by this assertion check.

There are deliberately no `Biconditional`/`Xor` node kinds: the compiler's internal tree IR has
them, but the flattener expands `A ↔ B` to `(¬A ∨ B) ∧ (¬B ∨ A)` and `A ⊕ B` to
`(A ∨ B) ∧ ¬(A ∧ B)` (sharing subtree indices) before the buffer exists
([nibli-semantics/src/lib.rs](nibli-semantics/src/lib.rs)). Consumers never see them.

### Terms (`LogicalTerm`, 5 variants)

| Variant | Payload | Source |
|---|---|---|
| `Variable` | `String` | `$x`-sigiled logic variables (sigil preserved), the fresh vars minted by `some` / `every` / `exactly N`, `?` witnesses, `it` inside a `where` clause, `slot` inside a `property { }`, plus compiler-minted event/Skolem vars |
| `Constant` | `String` | Capitalized names (`Adam` → `"adam"`), the closed pronoun set (`me`, `you`, `it_a`, …), and quoted string literals |
| `Description` | `String` | The definite determiner `the <predicate>` only — payload is the English corpus predicate name (`the dog` → `Description("dog")`) |
| `Unspecified` | — | The `_` placeholder, an omitted place (arity padding), or a bare `it` outside a relative clause |
| `Number` | `f64` | A numeric literal (`2`, `2.5`); unsigned, and overflow is a parse error |

All names in the flat IR are owned `String`s — the compiler's internal interner (`lasso::Spur`)
never crosses the flatten boundary.

## What the KR front-end emits (invariants a consumer can rely on)

These shapes are pinned by the compiler-seam conformance gate (hand-verified structural golden
cases in `nibli-verify/tests/nibli_kr_seam_gate.rs`, driven by the `nibli_kr_seam` generator
module; the shared buffer probes live in `nibli-verify/src/seam.rs`), so they are
contract, not accident:

- **Neo-Davidsonian event decomposition.** `dog(Adam).` compiles to
  `∃ev. dog(ev) ∧ dog_x1(ev, adam) ∧ …` — a unary *type* predicate over a fresh event
  variable, plus one binary *role* predicate `relation_x{i}(ev, arg)` per place (1-indexed),
  left-folded with `And`, existentially closed over the event variable. Unfilled places are
  padded with `Unspecified` up to the dictionary arity, so role predicates for a given relation
  always have consistent arity.
- **Quantifiers.** `some dog` → `Exists(v, And(restrictor, body))` — plain veridical
  existential quantification. `every dog` (description universal) →
  `ForAll(v, Or(Not(restrictor), body))` — the material-implication arrow (`every the dog` is
  the same shape over an opaque `the_domain_<name>` restrictor). Query-only `exactly N dog` (exact count) →
  `CountNode(v, N, And(restrictor, body))`. Prenex `all $x: BODY` → nested `ForAll`
  wrapping the compiled body **directly** — no restrictor, no arrow — so a `ForAllNode` body is
  the implication shape for description universals but not for prenex ones. Free `$x`
  variables close as `Exists` with the literal `$x` names (the user's spellings are
  preserved; there is no fixed variable pool).
  Existential import is a reasoner profile, not an extra IR node: import is OFF
  by default (clean-core); explicit legacy ON makes an asserted description universal mint a
  witness. That witness participates in every quantifier/enumeration surface. Runtime
  results carry structured provenance (`WitnessOrigin::ExistentialImport`) rather than
  asking consumers to recognize the internal Skolem spelling.
- **Connectives.** Sentence-level conjunction → `AndNode`, disjunction → `OrNode`,
  `->` (implication) → `Or(Not(left), right)`; biconditional/xor arrive pre-expanded as
  above.
- **Tense and deontics** wrap the whole predication: `PastNode`/`PresentNode`/`FutureNode` and
  `ObligatoryNode`/`PermittedNode` around the compiled form. (The converted aliases
  `obligated_by`/`permitted` are plain predicates, not deontic nodes.)
  For stored ordinary-predicate rule templates, the wrapper is part of the
  literal's identity at evaluation time: Bare, Past, Present, and Future match
  only the same flavor. There is no reasoner-global temporal lift hidden outside
  this IR; a same- or
  cross-flavor rule has wrappers on its antecedent/conclusion literals.
  Built-in identity and query-time compute dispatch retain their own semantics.
  One formula path may contain at most one temporal or deontic wrapper. The KR
  parser rejects mixed prefixes in either order, the AST compiler and renderer
  reject a programmatic proposition carrying both fields, and the reasoner
  rejects any manually nested temporal/deontic `LogicNode` wrappers before
  assertion, query/find, proof construction, materialisation, or replay. The WIT
  variants remain individually representable, but their nesting is not admitted
  engine input because the fact/rule store has one flavor slot. The check is
  path-sensitive: separate rule literals may still carry different wrappers.
- **Abstractions are opaque.** `event { }`/`fact { }`/`property { }`/`amount { }`/
  `concept { }` bodies compile to
  `And(type_pred, And(__abs_v1_<digest>_<key>(referent), body))`. `<key>` is the hex encoding
  of a tagged, length-delimited, alpha-canonical `(abstraction kind, body)` structure; it is
  the lossless identity. `<digest>` is a stable FNV-1a prefix for readability/indexing only
  and never decides equality: every assert/query ingress parses the full key and recomputes
  the canonical digest. The reasoner *matches* the complete marker (same content and kind
  unify) but *skips* the body behind it — asserting `believe(me, fact { P })` never makes a
  bare query `P` true. Consumers should key on the `__abs_` prefix and treat the versioned
  payload as internal. Exact legacy hash-only `__abs_<16hex>`, malformed v1, and unknown-version
  buffers are rejected fail-closed because their identity cannot be upgraded safely during replay.
  Exact codec/marker goldens freeze the v1 byte layout; changing it requires a new version.
- **Not every atom is event-decomposed.** Four flat-atom families exist alongside the
  Neo-Davidsonian groups: `equals` (the `=` identity) stays a flat two-argument
  `equals(x1, x2)` atom because the reasoner's union-find ingestion matches exactly that
  shape; `via` **modal tags** emit the tag's English-canonical predicate as a flat n-ary
  atom conjoined into the matrix (so the same relation name can appear both flat and
  event-decomposed across buffers); definite-description universals/counts emit a flat
  unary `the_domain_<name>` restrictor atom; and abstraction *type* predicates
  (`event`/`fact`/`property`/`amount`/`concept`) and `__abs_` markers are flat
  unary. Main-predication claims are always event-decomposed.
- **Queries compile identically to assertions.** The divergence is post-buffer:
  `CountNode` formulas in asserted position are valid queries but fail closed at assertion
  ingress because the store has no durable cardinality-constraint semantics.

### Compute predicates

The front-end never emits `ComputeNode` — it always emits `Predicate`. Fail-closed KR
name and arity resolution happens first; only after semantic compilation does
`nibli_reason::transform_compute_nodes(&mut buf, &preds)` convert `Predicate` →
`ComputeNode` (same payload) for every exact compiled relation name in the set.
`nibli_reason::default_compute_predicates()` is `{product, sum, quotient}` (×, +, ÷ —
the pre-flip gismu names were `pilji`/`sumji`/`dilcu`). Every first-party embedder runs
this post-compile rewrite.

The session registry is routing metadata, not a vocabulary or arity declaration.
`register_compute_predicate` accepts a committed-corpus surface spelling or canonical
relation and normalizes converted aliases and committed compounds to the relation emitted
in IR. An unknown registration is refused and the same name remains a KR compile error.
For an arbitrary compute name, a native BYO-IR caller constructs a `ComputeNode` directly;
its explicit argument vector supplies the raw shape, and no text registration is needed.
Alternatively, a producer that built plain `Predicate` nodes may call
`transform_compute_nodes` with its own exact IR-name set. `assert_fact` and
`query_entailment` never perform that rewrite internally, so a relation left as a plain
`Predicate` retains ordinary fact-store semantics. The shipping WIT component exports no
raw-buffer query or vocabulary/schema method, so implementing its `compute-backend` import
alone cannot make an arbitrary name usable by its text query methods.

A `ComputeNode` result is
proof-local: built-in evaluation or an external reply decides that node in the current
derivation but is never inserted into the typed fact store or assertion registry. It has no
fact id, domain, persistence, replay, retraction, or forward-chaining effect. Executable
`ComputeNode`s are query-only; assertion ingress rejects them in facts and every rule
position before allocating an id, while opaque abstraction bodies remain quoted. The
reference external compute names (`exponential`, `logarithm`) are rejected there by NAME,
registered or not — a plain `Predicate` spelling of either (role forms included) never
stores, and recompile-free buffer replay re-marks against the live compute registry. The
numeric comparisons `greater`/`less`/`num_equal` stay plain `Predicate`s — they are never
in the compute-predicate set — but the reasoner recognises them by name and decides them
arithmetically whenever both operands resolve to numbers, on the verdict path AND during
witness enumeration. That reading is likewise query-only: an atom whose operands could be
numbers is refused at assertion ingress in facts and in every rule position, so a numeric
threshold cannot be a rule guard (GUARANTEES §Disclosed Sharp Edges). An atom whose
operands are non-numeric keeps the ordinary relational reading and is stored. Each
top-level query recomputes or redispatches; a transient within-query memo may stabilize
repeated identical external checks but never survives to the next query. A backend error is
always `Unknown(BackendUnavailable)`, even
after an earlier success or when an ordinary fact has the same tuple. The backend remains a
trusted evidence source for the current proof step, as disclosed in README's "What
zero-hallucination means here". The IR is transport-neutral: the stock host/native
JSONL/TCP client is deliberately unauthenticated, while a custom native dispatcher or
component host may enforce admission before returning a Boolean. No backend identity,
version, timestamp/nonce, or admission receipt is represented in `ComputeNode` or the
current proof schema. Compiled KR and hand-built flat `ComputeNode` buffers share this
query-only lifecycle; they do not share a text-vocabulary admission path.

### What `NotNode` means

Structurally, `NotNode` is plain ¬. The closed-world reading ("FALSE means *not derivable*, not
*proved ¬P*"; negation-as-failure for stratified rules) is a **reasoner** property, not a buffer
property — the verdict side carries it in `ProofTrace.naf_dependent` and `ProofTrace.cwa_false`.
Note also that a universal's implication arrow flattens to the same `NotNode` as a genuine `~`,
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
- **Witness provenance is data, not a naming convention.** `WitnessBinding` carries
  `{ variable, term, origin }`, where `origin` is `KnowledgeBase`,
  `GeneratedWitness`, or `ExistentialImport`. The `ExistsWitness`,
  `ForallVerified`, and `ForallCounterexample` proof payloads carry the same
  origin-bearing binding, and
  `CountResult { expected, actual, existential_imported }` makes an imported share of
  the tally explicit. Internal `sk_N` spellings remain unstable and non-semantic.
- **Persistence** uses postcard (binary) over the same serde derives — `nibli-engine` stores
  each asserted root's `LogicBuffer` verbatim; a round-trip test covers every node and term
  variant. The reasoner's write-through typed-fact mirror has its own fail-closed v2
  schema because generated terms now contain structural Skolem ids. That mirror is not
  authoritative: startup erases and rebuilds it from the `LogicBuffer` registry, which is
  what restores rules, domain/equality indexes, source provenance, and retraction state.
  An older active registry row containing an asserted `CountNode` or executable
  `ComputeNode` now aborts replay with its fact id and remains on disk for
  explicit repair/re-import; it is never silently dropped, reinterpreted as
  witness generation, or executed as a durable premise.
- **WIT** ([wit/world.wit](wit/world.wit), package `nibli:engine@0.12.0`) declares the same types
  for the WASM component boundary: kebab-case variant names (`for-all-node` ↔ `ForAllNode`),
  identical declaration order (the component-model discriminant is positional). The
  ABI-matching types (`logic-node`/`logical-term`/`logic-buffer`/`query-result`/…) are
  `with`-remapped onto the canonical `nibli_types` enums on the guest side, so they are those
  types, not a hand-converted mirror. `proof-rule` is the exception — its data-carrying variants
  carry named-field payload records (`exists-witness-rule { var, term, origin }`, with
  universal payloads using origin-bearing `witness-binding` records). Fact-bearing
  proof cases also cross this boundary with structural provenance: `asserted`
  carries every active `{ id, label }` assertion citation, `derived` carries
  `{ assertion-id, rule-ordinal, assertion-label }` rule citations, and
  `presupposed` is distinct from both. These mirror
  `nibli_types::logic::ProofRule` — and keeps a small `convert_proof_rule` bridge (wit-bindgen
  emits only tuple/newtype variants, never Rust struct-variants).

## Entry points today

**Produce a buffer** (text → IR): `compile_debug(text)` on the two surfaces that expose it —
native (`nibli_engine::NibliEngine::compile_debug`) and the WIT session
(`compile-debug: func(input: string) -> result<logic-buffer, nibli-error>`) — or directly via
`nibli_semantics::compile_from_ast` (remember `transform_compute_nodes` afterward; the browser
`Session` does not export a compile-only method). Every text entry point resolves names and
arities through the committed corpus before compute marking; registration cannot make an
unknown name compile. For programmatic single facts,
prefer `CoreSession::assert_fact_direct` or `NibliEngine::assert_fact_direct`:
they event-decompose and arity-pad like surface text, then apply the live compute
registry so registered compute is rejected as query-only. The lower-level
compiler is `nibli_semantics::compile_injected_fact(relation, args)` (with the
flat-`equals` exception).

**Consume/reason over a buffer** (the BYO-IR surface, `nibli_reason::KnowledgeBase`):
`assert_fact(buffer, label) -> u64`, `query_entailment(buffer)`,
`query_entailment_with_proof(buffer)`, `query_find(buffer)` (witness bindings),
`count_witnesses(buffer)`, `aggregate(buffer, var, op)`, `with_assumptions(&[buffer], f)`
(hypothetical reasoning on a clone), `retract_fact(id)`, plus
`set_compute_dispatch(eval, batch_eval)` for wiring a compute backend. `CountNode`
and executable `ComputeNode` formulas are accepted by the query methods and
rejected by `assert_fact` and `with_assumptions`; opaque abstraction content
remains quoted. An arbitrary compute name is therefore expressible here as an explicit
`ComputeNode` query without registration; the caller owns its argument shape.

**The three packaged surfaces**, for integrators who want "does this KB entail that claim"
without touching the IR:

| Surface | Shape | Notes |
|---|---|---|
| `nibli_engine::NibliEngine` (native Rust) | `assert_text -> Vec<u64>`, `query_text_with_proof`, `query_find_text`, `retract_fact`, `compile_debug`, optional redb persistence | Splits roots: a multi-statement text becomes N independent facts |
| `nibli-wasm` `Session` (browser JS) | `assert_text -> Vec<u64>`, `query_with_proof -> JSON string`, `list_facts -> JSON`, `retract_fact`, `reset` | The query JSON has keys `status`, `detail`, `naf_dependent`, `cwa_false`, `proof_text`, `why`, `proof` (the full `ProofTrace`) |
| `nibli-pipeline` WASM component (WIT world `nibli-pipeline`) | `assert-text -> list<(fact-id, logic-buffer)>`, `assert-buffer-with-id` (recompile-free replay), `query-text-with-proof -> (query-result, proof-trace)`, `compile-debug -> logic-buffer`, `assert-fact`, `set-strict`, … | Imports `compute-backend` from the host, but exports no raw-buffer query or schema method: its compute-capable text queries remain limited to corpus-resolvable registered relations. Splits roots like the native surfaces; each pair carries the root's compiled buffer so a persisting host (nibli-host) stores the FACT itself. (The legacy `assert-text-with-id` text-replay path was removed at `nibli:engine@0.5.0` with store schema v3 — `assert-buffer-with-id` is the one replay primitive) |

Verdicts everywhere are `QueryResult`: `True`, `False`, `Unknown(reason)` (cycle-cut /
incomplete-knowledge / naf-dependent / backend-unavailable / non-finite), or
`ResourceExceeded(kind)` (depth / fuel / memory).

## Writing a new consumer or producer

The two shipped external consumers are the templates, and they also define the de-facto
"mappable" fragments:

- [`nibli-verify/src/tptp.rs`](nibli-verify/src/tptp.rs) (→ Vampire): classical Horn/NAF-free
  fragment — walks `Predicate`/`And`/`Or`/`Not`/`Exists`/`ForAll`, maps 2-arg `equals` to TPTP
  native `=`, maps `Unspecified` to a rigid shared constant, renames variables per-formula, and
  **hard-errors on any other node kind** rather than mistranslating.
- [`nibli-verify/src/asp.rs`](nibli-verify/src/asp.rs) (→ clingo): stratified-Datalog+NAF
  fragment — regroups the event decomposition back to surface atoms
  (`∃ev. rel(ev) ∧ rel_x1(ev,a1) ∧ …` collapses to `rel(a1,…,aN)`), accepts `NotNode` (NAF) and
  abstraction markers (as opaque constants), canonicalizes `equals` classes.
- [`nibli-verify/src/filter.rs`](nibli-verify/src/filter.rs) documents the fragment criteria
  both rely on.

A **producer** (an alternative front-end) must emit the invariant shapes above — most importantly
the event decomposition with consistent role arities, the ∀-as-implication arrow, and flat
2-arg `equals` — and hand the buffer to the `nibli-reason` entry points (running
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
- The WIT `logic-types` interface (`nibli:engine@0.12.0`).

**Internal (may change without notice):**
- Variable naming (`_v0…`, `_ev0…`), Skolem display names (`sk_N` — presentation only,
  minted by the reasoner and never in a compiled buffer), the exact versioned `__abs_`
  payload, `__neg_ev*` pattern variables (reasoner-internal),
  node ordering beyond the post-order guarantee, and concrete index values.
- The compiler's internal tree IR (`nibli_semantics::ir::IrForm`, `Spur`-interned, with
  `Biconditional`/`Xor`), `nibli-reason`'s stored-fact forms, and the `nibli-store` on-disk mirrors.
- `AggregateOp` and the compute wire structs are Rust-side auxiliaries, not buffer types.

**Versioning:** the buffer itself carries no version field. The WIT package version
(`nibli:engine@0.12.0`) and the persistence layers' fail-closed schema versions (`nibli-store`)
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
