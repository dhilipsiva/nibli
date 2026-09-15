# Changelog

All notable changes to the nibli workspace are documented here.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and the workspace adheres to lockstep [Semantic Versioning](https://semver.org/)
for its published crates (Tier A in
[RELEASING.md](RELEASING.md)'s decision table). The WIT component ABI version
(`nibli:engine@…` in `wit/world.wit`) is **independent** of crate semver.

During 0.x, minor versions may break APIs; every release documents its changes
here first.

## [Unreleased]

### Changed

- **Text compute registration is now explicitly corpus-scoped (decided
  2026-08-13; no Rust signature or WIT ABI change).**
  `register_compute_predicate("name")` / `register-compute-predicate(name)` is
  post-compile routing metadata, not a vocabulary or arity declaration: it now
  refuses an unknown name immediately, while unknown KR text continues to fail
  closed at compilation. Resolvable surface aliases and committed compounds are
  normalized to the canonical relation emitted in logic IR, so the registry,
  live-reference scan, and backend agree on one name; known text over-arity
  still fails before dispatch. Arbitrary compute names remain supported only as
  caller-built raw `ComputeNode` buffers through the native `KnowledgeBase`
  query API (or after a future explicit schema extension). The shipping
  component exports no raw-buffer query, so supplying a custom WIT backend does
  not add component text vocabulary. Native tests pin the fail-closed text
  contract, raw-IR query-only lifecycle, all six single flavors, deterministic
  compilation, assertion/rule refusal, and existing corpus dispatch; the host
  smoke pins unknown registration/query rejection and corpus over-arity across
  the WIT boundary.

- **WIT 0.11.0: registration order can no longer strand a stored compute fact
  (decided 2026-08-09).** An external compute relation asserted BEFORE
  registration stored an ordinary fact no later compute query would ever
  consult — listed by `:facts`, retractable, unreachable the moment any session
  registered the name. Closed with BOTH guards. The reference names
  `exponential`/`logarithm` are query-only at assertion ingress on every
  surface, registered or not (`validate_no_external_compute_names`, ahead of
  the count/compute/comparison guards in preflight, before id allocation — unlike the comparisons
  there is no relational reading to protect: every committed place is numeric,
  and a registered query forwards even symbolic operands to the backend); role
  spellings collapse onto the anchor, opaque quoted content stays assertable,
  and a legacy persisted row carrying a reference name now fails replay
  non-destructively (the count-row precedent). And `register-compute-predicate`
  is now fallible — refused while live stored facts or rules (NAF bodies
  included) reference the corpus relation, the blocking fact ids in the message
  — closing the registration-order hole (`:compute person` over a live `person`
  fact is refused instead of silently orphaning it). Role spellings collapse on BOTH sides of the
  reference scan and role-shaped names are refused outright (`:compute eats_x1`
  would have found no blockers while marking exactly the role conjuncts every
  stored `eats` fact carries); the engine-special relations (identity, the
  numeric comparisons) are refused too, since marking them would silently
  replace built-in query semantics; the scan re-runs on re-registration so a
  raw sub-session ingress violation surfaces instead of returning Ok forever;
  and recompile-free buffer replay (`assert-buffer-with-id`, engine store
  replay) re-marks against the live registry, so an out-of-order replay fails
  closed instead of storing a plain fact for a registered name. The new `compute-predicates` getter reports the
  sorted registry; bare `:compute` prints it, `:compute <name>` prints a
  refusal verbatim and journals only successes. Formalize, nibli-validate, and
  RDF import refuse the same text via the engine's own exported guard. Pinned
  in both orders at the engine level
  (`an_external_compute_name_is_query_only_even_before_registration`,
  `assert_then_register_is_refused_until_the_statements_are_retracted`), by
  `pins/external-compute-boundary.nibli` on the static half, and across the WIT
  boundary by the `smoke-host-compute-query-only` and
  `smoke-host-compute-registration-order` gates. GUARANTEES §Compute Result
  Lifecycle states the contract; §Disclosed Sharp Edges carries the residuals
  and the re-open trigger.

### Fixed

- **Raw witness collections now fail closed on every non-definitive final leaf.**
  `KnowledgeBase::query_find`, `count_witnesses`, and `aggregate` return the existing
  `witness enumeration incomplete` reasoning error whenever any evaluated candidate
  finishes as `Unknown(_)` or `ResourceExceeded(_)`, across either polarity. The old
  reason allowlist treated direct `NafDependent` and `NonFinite` leaves as complete
  absences, allowing `Ok([])`, `Ok(0)`, or `Ok(None)` — and even a partial row from an
  `Unknown OR True` branch. The classifier is now `!QueryResult::is_definitive()`;
  definitive TRUE/FALSE rows, equality canonicalisation, logical deduplication, proof
  behavior, and the separate exact-`CountNode` evaluator are unchanged. Public
  reasoner/session/engine docs now state the complete-or-error contract. No result enum,
  signature, workspace version, or WIT ABI changed.

- **`:reset` no longer forgets compute registrations on a later trap rebuild.**
  nibli-host's `:reset` cleared the replay journal including its
  `RegisterCompute` entries, while the guest session's registry survives
  `reset-kb` (`CoreSession::reset` touches only the KB) — so a post-reset
  trap-triggered rebuild replayed an empty journal into a fresh session and
  silently dropped every registration, re-opening the registration-order hole
  this release closes. The journal now retains registration entries across
  `:reset`, mirroring the guest — pinned by the `:reset` + fuel-trap tail of
  the `smoke-host-compute-registration-order` gate.

- **Negation no longer launders a search cut past witness enumeration.** `negate_result`
  collapses every non-definitive inner verdict to `Unknown(NafDependent)` — deliberately,
  and pinned by `proofs/Combiner.lean`. Before the partial repair, a leaf that was CUT
  (`CycleCut`/`IncompleteKnowledge`/`BackendUnavailable`) and then negated became
  indistinguishable from one that was merely unprovable, so `find`/`count_witnesses`/
  `aggregate` reported a definitive ZERO for a leaf they never decided. This was not
  limited to a surface `~`: rule firing negates antecedents too, so an ordinary positive
  goal inherited the laundering whenever a rule concluding it had an undecided negated
  antecedent — a silent zero for a query containing no negation at all.
  A monotone `naf_cut_epoch` now records the collapse at the six negation sites, and the
  witness-leaf guard still consults it only after the leaf's final verdict. The generalized
  classifier above now refuses direct `NafDependent` and `NonFinite` leaves too; the epoch
  remains a regression-visible record of collapse sites. Final-leaf gating keeps the
  correctness boundary: a rule attempt the engine abandons cannot make a goal that ends
  TRUE, or definitively FALSE by another route, refuse. `negate_result`, `UnknownReason`,
  the WIT result surface, and the Lean model are unchanged.
- **`find_enumeration` is now scoped to `query_find_inner`'s dynamic extent.** It was set
  on entry and cleared only at the two entailment entries, which two thin wrappers bypass
  — so a latch left set could have disabled the compute backend for a later ordinary
  query. Cleared on the way out instead, error paths included.
- **Witness enumeration now decides EVERY locally-decidable compute group, and never
  dispatches.** The comparison fix below shipped with a scope parameter that declined
  every non-comparison head, on two stated grounds that were both wrong. *Declining* the
  group is what dispatched: `find_witnesses` peels the group's existential itself and
  recurses on the body, so the head reached the flat `ComputeNode` arm carrying only the
  event variable — a one-argument `product(varfarin)` payload no correct backend could
  answer — once per non-Skolem candidate. And the excluded side did not fail closed: on
  an empty or Skolem-free domain the sweep had no candidate to trip
  `resolve_args_for_dispatch`, so `product(10, 2, 5).` returned **zero rows with `Ok`**
  while the verdict computed **TRUE**. Ground `greater(20, 15).` returned one row and
  ground `product(10, 2, 5).` returned none — two halves of one hook disagreeing on a
  query with no user variables. The scope parameter is gone; enumeration runs the same
  recogniser and routing as the verdict path, so `product`/`sum`/`quotient` filter rows,
  and a query-scoped latch refuses external dispatch at
  `dispatch_to_backend`/`dispatch_batch_to_backend` — the single choke point every
  route funnels through — with a stated budget of **zero calls**, on the direct,
  obligation and permission routes alike. `UNKNOWN (backend-unavailable)` under
  enumeration now means the engine declined to call out, not that the backend failed.
  Non-finite operands/results and their negated `NafDependent` wrappers now inherit the
  complete-or-error collection contract above; they no longer return a definitive empty
  collection. Strict numeric projection remains a separate `TODO.md` item.
- **A numeric comparison now filters witnesses, not just verdicts.**
  `try_evaluate_numeric_group` had exactly one caller — the `ExistsNode` arm of the
  entailment evaluator. `find_witnesses` has its own `ExistsNode` arm, which peeled the
  comparison group's `∃ev` and swept domain candidates, so every conjunct degraded to a
  store lookup that finds nothing (a comparison is never stored — assertion ingress
  refuses one). `quantity($da, $de) & greater($de, 15).` therefore answered **TRUE** as a
  boolean and returned **zero rows** from `find` / `count_witnesses` / `aggregate`, with
  no error: a jointly inconsistent pair, and the real reason a dose threshold could not
  be used to select the doses. The find path now consults the same group evaluator under
  a new scope parameter, so one shape recogniser serves both halves. (The scope
  parameter was removed again in the follow-up below, which extends the same fix to
  arithmetic; the reasoning recorded for excluding it was wrong on both counts.)
  Pinned by `verdict_and_find_agree_for_every_comparison`,
  `numeric_threshold_verdict_and_find_agree`, and siblings covering non-finite operands,
  the relational reading, row shape, and the excluded arithmetic case.
- **`nibli-verify`'s fragment filters admitted numeric comparisons.** Comparisons are
  not `ComputeNode`s (only built-in arithmetic is registered), so nothing in
  `buffer_non_classical` or either ASP filter rejected them. Neither oracle has a theory
  of arithmetic — Vampire's path is FOF with numbers as `num_<n>` Herbrand constants,
  and the ASP path renders them the same way — so an admitted comparison would have been
  a false alarm (`Diverge`), not a missed case. Latent only because no generator or
  curated case emits one; closed now, in both the flat and event-decomposed spellings,
  before something walks into it.
- **Formalize's assertion gate had no comparison guard.** It checked exact-count and
  compute nodes and stopped, so LLM-authored text carrying `greater($n, 15)` passed the
  whole gate stack and was refused only by the engine, burning an agent retry that no
  gate had objected to. It now calls the engine's own
  `validate_no_operational_comparisons` (newly public), so the two sides cannot drift,
  and the system prompt states the rule.

### Changed

- **Rule-position numeric comparison: DECIDED, not deferred.** Whether a comparison in a
  rule body should COMPUTE on bound values was evaluated in full and declined. Four
  things settled it, none visible from the surface syntax: `greater` has four places, so
  it is a group-level rewrite of rule compilation (across `typed_conditions` *and*
  `negated_exists_groups`, with index and dependency-edge accounting), not an atom swap;
  the assertion guard cannot be made position-aware where it runs, since a rule arrives
  as a quantified disjunction over a shared DAG with no `ImpliesNode` to split on;
  `materialize::project_rule` does not already refuse the shape (`ComputeCondition`
  fires only on flat conditions, and a decomposed comparison projects as an ordinary
  atom that would be seeded empty and marked complete) — it is unreachable only because
  the ingress guard exists; and **neither differential oracle can judge arithmetic**, so
  the feature would ship unchecked by the two gates built to catch exactly this class.
  The refusal message now names the three honest idioms (query it, assert the
  classification, use the numeral-free ordering relations), `GUARANTEES.md` carries the
  reasoning and the re-open trigger — a differential oracle that can judge arithmetic —
  and `pins/numeric-comparison-boundary.nibli` pins the boundary in both directions.

- **Rule-tuple binding is in place, and saturation is ~3x faster:** `eval_rule`'s
  join cloned the whole binding environment once per candidate tuple per join
  level. On a 2004-line constitution driven through 555 pins, that copy and the
  allocator traffic behind it were 63% of the run against 5% for the join logic;
  the same workload now finishes in 3.57 s rather than 11.58 s. The map is
  extended in place and unwound after each candidate via a trail of the keys the
  bind inserted. `bind_tuple`'s scan is otherwise unchanged — same order, same
  arms, same comparisons — so no verdict, tuple ordering, or work counter moves;
  the 555-pin roster and the `--strata` dump are byte-identical to a pre-refactor
  binary. Checked by a 5000-seed materialisation differential (172,905 battery
  queries, zero divergence), 600 fresh-process runs, and `cargo mutants
  --in-diff` at 14/14 caught. Hashing is now the largest remaining cost;
  slot-indexed bindings would remove it, and the full-relation scan per join
  level is the larger opportunity beyond that.
- **The stock external-compute transport remains explicitly low-assurance:**
  `nibli-host` and `NibliEngine::enable_compute_backend` continue to use plaintext,
  unauthenticated JSON Lines over TCP. The protocol has no peer identity,
  confidentiality, integrity or request binding, version negotiation, freshness,
  replay/expiry/revocation checks, or admission receipt; a parseable Boolean received
  in stream order is trusted as proof-local evidence. This is an accepted deployment
  profile, not a high-assurance guarantee. Native embedders can install policy in
  `set_compute_dispatch`, and component hosts can implement the imported
  `compute-backend` interface; the stock CLI has no authentication toggle, and the
  current proof schema cannot carry policy receipts.
- **Proof facts carry structural source provenance; WIT is
  `nibli:engine@0.10.0`:** the truth store now has a replay-derived support
  sidecar instead of treating set membership as proof of user assertion.
  `Asserted` lists every active fact id/label (so duplicate assertions remain
  separately citable), `Derived` cites stable `{assertion id, rule ordinal}`
  sources and grounded premises even when forward chaining eagerly stored its
  conclusion, and existential-import evidence is a distinct `Presupposed`
  case. Equality-substitution proofs cite a deterministic path of actual
  equality facts rather than a synthetic union-find shortcut. Retraction,
  rebuild, profile toggles, and persistent reopen regenerate the same sources
  from the authoritative assertion registry. This changes the native proof
  JSON and component proof-rule ABI during 0.x; old JSON without citation
  fields still deserializes through serde defaults.
- **Compute results are proof-local, never knowledge-base facts:** built-in and
  external results decide only the current `ComputeCheck`; they are not inserted
  into the typed fact store or assertion registry, receive no id, do not appear
  in fact listings, cannot be retracted, never change the quantifier domain, are
  not persisted or replayed, and trigger no forward chaining. Executable
  compute is now query-only: assertions and rules containing a `ComputeNode`
  fail before id allocation (opaque quoted content remains inert). Each
  top-level query recomputes or redispatches, with identical compiled-KR and
  raw-flat behavior; a transient within-query memo keeps repeated oracle checks
  and their trace consistent but never survives to another query. A backend
  error uniformly returns `UNKNOWN (backend-unavailable)`, even after an
  earlier query succeeded or despite a matching ordinary fact. External
  replies remain trusted evidence, so the backend is still in the TCB for each
  proof step that uses one. Failed existential/count checks retain their
  per-member compute evidence, and `cwa_false` is now derived from the enclosing
  proof structure rather than a global scan for any failed compute step.
- **Exact-count formulas are query-only:** `exactly N` and `no` remain
  compiler/IR/query/proof features, but assertion, assumption, and
  preassigned/replay entry points now reject a `CountNode` in asserted position before
  allocating an id or mutating the KB. The former behavior minted witnesses
  without persisting a cardinality invariant (and `exactly 0` stored no
  prohibition), so it could falsify itself or drift after later mutations.
  Authors now assert ordinary facts and query the current count. Counts inside
  opaque abstraction bodies remain quoted content. Legacy persisted count
  assertions fail replay non-destructively. This is a breaking assertion
  semantics change during 0.x; the grammar, IR, WIT variants, renderer, and
  query-result/proof shapes are unchanged.
- **WIT `nibli:engine@0.9.0` exposes generated-witness provenance:**
  `witness-origin` gains `generated-witness`, so find bindings and existential
  proof steps distinguish opaque reasoner-minted witnesses from user constants
  without interpreting the display-only `sk_N` spelling. Universal proof
  payloads now carry origin-bearing `witness-binding` records too, instead of
  bare terms. These are breaking component, native Rust, and proof-JSON changes
  during 0.x.
- **Internal Skolem identity is structural and source-scoped:** generated
  independent and dependent witnesses are typed terms keyed by assertion id,
  binder ordinal, sort, and origin. A user constant such as `"sk_0"` or
  `"sk_0(adam)"` can no longer alias a generated witness through equality,
  event joins, rule identity, find/count, proof memoization, retraction, or
  rebuild. `sk_N` remains presentation only. Compute dispatch refuses opaque
  generated arguments as `UNKNOWN (backend-unavailable)` instead of leaking
  them into the string-only backend protocol; equal-looking user constants are
  still dispatched normally.
- **Typed fact-store schema is v2:** authoritative v1/unversioned populated
  stores fail closed. The engine's disposable typed mirror is erased and
  restamped atomically, then rebuilt from the authoritative `LogicBuffer`
  registry without decoding legacy rows. Compiler-only pattern/placeholder terms
  are rejected at persistence ingress.
- **Persistent native direct/text assertions now share one source-id space:**
  `assert_fact_direct` is durable when `NibliEngine` is opened with a store, and
  both assertion paths reconcile the live and durable allocators. A reasoning
  rejection physically deletes the row written before evaluation, so a failed
  call cannot resurrect on reopen.
- **`KnowledgeBase::with_store` accepts only an empty custom store:** typed rows
  alone cannot restore rules, domain/equality indexes, source
  provenance, or retraction semantics. Embedders must install an empty mirror and
  replay their authoritative buffers with stable ids via `assert_fact_with_id`.
- **Existential import is now an explicit, coherent legacy profile:** clean-core
  is the default, so a description universal does not manufacture existence and
  `some` is plain ∃. `NIBLI_EXISTENTIAL_IMPORT=1`,
  `:existential-import on`, or the programmatic setter opts into the old xorlo
  witness behavior. An imported witness now participates consistently in ∃, ∀,
  find, exact-count, `count_witnesses`, and aggregate enumeration instead of
  being visible only to boolean reasoning. Profile changes transactionally replay
  the active assertion registry (rollback preserves the old profile on failure),
  so toggles apply immediately to existing rules. The host reports the effective
  profile at startup/toggle and the browser UI labels it.
- **WIT `nibli:engine@0.8.0` exposes witness provenance and effective import
  state:** `witness-binding` and `exists-witness-rule` gain `witness-origin`,
  `count-result-rule` gains `existential-imported`, and
  `set-existential-import` is now fallible because it rebuilds the KB; the new
  `existential-import-enabled` getter reports what the session is actually using.
  The native and wasm-bindgen APIs expose the same origin/profile information.
  This is a breaking component/proof-JSON/API change during 0.x.
- **Ordinary-predicate temporal rules are now explicit and flavor-exact:** bare
  rules no longer get
  an implicit second firing pass for `past`/`now`/`future` queries. Bare means
  unqualified, not rigid or timeless; authors declare the intended mapping on
  each rule literal (for example, `all $x: past dog($x) -> past animal($x).`).
  Bare NAF stays bare, explicit tensed NAF keeps its flavor, flavored rules keep
  ordinary proof labels, and materialisation continues to fall back rather than
  erase wrappers. The Vampire/clingo flavorizer now emits each rule once and
  differentially checks bare taxonomy/causal/NAF non-lifting alongside explicit
  same- and cross-flavor controls; every curated temporal case must reach its
  oracle rather than silently skip.
- **Mixed tense×deontic stacks now fail closed instead of losing a wrapper:** one
  atom may carry one temporal prefix or one deontic prefix, but not both.
  `must past P` and `past must P` are compile errors; AST compilation/rendering
  rejects programmatic dual-field propositions, and raw `LogicBuffer` ingress
  rejects any second flavor wrapper on the same path before facts, rules, NAF,
  queries, finds, proofs, materialisation, or replay can observe it. Separate
  rule literals may still have different flavors. This is a breaking surface
  syntax restriction during 0.x; the individual WIT node variants are unchanged.
  A legacy persisted buffer containing a mixed stack fails replay with a reasoning
  error rather than being rewritten, deleted, or interpreted with one wrapper.

### Fixed

- **Composed opaque projections no longer exhaust high-arity derived-subject
  witnesses:** rule firing now joins event variables left-to-right under bindings,
  choosing the next event from cheap grounded-index selectivity and generating only
  that event's complete candidate set. Ground query terms prioritize matching
  dependent Skolems without removing alternatives, and partially grounded Skolems
  enumerate only their unresolved dependencies. If the ordinary search reaches the
  depth bound inside an exact single-positive antecedent, the engine lazily completes
  only that antecedent's relation cone and consults its exact extension. This preserves
  cumulative query-root caching, opaque abstraction identity, flavor-exact matching,
  derived-only enforcement, and the existing fail-closed trace/find/cycle paths. The
  deterministic regression records the release-bound reduction from 61,098 complete
  event assignments to 94, with a checked ceiling of 128 rather than a wall-time claim.
- **Opaque event queries no longer expand unrelated recursive relations or global
  witness pools:** materialisation is scoped to cumulative query cones instead of
  seeding every eligible relation. NAF-bearing cones remain eager; shallow purely
  positive entailment uses indexed backward chaining and requests saturation only
  after a non-definitive result, while find/count still request complete positive cones.
  Candidate generation now uses mandatory relation anchors, specializes dependent
  Skolems from already-bound sibling arguments, and preserves all six bare,
  temporal, and deontic fact flavors. Quoted abstraction bodies remain opaque;
  binary transitive semantics and deterministic candidate order are unchanged.
- **Sound semantic identity:** rule deduplication now buckets by digest but compares a
  full alpha-canonical identity, including flat/grouped NAF metadata, instead of treating
  one 64-bit hash as equality. Opaque abstractions now emit a versioned
  `__abs_v1_<digest>_<lossless-key>` marker whose tagged, length-delimited key includes
  abstraction kind and the complete alpha-canonical body. Ingress recomputes the digest
  from that key, so the digest is non-semantic; malformed/unknown marker versions and exact
  legacy `__abs_<16hex>` persisted buffers fail closed with an actionable database/re-import
  recovery path rather than silently returning a false verdict against newly compiled queries.
  Programmatic constraints, custom fact stores, and authoritative typed-store rows now share
  the same validation; the engine's disposable typed mirror is erased before decoding and
  rebuilt from the canonical LogicBuffer registry, so an obsolete mirror cannot block recovery.
- **`nibli-formalize`:** the shipped LLM system prompt demonstrated
  `every dog $d: animal($d) & barks($d).` — `barks` is not a corpus name, so
  that statement is a compile error, in a prompt whose own text warns that the
  compiler fails closed on unknown words. Corrected to `runs`. The
  gate-validity guard covered the few-shot examples only; it now also compiles
  every complete statement written in the instruction prose
  (`prose_kr_statements_are_gate_valid`), so this class cannot recur.

## [0.1.0] - 2026-08-03

The first tagged release: the engine as it has shipped on `main` — a
deterministic theorem prover compiled to WebAssembly (WASI P2), with the
**nibli KR** predicate-call language as its sole front-end. **0.x caveat:**
minor versions may break APIs; the embed surface (`nibli-engine`) is not yet
declared stable.

### Added

- **The pipeline**: nibli KR (`nibli-kr`, pest-grammar front-end) →
  First-Order Logic IR (`nibli-semantics`, spec in `LOGIC_IR.md`) →
  demand-driven backward chaining over an indexed fact store
  (`nibli-reason`), shared by every runtime surface through
  `nibli-session::CoreSession`.
- **Runtime surfaces**: the `nibli-pipeline` WASM component
  (`nibli:engine@0.7.0` WIT) under the `nibli-host` Wasmtime REPL; the native
  `nibli-engine` embedding; the browser `nibli-wasm` / `nibli-ui` bundles;
  dev tooling in `nibli` (REPL, validate, import CLI, `nibli-pin`, benches).
- **Guarantees and gates** (`GUARANTEES.md`): differential soundness against
  Vampire and clingo, six mechanized Lean 4 proofs with Rust conformance
  bridges, the KR seam gate, corpus/dictionary differentials, KB-level
  behavioural pins, fuzzing, and a mutation-testing baseline.
- **The committed English corpus** (`nibli-lexicon`): the dictionary as
  validated Rust source — one build mode, no network at build time.
- Persistent store (`nibli-store`, redb schema v3), English rendering
  (`nibli-render`), proof-trace wire format (`nibli-protocol`), RDF/OWL
  import (`nibli-import`), the agentic formalizer (`nibli-formalize`), and
  built-in authorization (`nibli-auth`, unpublished).
- Workspace release packaging (R0): lockstep `[workspace.package]` `0.1.0`
  inherited by every member, `[workspace.dependencies]` (path + version) for
  the internal crates (internal *dev*-dependencies stay path-only on purpose
  — they are stripped at publish and must not constrain the publish order),
  `publish = false` on the non-publishable tier, per-crate descriptions and
  READMEs, this CHANGELOG, and the `just release-check` consistency gate.

[Unreleased]: https://github.com/dhilipsiva/nibli/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/dhilipsiva/nibli/releases/tag/v0.1.0
