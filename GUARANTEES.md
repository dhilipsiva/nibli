# Nibli Engine Guarantees

Formal statement of the reasoning engine's properties, boundaries, and contracts.

## Front-End Languages

**Guarantee:** Nibli has two surface languages compiling to the same FOL IR (`LogicBuffer`), and every guarantee in this document is language-independent — it holds for a claim whichever front-end spelled it.

- **Klaro** (default since 2026-07-12) — the predicate-call surface (`dog(Adam).`, `animal(every dog).`; spec `SURFACE_SYNTAX.md`, v0.1 compat profile). Name resolution is **fail-closed**: a word that is neither a known alias nor a dictionary word is a compile error, never an arity-guessed new predicate.
- **Lojban** (legacy) — the original surface (`la .adam. cu gerku`), selected per surface via `:lojban` / `--lang lojban` / `NIBLI_LANG=lojban`. Coverage in `LOJBAN_COVERAGE.md`; retires at clean-core v2.

The equivalence is CI-enforced, not aspirational: `verify-klaro` sweeps every implemented construct against its Lojban twin and runs a render→reparse translation battery over the corpora (canonicalized-`LogicBuffer` equality); `verify-klaro-twins` pins per-line logical equality between each committed `.klaro` corpus twin and its tested `.lojban` source; `verify-klaro-dict` differentially checks the shipped alias map against the shipped arity dictionary per alias, including a behavioral compile-equality battery. Example syntax elsewhere in this document is written in the Lojban surface where it predates the flip — each such claim holds identically for its Klaro twin spelling.

## Soundness

**Guarantee:** The engine never returns TRUE for a formula that does not follow from the asserted facts and compiled rules, given a correct implementation.

If the engine says TRUE, a formal proof trace exists showing the derivation chain from asserted axioms through named inference rules to the conclusion. Every step is mechanically verifiable.

**Caveat:** The engine is software. A bug in the parser (gerna), semantic compiler (smuni), or reasoning engine (logji) could produce a valid-looking proof of a wrong statement. Such a bug would be deterministic, reproducible, and testable — fundamentally different from stochastic hallucination. The engine is tested by a four-figure suite of unit and integration tests across the full pipeline (derive the current figure with `just count-tests` — this document deliberately states no hard number, which goes stale) and, more load-bearing than any count, by the differential-oracle, mechanized-proof, mutation, and fuzz gates described below.

**Differential soundness gate (Track A):** Beyond unit/integration tests, the reasoner is differentially checked against **two** external solvers, one per fragment, gated in CI (`just verify-soundness`). The `nibli-verify` harness exports the compiled FOL IR (`LogicBuffer`) and asserts nibli's `TRUE`/`FALSE` matches the oracle:

- **Classical fragment — Vampire.** For the cleanly-mappable **Horn / NAF-free fragment**, the IR is translated to TPTP and checked against **Vampire** — `TRUE ⟺ Theorem`, `FALSE ⟺ CounterSatisfiable` — over a curated corpus, a seeded batch of random Horn programs, the auto-extracted mappable slice of the `gdpr`/`ddi` case-study corpora, and a **Predilex taxonomy leg**: real-vocabulary rule programs (direct edges, 2-hop chains, closed-world negative controls) generated from the vendored Predilex hypernym links (`cukta`⇒`rutni`, `bloti`⇒`marce`⇒`rutni`, … — independent, human-curated lexical implications; the master's 208 λ-calculus `definition` formulas are higher-order/arithmetic and stay out of fragment). On that fragment nibli's derivation equals the least Herbrand model equals classical entailment, so a disagreement is a genuine reasoner-soundness signal.
- **Closed-world fragment — clingo.** For the **stratified negation-as-failure + closed-world fragment** a classical prover cannot cover (it has no CWA), the IR is regrouped from its event-decomposed form into function-free surface Datalog and checked against **clingo** (Answer Set Programming): nibli's closed-world `TRUE`/`FALSE` must equal whether the reified `goal` atom is in clingo's unique stable model. This is sound because a stratified program's perfect model equals its unique answer set (the criterion is proved in `proofs/Stratification.lean`), and nibli rejects unstratifiable KBs at assert time, so only unique-model programs reach clingo. Checked over a curated NAF corpus plus random stratified-NAF programs (stratified by construction).

Together these validate **logji against both the classical and the stratified-perfect-model semantics of smuni's IR**. Deontic-headed NAF is covered by the ASP oracle (the real `gdpr.lojban` erasure rule runs verbatim in the curated NAF corpus: `se bilga` compiles as a plain gismu and the `lo nu` abstraction maps as an opaque content-hash constant). Ground `du`-equality is covered by **both** oracles: the Vampire side maps `du` to TPTP native `=` (congruence closure over a definite theory derives exactly the union-find's reflexive/symmetric/transitive/substitutive consequences, in both directions), and the ASP side canonicalizes `du`-equivalence classes to a single representative constant before regrouping — including the NAF-through-equality shape, where a witness on one member of a class blocks a `poi na` rule for every member. Non-ground `du` (inside rules), negated `du` (`na du`, a contradiction record rather than NAF), and numeric/description `du` remain conservatively skipped. **Tense flavors** (`pu`/`ca`/`ba`) are covered by **both** oracles via a flavorization pre-pass (`nibli-verify/src/tense.rs`): the engine treats tense wrappers as opaque, exact-match fact flavors, so the pre-pass rewrites them to flavor-suffixed predicates — unmarked rules are instantiated once per occurring flavor (mirroring the engine's flavor-polymorphic rule firing), and explicitly-tensed literals stay pinned to their flavor (an explicitly-tensed consequent also pins its unmarked conditions to bare, as engine-probed). Tense×NAF is conservatively skipped rather than canonized: the engine's `NegatedExistsGroup` carries no tense field, so NAF restrictors are evaluated tenselessly (a bare witness blocks a flavored query; a same-flavor witness does not) — that behavior stays un-oracled pending its resolution. Tense×abstraction and nested wrappers are likewise skipped. **Exact-count queries** (`PA lo X cu Y`) are covered by the ASP oracle as clingo `#count` aggregates — since the 2026-07-02 entity-level counting decision (§Aggregation), **including KBs with rules and with `du`**: the engine excludes the xorlo presupposition witness from counting (the ASP program never had one) and counts one representative per `du`-equivalence class (matching the translator's canonicalization), so the former conservative skips are canonized and the random count generator mixes both shapes in. The gate does not independently validate smuni's decomposition.

**Compiler-seam conformance gate (gerna→smuni):** The two oracle gates above (and the six proofs) all start from the *already-compiled* `LogicBuffer` — they verify the reasoner, not the front-end that produces the IR. The `gerna_smuni_seam_conformance` gate (`nibli-verify/src/seam.rs`, part of `just verify-soundness`) closes the near half of that gap: it compiles **source Lojban text** end-to-end (gerna parse + smuni compile) and checks the resulting FOL two ways — (a) **structural golden cases**, where the compiled shape is hand-verified against the intended FOL (Neo-Davidsonian event decomposition + arg→role mapping, `na`→¬, `.e`/`.a`→∧/∨, the `ro lo`→∀-implication vs `lo`→∃-conjunction contrast, `se`-conversion place-swap); and (b) **metamorphic pairs**, where two different surface forms that must mean the same thing (`E se P F` ≡ `F P E`) are required to compile to the same FOL (modulo a positional variable-renaming), over a curated pair plus a seeded random batch. It needs no external solver, so it always runs. Honest scope: a corpus/property gate, **not** a proof — the golden cases catch a *systematic* miscompilation only where the FOL is hand-verified, and the metamorphic pairs catch *transformation* bugs.

**Mutation-testing baseline (soundness paths):** `cargo-mutants` sweeps every generated mutant of the soundness-critical files (`logji/src/{reasoning,rules,kb}.rs`, `smuni/src/semantic/` — scope and per-mutant test set in `.cargo/mutants.toml`: the logji, smuni, and nibli-engine suites run for each mutant, with a stabilized generous timeout so long-but-finite mutants complete deterministically instead of flapping between the timeout bucket and missed under parallel load). Baseline cut 2026-07-02 from a 906-mutant sweep: **688 caught + 25 timeouts** (a mutant that hangs the tests is a catch), 73 unviable, and **120 survivors (112 after line-number normalization) — an 85.6% kill rate over viable mutants**. **Triage is complete**: every survivor in `mutants-baseline.txt` sits in a justified category — explanation-layer (trace/display only), warn-only (permissive-mode warnings), strategy/redundancy-equivalent (every branch computes the same verdict), or defensive/unreachable-by-invariant — there is no pending bucket. `just mutants` re-runs the sweep and **fails on any survivor not in the baseline**, so test kill-power can only regress loudly; killed baseline entries prompt a shrink. On-demand rather than per-push (a full sweep is ~17 min on a fast desktop). Honest scope: the per-mutant test set deliberately excludes the differential-oracle sweeps (far too slow per mutant), so a survivor here can still be caught by Vampire/clingo in `ci` — the baseline measures the *fast* suites' kill power. The triage paid for itself twice over: it exposed dead code, a real deontic soundness bug (`ganai A gi e'e B` derived a **bare** fact — permission leaked into unqualified truth; both rule positions are now flavor-exact, mirroring tense, pinned at engine + logji level), and pinned two previously-undocumented behaviors as explicit contracts: **exact-count assertions are verdict-inert** (asserting `pa lo gerku cu barda` derives nothing — even the identical count query stays FALSE; the count-semantics decision is tracked), and **`li` numbers never enter the quantifier domain** (a universal restricted to a number-bearing predicate is vacuously true).

**Parse-differential gate (gerna ↔ camxes):** the parser half of the front end is differentially checked against **ilmentufa's camxes** (the maintained PEG implementation of the official Lojban grammar; `just verify-parser`, part of `ci`; the Nix shell provides `node` + a pinned ilmentufa checkout, and the gate skips cleanly outside it). One-directional by design: every sentence gerna ACCEPTS — the shipped corpora plus seeded random batches from all three case generators — must parse under the official grammar; gerna-rejects carry no signal since gerna implements a fragment. Acceptance-level only (parse TREES are not structurally compared — the seam gate's hand-verified goldens cover the text→FOL structure question). The known-divergence allowlist (still-diverging invariant, so it cannot go stale) is currently EMPTY: the five divergences the gate found on its first run were fixed at the source — the DDI corpus cmevla `.fenituin.` (a consonant + rising diphthong, invalid official morphology) was renamed `.fenitoin.` everywhere it is pinned, and the readme rule now uses the official `jenai` selbri connective. The historical relaxed `X je na Y` spelling is now REJECTED at the grammar level (camxes-std parity; a grammar test and a seam structural case pin both directions — `jenai` compiles, `je na` errors). gerna's grammar still accepts the relaxed cmevla morphology; the gate guarantees no shipped corpus or generated line uses it.

**Dictionary-arity differential gate (smuni-dictionary ↔ Predilex):** the dictionary's per-word arities — the values that drive event decomposition and strict-mode arity rejection — are cross-checked against **Predilex** (a CC0 thesaurus of language-neutral sememes-as-predicates; `just verify-dict`, part of `ci`; both CSVs vendored verbatim/projected at a pinned upstream commit in `nibli-verify/vendor/predilex/`). The sound invariant is a **lower bound**, not equality: a Predilex mapping proves the places it uses exist (a slot-permutation's digits, or the master sememe arity under an identity mapping) but never that no more do — the sememes are systematically coarser than Lojban's place structures (~86 of 198 checked words carry extra by-standard/via-medium places, the historical "place-deletion" class, which passes structurally rather than via a curated list). An UNDERCOUNT (dictionary arity < bound) flags a truncated place structure: the gate's first run caught the `cusku` arity-3 override pin (CLL/lensisku/Predilex all say 4 — fixed) and a cross-mode `bilga`/`curmi` fallback default (fixed). The `KNOWN_UNDERCOUNTS` allowlist (value-pinned still-undercounting invariant, so it cannot go stale) holds exactly five hand-verified lensisku definition-text gaps — lujvo whose definitions mark only `$x_1$` while Predilex maps a 2-place sememe; nibli faithfully mirrors its primary source. Dual-mode, never skips: a full-dictionary build checks ~198 word bounds, the CI fallback build checks the curated core set under a loud FALLBACK MODE banner (mode detected from `DICTIONARY.len()` — a compile-time property of the artifact under test, immune to stale-build lies). Honest scope: arity-only (nibli keeps no place-frame permutation data), and Predilex is an independent hint-quality reference, not ground truth — divergences are triaged, not auto-trusted.

**Three-way determinism gate:** the same annotated session script (`determinism-corpus.klaro` — ground facts, rule chains, stratified NAF, `du` identity, tense flavors, exact counts, tolerant/exact arithmetic, and a post-retraction rebuild, every query pinned to its verdict) runs on all three runtime surfaces and must produce the pinned verdicts on each: the native in-process engine (`determinism_corpus_klaro_native`, part of `just verify-klaro-twins`), the lasna WASI component under Wasmtime (`smoke-gasnu-determinism`, part of `ci-wasm`), and the wasm32-unknown-unknown build under node/V8 — the browser-class runtime of the live playground (`just verify-wasm-node`, part of `ci-wasm`; skips cleanly without wasm-pack). The legacy `determinism-corpus.lojban` twin replays natively against the same byte-identical verdicts (`determinism_corpus_lojban_twin`, part of `just verify-soundness`) — a fourth leg pinning cross-front-end determinism, not just cross-runtime. Scope note: pinned queries must complete within every runtime's resource bounds — fuel is a host-level budget (Wasmtime) the native engine does not enforce, so a fuel-trapping query is runtime-dependent by design and excluded.

**Mechanized proof (Track B — complete):** The soundness-critical core is formalized in **Lean 4** (`proofs/`, checked by `just verify-proofs`), each proof bridged to the real engine by a conformance test. Proved:
- **The four-valued verdict combiner** (`proofs/Combiner.lean`): conjunction/disjunction/negation of verdicts never fabricate a definitive `TRUE`/`FALSE` nor swallow a non-definitive operand (the exact algebra whose bug — `True ∧ Unknown → False` — this closes). The combiner's domain is finite, so the Lean proof plus the **exhaustive** Rust conformance test (`exhaustive_soundness_matches_lean_model`) give a *complete* guarantee of the real combiner.
- **The NAF stratification criterion** (`proofs/Stratification.lean`): the dependency-graph condition the engine checks ("no negative edge whose target reaches its source") is proved *equivalent* to the existence of a valid stratification — so the check accepts ⇒ the program is genuinely stratifiable (NAF is sound), and never wrongly rejects a stratifiable one.
- **The SCC decomposition** (`proofs/Scc.lean`): SCCs are the mutual-reachability equivalence classes (a unique partition), and the SCC-based stratification check equals the proven reachability criterion — tying Tarjan's `compute_sccs` to the criterion above.
- **The one-directional unifier** (`proofs/Unify.lean`): a successful head match instantiates the rule template to *exactly* the ground goal (`unify_sound`).
- **Rule firing** (`proofs/RuleFiring.lean`): one firing step is a sound universal-instantiation + modus-ponens step — composing `unify_sound` — and never fabricates.
- **The capstone: a proof trace ⇒ the perfect model** (`proofs/Trace.lean`): a recorded trace, read as a proof certificate, is sound — a `TRUE` trace certifies the conclusion holds in the stratified/perfect model (`pos_sound`, composing rule firing), and a closed-world `FALSE` certifies it does *not* (`neg_sound` — no fabrication). The capstone's four model axioms are each **conformance-bridged to the engine** (`trace_soundness_conformance`): `factAx` — every `Asserted` leaf is a stored KB fact; `candOk`/`ruleClosed` — every `Derived` step maps to a registered rule; `supported` — every closed-world `FALSE` is a genuine non-fact, **every** candidate rule whose conclusion unifies with the goal is recorded as blocked (candidate-completeness), and each block is re-derived at the authoritative depth to a **definitive** premise — a positive premise definitively refuted or a negated premise definitively holding, never an `Unknown` standing in for a refutation — exactly the `Neg` constructor of `Trace.lean`. So the theorem is load-bearing, not merely proof-conditional.

The proofs are model-level (the perfect model is *characterized* by axioms, not constructed as a fixpoint; each axiom is bridged to the engine by a conformance test rather than machine-proved in Lean) plus corpus conformance tests — not one end-to-end machine-checked pipeline from source text to model. The `gerna→smuni` compiler seam that the proofs stop at is now **conformance-gated** (the structural + metamorphic seam gate above), narrowing that gap without closing it: a full machine-checked front-end (or an external-grammar differential) and the non-core `ProofRule` variants (Exists/Forall/Count/Compute/Modal/EqualitySubstitution) remain natural extensions; the soundness-critical core is proved.

## Completeness

**Guarantee:** For non-recursive rule sets with chain depth <= N (default 10), backward chaining with iterative deepening is complete — if a proof exists within the depth bound, it will be found.

**Iterative deepening:** Queries try depth 1, 2, 3, ..., up to `max_chain_depth`. This guarantees finding the shallowest proof first. If the proof exists at depth D <= max_chain_depth, it is found. If no proof exists at any depth, the engine returns FALSE (not ResourceExceeded).

**ResourceExceeded(Depth):** Returned only when all depths up to max_chain_depth are exhausted without finding a proof — the conclusion may exist at a deeper level but the engine cannot determine this within its configured bound. The exact boundary is pinned by `depth_boundary_contract` (logji): with bound D, a chain needing ≤ D rule steps is TRUE, a chain needing D+1 is `ResourceExceeded(Depth)` — never FALSE — and an unreachable goal is FALSE — never a resource verdict.

**Practical cost note (disclosed):** iterative deepening re-explores the shallower search at every level, and per-level cost on rule chains grows steeply (measured ~15×+ per additional chain step: ~0.8 s at chain length 3, ~21.5 s at 4, debug build). The depth bound is therefore a soundness/termination contract, not a performance envelope — the default 10 is far beyond what is computationally practical for long LINEAR chains, while the shipped corpora chain 2–4 hops. This is also why the boundary is pinned at a reduced bound: the contract is depth-uniform.

**For recursive rule sets:** The engine uses a visited-set to detect cycles, returning `Unknown(CycleCut)` instead of diverging. This makes it sound but incomplete for recursive programs — a derivable conclusion may be reported as Unknown if the proof path goes through a cycle.

## Negation Policy

**Semantics:** Global negation-as-failure (NAF) under the Closed-World Assumption (CWA). `NOT P` holds when `P` cannot be proved from the current knowledge base.

**Stratification:** Enforced at rule registration time. The engine builds a predicate dependency graph and rejects any rule that would create a negative cycle (a cycle containing at least one negation edge). This guarantees NAF is applied only in stratifiable programs, where it is sound. The *criterion* is mechanically proved correct in `proofs/Stratification.lean` (the graph condition is equivalent to the existence of a valid stratification — see Soundness § "Mechanized proof"), and the end-to-end REGISTRATION path is differentially checked (`nibli-verify/src/strat_diff.rs`, part of `just verify-soundness`): seeded random rule programs — genuinely mixing stratifiable and unstratifiable shapes — are asserted rule by rule, every accept/reject decision must match an independent implementation of the criterion written from the Lean statement (never from the engine's code), and after any rejection a fresh engine replaying only the surviving lines must answer an entity×predicate battery identically, so a rejected rule provably leaves no trace in the KB.

**NAF visibility:** Proof traces mark Negation steps with `holds: true` as NAF-dependent. The `ProofTrace::has_naf_dependency()` method reports whether a conclusion relies on the CWA. Under open-world semantics, the same conclusion would be Unknown rather than True.

**Closed-world FALSE visibility:** Dually, a positive `FALSE` that rests on the closed-world assumption — *not derivable* from the KB, as opposed to a numeric/arithmetic FALSE that was genuinely *decided* (e.g. `5 dunli 3`) — is flagged `ProofTrace.cwa_false` and renders a symmetric caveat in every proof view. Under open-world semantics such a FALSE would be Unknown, not a proof of the negation.

**CWA implication:** `FALSE` means "not derivable from the current KB and therefore assumed false." It does NOT mean "known to be false in the real world." If the KB is incomplete, NAF may give True for conclusions that would be Unknown with complete information.

**Tense: NAF is tenseless** — see the tense entry in "Disclosed Sharp Edges" below.

## Equality Semantics

**Predicate:** `du(a, b)` — identity/equivalence. Means `a` and `b` are the same entity.

**Properties:**
- **Reflexivity:** `du(x, x)` holds for any x without explicit assertion.
- **Symmetry:** `du(a, b)` implies `du(b, a)` — checked via canonical representative.
- **Transitivity:** `du(a, b)` + `du(b, c)` implies `du(a, c)` — union-find with path compression.
- **Substitutivity:** `du(a, b)` + `P(a)` implies `P(b)` — checked in both direct fact lookup and backward chaining.

**Scope:** Untensed only. `Past(du(a, b))` is stored but does not activate the equivalence index. Tensed equality is future work.

**Implementation:** Union-Find in `KnowledgeBaseInner` with path compression and union-by-size. Equivalence classes rebuilt from surviving `du` facts on retraction.

## Predicate Validation

**Arity checking:** The engine tracks predicate arities via a `PredicateRegistry`. First assertion of a predicate registers its arity (from the ~10,900-entry PHF dictionary if known, otherwise inferred from first use). Subsequent assertions with mismatched arity produce a warning. The dictionary arities themselves are cross-checked against an independent reference by the dictionary-arity differential gate (§Soundness, `just verify-dict`).

**Mode:** Permissive by default — arity mismatches are warned, not rejected; the fact is still inserted. **Strict mode (opt-in)** rejects instead: the offending fact is refused and the whole assertion fails **atomically** (the failed assertion's partial mutations are rolled back via the registry rebuild). Enable with `NIBLI_STRICT=1` (read by the WASM session at startup; gasnu forwards it into the guest) or at runtime via the gasnu `:strict on|off` command, `KnowledgeBase::set_strict`, or `NibliEngine::set_strict`. Strict is inert during retraction-replay rebuilds, so previously-accepted facts always restore faithfully. Honest scope: the event-decomposed surface pipeline produces arity-consistent predicates by construction, so arity mismatches arise via the programmatic/flat-buffer APIs — where the rejection is pinned by tests.

## Integrity Constraints

**Mechanism:** `register_constraint(label, conjuncts)` declares a set of facts that must NOT all hold simultaneously. Checked after every fact insertion.

**Mode:** Permissive by default — violations are warned via stderr, not rejected; the fact is still inserted. **Strict mode (opt-in, same switches as §Predicate Validation)** rejects: the violating fact is rolled back and the assertion fails atomically. Facts inserted internally (forward chaining, compute auto-assert) are also rejected loudly on violation, but have no user call to fail — their rejections are stderr-visible only.

**Scope:** Constraints are structural declarations — they survive KB reset but are not persisted to disk.

## Resource Limits

**Backward-chaining depth:** Configurable `max_chain_depth` (default 10; set via `KnowledgeBase::set_max_chain_depth` — the shipped runtime surfaces keep the default). Iterative deepening tries 1..=max_chain_depth. Exceeding returns `ResourceExceeded(Depth)`.

**WASM fuel:** Wasmtime fuel-based execution limits prevent unbounded computation. Configurable via `NIBLI_FUEL` env var or `:fuel` REPL command. Exceeding returns `ResourceExceeded(Fuel)`.

**WASM memory:** `StoreLimits` caps linear memory growth. Configurable via `NIBLI_MEMORY_MB` env var (default 512 MB). Exceeding returns `ResourceExceeded(Memory)`.

**Contract:** When a resource limit is hit, the engine returns `ResourceExceeded(kind)` — never FALSE. The engine honestly reports that it cannot determine the answer within its resource bounds, rather than guessing.

## Retraction Model

**Incremental TMS:** For simple ground facts (no Skolemization, no rules), retraction removes the fact directly from the fact store and all indexes — O(1) per fact.

**Full rebuild fallback:** For complex assertions (ForAll rules, existential variables, Skolemized facts), retraction falls back to full rebuild from surviving base facts. This is O(total_non_retracted_facts) but guaranteed correct. The guarantee is checked metamorphically at scale (`nibli-verify/src/retract_diff.rs`, part of `just verify-soundness`): seeded random op sequences mix ground, existential, rule, `du`, and stratified-NAF asserts with retractions of random earlier ops, and after EVERY retraction the incremental engine must answer an entity×predicate battery byte-identically to a fresh engine that asserted only the surviving lines — retract ≡ never-asserted, across both the O(1) and the full-rebuild paths.

**Equivalence rebuild:** When `du` facts are retracted, the equivalence index is rebuilt from all surviving `du` facts.

**Public rebuild:** `KnowledgeBase::rebuild()` forces a full rebuild — available as a consistency check or recovery mechanism.

## Query Result Contract

Every query returns exactly one of four results:

| Result | Meaning |
|--------|---------|
| `True` | The formula is derivable from the KB. A proof trace is available. |
| `False` | The formula is not derivable (CWA: assumed false). |
| `Unknown(reason)` | The engine cannot determine the answer: `CycleCut` (recursive cycle detected), `IncompleteKnowledge`, `NafDependent`, `BackendUnavailable` (compute backend unreachable), or `NonFinite` (a numeric operand or result is ±inf/NaN). |
| `ResourceExceeded(kind)` | A resource limit was hit: `Depth`, `Fuel`, or `Memory`. The answer may exist but cannot be found within the configured bounds. |

There is no confident-sounding middle ground. The engine never guesses. (One deliberately DECIDED numeric case that surprises: divide-by-zero over finite operands is a confident FALSE, not non-finite — see "Disclosed Sharp Edges".)

## Hypothetical Reasoning

**Mechanism:** `KnowledgeBase::with_assumptions(assumptions, callback)` creates a temporary clone of the KB, asserts assumptions into the clone, runs the callback, and discards the clone. The original KB is untouched.

**Isolation:** Multiple independent hypotheticals and nesting are supported. Each gets its own snapshot.

**Cost:** O(KB_size) per clone (acceptable for v1). Copy-on-write overlay is future work.

## Aggregation

**Counting is ENTITY-level (decided 2026-07-02).** Everywhere a quantity is produced — exact-count queries (`PA lo X cu Y`), witness enumeration (`??` / `query_find`), `count_witnesses`, `aggregate` — the unit is the *entity*, not the name or the derivation:

- **`du` classes collapse:** two names merged by `du` are ONE entity and count once (the tally enumerates one representative per equivalence class; `[Find]` shows a real asserted name, not a canonical rewrite). Verified against clingo's `#count` over canonicalized constants (the ASP count oracle no longer skips `du`-bearing KBs).
- **Derivation events don't multiply:** a witness tuple's identity is its entity bindings — the internal `_ev*` event variables are engine bookkeeping (pre-decision, one dog answered `?? da gerku` once per derivation event).
- **xorlo presupposition witnesses are not enumerable:** the fresh witness a description universal asserts (`ro lo gerku cu danlu` presupposes ≥1 dog) still satisfies ∃/∀ boolean queries, but is EXCLUDED from counts and `??` results — a phantom entity a rule presupposed must not change "how many". Verified against clingo (whose programs never contained the phantom; the ASP count oracle no longer skips rule-bearing KBs).

**Exact-count ASSERTIONS materialize witnesses (decided 2026-07-02).** `pa lo gerku cu barda` asserts one fresh witness that is a dog and is big — so the assertion is SELF-DERIVABLE (`? pa lo gerku cu barda` is TRUE) and composes with the closed world (asserting more big dogs later changes the count the query reports, as CWA requires). `re lo …` materializes two DISTINCT witnesses with distinct events. Count 0 (`no lo …`) materializes nothing: under CWA "no X are Y" already holds unless the store contradicts it. Scope: count assertions are defined for top-level assertions; a count inside a rule consequent is not a supported shape.

**count_witnesses:** Returns the number of distinct ENTITY-level witness binding sets satisfying an existential formula (the same collapse rules as above; a depth/cycle-cut enumeration refuses to return a definitive undercount — see §Resource Limits).

**aggregate(formula, variable, op):** Extracts numeric values from a named variable across all witness bindings and applies Sum, Min, Max, or Avg. Returns None if no numeric witnesses found.

## Disclosed Sharp Edges

Deliberate or accepted-but-surprising behaviors, each pinned by a test so any change is loud. These are disclosures, not bugs: the engine stays sound relative to them, but a user unaware of them can be surprised by a verdict.

- **Unknown-arity words silently drop over-arity sumti.** A selbri whose arity is KNOWN (shipped dictionary) REJECTS untagged sumti that overflow its places (fail closed, pinned by an engine test). A word NOT in the dictionary defaults to arity 2, and its real arity may be higher — an "overflow" there is unprovable, so the extra untagged sumti are dropped WITHOUT an error (the `overflow_untagged` path in `smuni/src/semantic/compile.rs`). With out-of-dictionary vocabulary, use place tags (`fa`..`fu`) or verify the word's place structure.

- **NAF is tenseless (tense × NAF).** The engine's `NegatedExistsGroup` carries no tense, so a NAF restrictor is evaluated at the BARE flavor: `NOT P` holds by CWA when only `Past(P)` is stored, a bare witness blocks a flavored query, and a same-flavor witness does not block a bare NAF check. This is why tense×NAF stays conservatively un-oracled (skipped, not canonized) in the differential gates above.

- **Divide-by-zero over finite operands is a DECIDED FALSE.** `dilcu` guards `x3 == 0.0` exactly: with finite operands the verdict is a confident FALSE ("x1 = x2/0" is decidably unsatisfiable), NOT `UNKNOWN(non-finite)`. Non-finite OPERANDS, or a finite-operand computation whose RESULT overflows (`1e200 × 1e200 → inf`), stay `UNKNOWN(non-finite)` (`nibli-types/src/arithmetic.rs`, mirrored by the gasnu host fast path and the Python reference backend).

- **`lo` under a sumti connective reads per-occurrence.** `lo gerku cu batci la .adam. .e la .bel.` distributes over `.e`, and each conjunct mints its OWN existential witness: two different dogs — one biting Adam, one biting Bel — satisfy it. It does NOT assert that one dog bites both (pinned by `lo_under_connective_is_per_occurrence_existential`).

- **`na` and tense have one fixed relative scope.** On a single bridi, `na` and a tense marker are flags, not scoped operators: every surface ordering compiles to tense OUTSIDE negation (`pu na broda` ≡ `Past(¬broda)` — "in the past, it was not the case that…"). The other scoping (`¬Past(broda)`, "it is not the case that it was…") is not expressible on one bridi; under CWA the two coincide for ground facts, but they diverge inside larger formulas.

- **`li` numbers never enter the quantifier domain.** A number asserted into a predicate (`li mu cu barda`) does not become a domain member: a universal restricted to that predicate is VACUOUSLY TRUE regardless of its body (pinned by `numeric_terms_are_not_universal_domain_members`). Numbers participate in arithmetic and comparison relations, not in entity quantification or counting.

## What the Engine Cannot Do

- **Probabilistic reasoning:** No confidence scores, no uncertainty propagation. Every result is True, False, Unknown, or ResourceExceeded.
- **Abductive reasoning:** Cannot generate hypotheses ("what facts would make this true?"). Can test hypotheses via `with_assumptions`.
- **Higher-order reasoning:** First-order logic only. No quantification over predicates.
- **Common-sense reasoning:** No default reasoning beyond NAF. No frame axioms, no inertia.
- **Fuzzy logic:** No degrees of truth. Binary true/false within the formal core.
- **Intentional vagueness:** Legal terms like "reasonable" or "good faith" cannot be formalized. The engine handles the deductive, rule-based layer only.
