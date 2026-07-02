# Nibli Engine Guarantees

Formal statement of the reasoning engine's properties, boundaries, and contracts.

## Soundness

**Guarantee:** The engine never returns TRUE for a formula that does not follow from the asserted facts and compiled rules, given a correct implementation.

If the engine says TRUE, a formal proof trace exists showing the derivation chain from asserted axioms through named inference rules to the conclusion. Every step is mechanically verifiable.

**Caveat:** The engine is software. A bug in the parser (gerna), semantic compiler (smuni), or reasoning engine (logji) could produce a valid-looking proof of a wrong statement. Such a bug would be deterministic, reproducible, and testable — fundamentally different from stochastic hallucination. The engine is tested with 639+ unit tests and 21 integration tests across the full pipeline.

**Differential soundness gate (Track A):** Beyond unit/integration tests, the reasoner is differentially checked against **two** external solvers, one per fragment, gated in CI (`just verify-soundness`). The `nibli-verify` harness exports the compiled FOL IR (`LogicBuffer`) and asserts nibli's `TRUE`/`FALSE` matches the oracle:

- **Classical fragment — Vampire.** For the cleanly-mappable **Horn / NAF-free fragment**, the IR is translated to TPTP and checked against **Vampire** — `TRUE ⟺ Theorem`, `FALSE ⟺ CounterSatisfiable` — over a curated corpus, a seeded batch of random Horn programs, and the auto-extracted mappable slice of the `gdpr`/`ddi` case-study corpora. On that fragment nibli's derivation equals the least Herbrand model equals classical entailment, so a disagreement is a genuine reasoner-soundness signal.
- **Closed-world fragment — clingo.** For the **stratified negation-as-failure + closed-world fragment** a classical prover cannot cover (it has no CWA), the IR is regrouped from its event-decomposed form into function-free surface Datalog and checked against **clingo** (Answer Set Programming): nibli's closed-world `TRUE`/`FALSE` must equal whether the reified `goal` atom is in clingo's unique stable model. This is sound because a stratified program's perfect model equals its unique answer set (the criterion is proved in `proofs/Stratification.lean`), and nibli rejects unstratifiable KBs at assert time, so only unique-model programs reach clingo. Checked over a curated NAF corpus plus random stratified-NAF programs (stratified by construction).

Together these validate **logji against both the classical and the stratified-perfect-model semantics of smuni's IR**. Deontic-headed NAF is covered by the ASP oracle (the real `gdpr.lojban` erasure rule runs verbatim in the curated NAF corpus: `se bilga` compiles as a plain gismu and the `lo nu` abstraction maps as an opaque content-hash constant). Ground `du`-equality is covered by **both** oracles: the Vampire side maps `du` to TPTP native `=` (congruence closure over a definite theory derives exactly the union-find's reflexive/symmetric/transitive/substitutive consequences, in both directions), and the ASP side canonicalizes `du`-equivalence classes to a single representative constant before regrouping — including the NAF-through-equality shape, where a witness on one member of a class blocks a `poi na` rule for every member. Non-ground `du` (inside rules), negated `du` (`na du`, a contradiction record rather than NAF), and numeric/description `du` remain conservatively skipped. **Tense flavors** (`pu`/`ca`/`ba`) are covered by **both** oracles via a flavorization pre-pass (`nibli-verify/src/tense.rs`): the engine treats tense wrappers as opaque, exact-match fact flavors, so the pre-pass rewrites them to flavor-suffixed predicates — unmarked rules are instantiated once per occurring flavor (mirroring the engine's flavor-polymorphic rule firing), and explicitly-tensed literals stay pinned to their flavor (an explicitly-tensed consequent also pins its unmarked conditions to bare, as engine-probed). Tense×NAF is conservatively skipped rather than canonized: the engine's `NegatedExistsGroup` carries no tense field, so NAF restrictors are evaluated tenselessly (a bare witness blocks a flavored query; a same-flavor witness does not) — that behavior stays un-oracled pending its resolution. Tense×abstraction and nested wrappers are likewise skipped. **Exact-count queries** (`PA lo X cu Y`) are covered by the ASP oracle as clingo `#count` aggregates, over the guarded **ground-fact fragment**: with a universal rule in the KB the rule's xorlo existential-import witness is itself a counted domain member (engine-probed: two dogs plus `ro lo gerku cu danlu` makes `re lo gerku cu danlu` count 3), and `du`-merged entities are not collapsed by the engine's count — so count queries over KBs containing rules or `du` are conservatively skipped pending the count-semantics decision, not canonized. The gate does not independently validate smuni's decomposition.

**Compiler-seam conformance gate (gerna→smuni):** The two oracle gates above (and the six proofs) all start from the *already-compiled* `LogicBuffer` — they verify the reasoner, not the front-end that produces the IR. The `gerna_smuni_seam_conformance` gate (`nibli-verify/src/seam.rs`, part of `just verify-soundness`) closes the near half of that gap: it compiles **source Lojban text** end-to-end (gerna parse + smuni compile) and checks the resulting FOL two ways — (a) **structural golden cases**, where the compiled shape is hand-verified against the intended FOL (Neo-Davidsonian event decomposition + arg→role mapping, `na`→¬, `.e`/`.a`→∧/∨, the `ro lo`→∀-implication vs `lo`→∃-conjunction contrast, `se`-conversion place-swap); and (b) **metamorphic pairs**, where two different surface forms that must mean the same thing (`E se P F` ≡ `F P E`) are required to compile to the same FOL (modulo a positional variable-renaming), over a curated pair plus a seeded random batch. It needs no external solver, so it always runs. Honest scope: a corpus/property gate, **not** a proof — the golden cases catch a *systematic* miscompilation only where the FOL is hand-verified, and the metamorphic pairs catch *transformation* bugs.

**Parse-differential gate (gerna ↔ camxes):** the parser half of the front end is differentially checked against **ilmentufa's camxes** (the maintained PEG implementation of the official Lojban grammar; `just verify-parser`, part of `ci`; the Nix shell provides `node` + a pinned ilmentufa checkout, and the gate skips cleanly outside it). One-directional by design: every sentence gerna ACCEPTS — the shipped corpora plus seeded random batches from all three case generators — must parse under the official grammar; gerna-rejects carry no signal since gerna implements a fragment. Acceptance-level only (parse TREES are not structurally compared — the seam gate's hand-verified goldens cover the text→FOL structure question). The known-divergence allowlist (still-diverging invariant, so it cannot go stale) is currently EMPTY: the five divergences the gate found on its first run were fixed at the source — the DDI corpus cmevla `.fenituin.` (a consonant + rising diphthong, invalid official morphology) was renamed `.fenitoin.` everywhere it is pinned, and the readme rule now uses the official `jenai` selbri connective (gerna parses the `nai`-suffixed forms `jenai`/`janai`/`jonai`/`junai`, compiling `X jenai Y` identically to the relaxed `X je na Y` — pinned by a seam metamorphic pair). gerna's GRAMMAR still accepts the relaxed forms; the gate guarantees no shipped corpus or generated line uses one.

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

**ResourceExceeded(Depth):** Returned only when all depths up to max_chain_depth are exhausted without finding a proof — the conclusion may exist at a deeper level but the engine cannot determine this within its configured bound.

**For recursive rule sets:** The engine uses a visited-set to detect cycles, returning `Unknown(CycleCut)` instead of diverging. This makes it sound but incomplete for recursive programs — a derivable conclusion may be reported as Unknown if the proof path goes through a cycle.

## Negation Policy

**Semantics:** Global negation-as-failure (NAF) under the Closed-World Assumption (CWA). `NOT P` holds when `P` cannot be proved from the current knowledge base.

**Stratification:** Enforced at rule registration time. The engine builds a predicate dependency graph and rejects any rule that would create a negative cycle (a cycle containing at least one negation edge). This guarantees NAF is applied only in stratifiable programs, where it is sound. The *criterion* is mechanically proved correct in `proofs/Stratification.lean` (the graph condition is equivalent to the existence of a valid stratification — see Soundness § "Mechanized proof"), and the end-to-end REGISTRATION path is differentially checked (`nibli-verify/src/strat_diff.rs`, part of `just verify-soundness`): seeded random rule programs — genuinely mixing stratifiable and unstratifiable shapes — are asserted rule by rule, every accept/reject decision must match an independent implementation of the criterion written from the Lean statement (never from the engine's code), and after any rejection a fresh engine replaying only the surviving lines must answer an entity×predicate battery identically, so a rejected rule provably leaves no trace in the KB.

**NAF visibility:** Proof traces mark Negation steps with `holds: true` as NAF-dependent. The `ProofTrace::has_naf_dependency()` method reports whether a conclusion relies on the CWA. Under open-world semantics, the same conclusion would be Unknown rather than True.

**Closed-world FALSE visibility:** Dually, a positive `FALSE` that rests on the closed-world assumption — *not derivable* from the KB, as opposed to a numeric/arithmetic FALSE that was genuinely *decided* (e.g. `5 dunli 3`) — is flagged `ProofTrace.cwa_false` and renders a symmetric caveat in every proof view. Under open-world semantics such a FALSE would be Unknown, not a proof of the negation.

**CWA implication:** `FALSE` means "not derivable from the current KB and therefore assumed false." It does NOT mean "known to be false in the real world." If the KB is incomplete, NAF may give True for conclusions that would be Unknown with complete information.

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

**Arity checking:** The engine tracks predicate arities via a `PredicateRegistry`. First assertion of a predicate registers its arity (from the ~10,900-entry PHF dictionary if known, otherwise inferred from first use). Subsequent assertions with mismatched arity produce a warning.

**Mode:** Permissive (v1). Arity mismatches are warned, not rejected. The fact is still inserted. Strict mode (rejection on mismatch) is future work.

## Integrity Constraints

**Mechanism:** `register_constraint(label, conjuncts)` declares a set of facts that must NOT all hold simultaneously. Checked after every fact insertion.

**Mode:** Permissive (v1). Violations are warned via stderr, not rejected. The fact is still inserted. Strict mode is future work.

**Scope:** Constraints are structural declarations — they survive KB reset but are not persisted to disk.

## Resource Limits

**Backward-chaining depth:** Configurable `max_chain_depth` (default 10). Iterative deepening tries 1..=max_chain_depth. Exceeding returns `ResourceExceeded(Depth)`.

**WASM fuel:** Wasmtime fuel-based execution limits prevent unbounded computation. Configurable via `NIBLI_FUEL` env var or `:fuel` REPL command. Exceeding returns `ResourceExceeded(Fuel)`.

**WASM memory:** `StoreLimits` caps linear memory growth. Configurable via `NIBLI_MEMORY_MB` env var (default 512 MB). Exceeding returns `ResourceExceeded(Memory)`.

**Contract:** When a resource limit is hit, the engine returns `ResourceExceeded(kind)` — never FALSE. The engine honestly reports that it cannot determine the answer within its resource bounds, rather than guessing.

## Retraction Model

**Incremental TMS:** For simple ground facts (no Skolemization, no rules), retraction removes the fact directly from the fact store and all indexes — O(1) per fact.

**Full rebuild fallback:** For complex assertions (ForAll rules, existential variables, Skolemized facts), retraction falls back to full rebuild from surviving base facts. This is O(total_non_retracted_facts) but guaranteed correct.

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

There is no confident-sounding middle ground. The engine never guesses.

## Hypothetical Reasoning

**Mechanism:** `KnowledgeBase::with_assumptions(assumptions, callback)` creates a temporary clone of the KB, asserts assumptions into the clone, runs the callback, and discards the clone. The original KB is untouched.

**Isolation:** Multiple independent hypotheticals and nesting are supported. Each gets its own snapshot.

**Cost:** O(KB_size) per clone (acceptable for v1). Copy-on-write overlay is future work.

## Aggregation

**count_witnesses:** Returns the number of distinct witness binding sets satisfying an existential formula.

**aggregate(formula, variable, op):** Extracts numeric values from a named variable across all witness bindings and applies Sum, Min, Max, or Avg. Returns None if no numeric witnesses found.

## What the Engine Cannot Do

- **Probabilistic reasoning:** No confidence scores, no uncertainty propagation. Every result is True, False, Unknown, or ResourceExceeded.
- **Abductive reasoning:** Cannot generate hypotheses ("what facts would make this true?"). Can test hypotheses via `with_assumptions`.
- **Higher-order reasoning:** First-order logic only. No quantification over predicates.
- **Common-sense reasoning:** No default reasoning beyond NAF. No frame axioms, no inertia.
- **Fuzzy logic:** No degrees of truth. Binary true/false within the formal core.
- **Intentional vagueness:** Legal terms like "reasonable" or "good faith" cannot be formalized. The engine handles the deductive, rule-based layer only.
