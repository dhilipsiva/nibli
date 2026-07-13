# `proofs/` — mechanized soundness proofs (Track B)

Lean 4 formalizations of nibli's soundness-critical core. The proof assistant *proves* the
key invariants, rather than only testing them. Checked by `just verify-proofs`
(`lean proofs/*.lean`); the Nix dev shell provides `lean`. No mathlib — the Lean prelude
suffices, so each file is self-contained and offline.

## What's proved

### `Combiner.lean` — the four-valued verdict combiner

Formalizes the pure combiner functions from `nibli-reason/src/reasoning.rs`
(`combine_conjunction`, `combine_disjunction`, `combine_indeterminate`, `negate_result`) over
the finite `QueryResult` domain (`True`, `False`, `Unknown(×5)`, `ResourceExceeded(×3)`), and
proves the **soundness algebra**: the combiner never *fabricates* a definitive verdict
(reports `TRUE`/`FALSE` when the inputs don't justify it) nor *swallows* a non-definitive
sibling — the exact failure the historical bug had (commit `93bb900`: `True ∧ Unknown`
collapsed to `False`). Headline theorems:

- **Bug regressions:** `True ∧ Unknown = Unknown`, `False ∨ Unknown = Unknown` (both operand
  orders).
- **Soundness characterization:** `conj a b = True ↔ a = True ∧ b = True`,
  `conj a b = False ↔ a = False ∨ b = False`, and the disjunction duals — a definitive verdict
  appears in *exactly* the classically-correct case.
- **Negation:** the four NAF laws; negation never turns a non-definitive verdict definitive;
  involutive on `{True,False}`, and (documented, not an oversight) *not* involutive on
  `Unknown` (reasons collapse to `NafDependent`).
- **Precedence:** `ResourceExceeded` outranks `Unknown`; the carried reason is left-biased, so
  the combiner is commutative on the verdict *class* but not on the reason (proved both ways).

### `Stratification.lean` — the NAF stratification criterion

Formalizes the predicate dependency graph the engine builds to police negation-as-failure
(`nibli-reason/src/rules.rs` `check_stratification` / `compute_sccs`), and proves the **criterion is
correct**: over the graph, "no negative edge whose target reaches back to its source" (≡ no
negative edge with both endpoints in one SCC — exactly what the Rust check rejects on) is
**equivalent** to "a valid stratification (level function) exists." Headline theorems:

- **Soundness** (`noNegCycle_imp_stratifiable`): the check accepts ⇒ the program is genuinely
  stratifiable. Witnessed by `level p := |{nodes reachable from p}|`; a negative edge `H → B`
  with no negative cycle means `B` cannot reach `H`, so `level B < level H` (the strict
  stratification constraint).
- **Completeness** (`stratifiable_imp_noNegCycle`): a stratification precludes a negative edge
  on a cycle, so the check never rejects a stratifiable program.
- **Corollaries:** `NoNegCycle g ↔ Stratifiable g`, and `RejectsByCriterion g ↔ ¬ Stratifiable g`
  (the check rejects exactly the unstratifiable programs).

The finiteness reasoning is mathlib-free: reachability is the inductive reflexive-transitive
closure, made decidable for counting via `Classical`, with two short local `List.countP` lemmas.

### `Scc.lean` — the SCC decomposition

Formalizes the strongly-connected-component structure `check_stratification` relies on
(`compute_sccs`), closing the gap `Stratification.lean` left — *is the SCC-based check the engine
runs the same as the proven reachability criterion?* Two results:

- **SCCs are the mutual-reachability equivalence classes.** `SameSCC g a b := Reach g a b ∧ Reach g
  b a` is reflexive, symmetric, and transitive, so the SCC partition is well-defined. A
  decomposition is *correct* iff two nodes share a label exactly when they are `SameSCC`;
  `decomp_unique` proves any two correct decompositions induce the **same** partition (so Tarjan's
  output is unique up to relabeling), and `canonicalComp_correct` proves a correct one always
  exists. Verifying the imperative Tarjan traversal itself is out of scope; the real `compute_sccs`
  output is tied to this spec by the conformance test below.
- **The SCC check equals the criterion.** `sccRejects_iff_criterion` proves `SccRejects` (a negative
  edge with both endpoints in one SCC — exactly `check_stratification`) is equivalent to
  `RejectsByCriterion` (the reachability criterion). Composed with `Stratification.lean`'s
  `RejectsByCriterion ↔ ¬Stratifiable`, the SCC-based check rejects exactly the unstratifiable
  programs.

Mathlib-free: `funext`/`propext`/`cast` + the `Classical` namespace; the reachability model is
duplicated from `Stratification.lean` (each proof file stands alone).

### `Unify.lean` — the one-directional unifier

Formalizes the substitution engine under backward chaining (`nibli-reason/src/kb.rs` `unify_terms` :326 /
`substitute_term` :389): matching a rule's conclusion TEMPLATE (which carries pattern variables)
against a ground goal produces a substitution σ, and it must be sound — a successful match
instantiates the template to *exactly* the goal. Models `GTerm` (mirroring `GroundTerm`), an
association-list `Subst`, `subst`, and the accumulator-threading `unify`, and proves:

- **`unify_sound`**: `NoVar c → unify t c σ₀ = some σ → subst σ t = c` — the headline soundness
  property. The `depPair` case (two components sharing one accumulator) is discharged by two
  lemmas: **`unify_extends`** (a successful `unify` only adds bindings — prior ones are preserved)
  and **`subst_stable`** (a ground `subst σ t` is unchanged by extending σ), so the first
  component's binding survives the second component's unification.
- **`unify_minimal`**: `unify` never binds a variable absent from the template (no extraneous
  bindings).

The `NoVar c` hypothesis (the concrete side is ground) is enforced in the ENGINE as a mechanism,
not call-site discipline: `assert_typed_fact` drops any fact whose args contain a pattern variable
— recursively, including inside `SkolemFn`/`DepPair` components — at the single store-insert
boundary (`nibli-reason/src/rules.rs`, pinned by `non_ground_fact_is_dropped_at_the_assert_boundary`),
so a stored fact can never violate the hypothesis regardless of upstream changes.

Mathlib-free (prelude only). The `Number` payload is abstracted to `Nat` — only decidable equality
matters for match soundness, not f64 bit-semantics.

### `RuleFiring.lean` — one firing step is sound modus-ponens

Formalizes how backward chaining derives a goal by FIRING a universal rule (`nibli-reason/src/reasoning.rs`
`process_phase` / `emit_derived`; `UniversalRuleRecord`): unify the rule's conclusion template
against the goal (σ), discharge each condition under σ (positive conditions hold; the
`negated_condition_indices` FAIL, by negation-as-failure), and conclude the σ-instantiated head. It
lifts `Unify.lean`'s `unify_sound` from terms to atoms and then to a firing step:

- **`unifyArgs_sound`** / **`unifyAtom_sound`**: the arg-wise fold that mirrors the argument loop in
  the real `unify_facts` — a successful head match instantiates the conclusion template to *exactly*
  the ground goal (same `unify_extends` + `subst_stable` reasoning as `Unify.lean`'s `depPair` case,
  now over an argument list).
- **`firing_sound`**: if the rule holds in the model M (the perfect/least model is closed under
  every registered rule; the NAF conditions are well-defined *because* the program is stratified —
  `Stratification.lean` + `Scc.lean`), the head unifies with the ground goal via σ, and σ discharges
  the conditions, then the goal is in M. Composes `unifyAtom_sound`, so the instantiated head *is*
  the goal.
- **`firing_no_fabrication`** (contrapositive): if the goal is not in M, no firing of a model-sound
  rule can conclude it — some condition must be undischarged. Firing never fabricates.

Mathlib-free; the term-level unifier is duplicated from `Unify.lean` (each proof file stands alone).

### `Trace.lean` — the capstone: a proof trace ⇒ the conclusion holds in the perfect model

The headline soundness theorem, tying the five layers above together at the top: a recorded proof
trace, read as a proof CERTIFICATE, is sound w.r.t. the stratified/perfect model. The trace deals in
GROUND atoms (unify already happened — `Derived{fact}` carries the instantiated conclusion), so it
abstracts firing via a model axiom (no unifier duplication). A `PerfectModel` bundles the model + four
axioms — `factAx` (facts hold), `ruleClosed` (= `RuleFiring.firing_sound` at the ground instance),
`candOk`, and `supported` (least-model minimality). Only `supported` is not machine-checked here; it
is justified by `Stratification.lean` (a stratified program has a unique, supported perfect model) and
assumed, as `RuleFiring.lean` assumes `RuleHolds`. Certificates are DEPTH-INDEXED (`Pos`/`Neg : Nat →
Atom → Prop`, mutual `def` on a fuel `Nat` — a mutual `inductive` is rejected by the positivity
checker; the engine is depth-bounded, so this is faithful), and the negative certificate ranges over
the FINITE candidate rules so it is trace-constructible. Results:

- **`cert_sound`** (by induction on the fuel): `Pos → M` (a positive certificate is sound — the
  `fire` case composes `ruleClosed`=`firing_sound`) and `Neg → ¬ M` (a closed-world certificate is
  sound — the `notFound` case uses `supported` + the finite-candidate blocking premise + the mutual
  IH). Corollaries `pos_sound` (TRUE trace ⇒ conclusion in the model) and `neg_sound` (closed-world
  FALSE ⇒ conclusion NOT in the model — no fabrication).
- **`qproof_sound`**: the same for compound queries — a recorded `QProof`/`QRefute` over the
  connectives (`and`/`or`/`not`) is sound (`QProof q → qHolds q`, `QRefute q → ¬ qHolds q`), composing
  the atom certificates through the connective algebra (mirroring `Combiner.lean`).

This is the top of the tower: with the five component proofs, every layer of the reasoner — term
unification, rule firing, NAF stratification, the SCC decomposition, the verdict combiner, and the
whole recorded trace — is tied to a mechanized soundness proof. Mathlib-free (prelude only).

## Model ↔ code correspondence

A Lean proof guarantees the *model* is sound; a Rust conformance test ties it to the real code.

- **Combiner** (`exhaustive_soundness_matches_lean_model`, `nibli-reason/src/reasoning.rs`): checks the
  real Rust functions over all 10×10 inputs. The domain is finite, so exhaustive conformance + the
  model proof give a **complete** guarantee.
- **Stratification** (`check_stratification_matches_proven_criterion`, `nibli-reason/src/rules.rs`):
  checks the real Tarjan-based `check_stratification` agrees with a naive reachability
  implementation of the proven criterion, over hand-crafted + deterministically-randomized graphs.
  Graphs are unbounded, so this is a **corpus** conformance test (not exhaustive).
- **SCC decomposition** (`compute_sccs_matches_scc_spec`, `nibli-reason/src/rules.rs`): checks the real
  Tarjan `compute_sccs` output is a partition of the node set and groups two nodes together
  *exactly* when they are mutually reachable (the `reachable_sets` reference), over the same corpus
  (with a non-vacuity guard that a nontrivial SCC appears). Ties the actual algorithm to
  `Scc.lean`'s mutual-reachability spec; corpus, not exhaustive.
- **Unifier** (`unify_conformance`, `nibli-reason/src/tests.rs`): checks the real `unify_facts` /
  `substitute_fact` satisfy the proven soundness property (`substitute_fact(template, σ) ==
  concrete`) on every successful match, plus determinism + minimal bindings, over hand-crafted +
  random `(template, ground-concrete)` pairs. Ties the real substitution engine to `Unify.lean`;
  corpus, not exhaustive.
- **Rule firing** (`rule_firing_conformance`, `nibli-reason/src/tests.rs`): drives the real engine on the
  rule `∀x. (gerku(x) ∧ ¬mlatu(x)) → danlu(x)` and checks it fires *exactly* when the conditions are
  discharged (positive present, negated absent — all four corners), never fabricates when one is
  undischarged, and records the σ-instantiated head (`danlu(alis)`, not `danlu(bob)`). Ties the real
  firing step to `RuleFiring.lean`'s `firing_sound` / `firing_no_fabrication`.
- **Trace soundness** (`trace_soundness_conformance`, `nibli-reason/src/tests.rs`): a `validate_cert` walker
  asserts every recorded step's local certificate condition (Conjunction→holds=all-children,
  Negation→NAF/holds-flip, ProofRef→referent match, false leaves→¬hold) AND — the axiom bridges —
  ties the trace to the real engine: **`factAx`** (each `Asserted` leaf is a stored KB fact),
  **`candOk`/`ruleClosed`** (each `Derived` step maps to a registered rule), and **`supported`** (each
  closed-world `PredicateNotFound` is a genuine non-fact; **every** candidate rule whose conclusion
  unifies with the goal appears as a blocked child — candidate-completeness — and each block is
  re-derived at the authoritative depth to a definitive premise, a positive premise definitively
  refuted or a negated premise definitively holding: the exact `Neg` constructor at `Trace.lean:91`.
  The engine's certificate emission mirrors this — the blocked-premise re-check runs at the verdict's
  own depth and treats `negated_condition_indices` correctly, so a NAF-blocked candidate records its
  holding negated premise). `Exercised` counters assert each bridge fires (never vacuous) — including
  a multi-candidate completeness case and definitive-block re-derivations — and a break-one-leaf
  sanity confirms it catches violations. So the model axioms are no longer merely assumed — composed
  with `Trace.lean`, the capstone is **load-bearing, not proof-conditional**. Corpus, not exhaustive;
  rules carrying negated-exists groups (`poi na <selbri>`) block through the group check, whose
  definitiveness is not re-derived by the bridge (their candidate-completeness still is).

Keep the two sides in lock-step: when a Rust component changes, update both its `.lean` model and
its conformance test.

## Track B — complete

All six soundness-critical layers are now mechanized: the four-valued **combiner** (`Combiner.lean`),
the NAF **stratification** criterion (`Stratification.lean`), the **SCC** decomposition (`Scc.lean`),
the **unifier** (`Unify.lean`), **rule firing** (`RuleFiring.lean`), and the capstone **trace ⇒
perfect-model** theorem (`Trace.lean`) — each bridged to the real engine by a conformance test.

The proofs are model-level (each cites, as a hypothesis, the perfect-model / stratification facts the
adjacent proofs establish) plus corpus conformance tests, not a single end-to-end machine-checked
pipeline from source text to model; that, and the specialized non-core `ProofRule` variants
(Exists/Forall/Count/Compute/Modal/EqualitySubstitution), remain natural extensions. The
soundness-critical core — "if the engine says TRUE a derivation exists; if it says closed-world FALSE
none does" — is proved.
