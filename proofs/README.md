# `proofs/` — mechanized soundness proofs (Track B)

Lean 4 formalizations of nibli's soundness-critical core. The proof assistant *proves* the
key invariants, rather than only testing them. Checked by `just verify-proofs`
(`lean proofs/*.lean`); the Nix dev shell provides `lean`. No mathlib — the Lean prelude
suffices, so each file is self-contained and offline.

## What's proved so far

### `Combiner.lean` — the four-valued verdict combiner

Formalizes the pure combiner functions from `logji/src/reasoning.rs`
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
(`logji/src/rules.rs` `check_stratification` / `compute_sccs`), and proves the **criterion is
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

Formalizes the substitution engine under backward chaining (`logji/src/kb.rs` `unify_terms` :326 /
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

Mathlib-free (prelude only). The `Number` payload is abstracted to `Nat` — only decidable equality
matters for match soundness, not f64 bit-semantics.

## Model ↔ code correspondence

A Lean proof guarantees the *model* is sound; a Rust conformance test ties it to the real code.

- **Combiner** (`exhaustive_soundness_matches_lean_model`, `logji/src/reasoning.rs`): checks the
  real Rust functions over all 10×10 inputs. The domain is finite, so exhaustive conformance + the
  model proof give a **complete** guarantee.
- **Stratification** (`check_stratification_matches_proven_criterion`, `logji/src/rules.rs`):
  checks the real Tarjan-based `check_stratification` agrees with a naive reachability
  implementation of the proven criterion, over hand-crafted + deterministically-randomized graphs.
  Graphs are unbounded, so this is a **corpus** conformance test (not exhaustive).
- **SCC decomposition** (`compute_sccs_matches_scc_spec`, `logji/src/rules.rs`): checks the real
  Tarjan `compute_sccs` output is a partition of the node set and groups two nodes together
  *exactly* when they are mutually reachable (the `reachable_sets` reference), over the same corpus
  (with a non-vacuity guard that a nontrivial SCC appears). Ties the actual algorithm to
  `Scc.lean`'s mutual-reachability spec; corpus, not exhaustive.
- **Unifier** (`unify_conformance`, `logji/src/tests.rs`): checks the real `unify_facts` /
  `substitute_fact` satisfy the proven soundness property (`substitute_fact(template, σ) ==
  concrete`) on every successful match, plus determinism + minimal bindings, over hand-crafted +
  random `(template, ground-concrete)` pairs. Ties the real substitution engine to `Unify.lean`;
  corpus, not exhaustive.

Keep the two sides in lock-step: when a Rust component changes, update both its `.lean` model and
its conformance test.

## Roadmap (remaining Track B)

Next soundness-critical slices, in rough tractability order: **rule firing** (one firing step is a
sound universal-instantiation + modus-ponens step — composes `Unify.lean`'s `unify_sound`, with
NAF-condition soundness delegated to `Stratification.lean` + `Scc.lean`), and ultimately the
headline theorem — *a recorded proof trace ⇒ the conclusion holds in the stratified/perfect model*
(per-`ProofRule` local soundness + induction over the trace DAG, composing all four proofs).
