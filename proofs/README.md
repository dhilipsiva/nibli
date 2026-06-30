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

## Model ↔ code correspondence

A Lean proof guarantees the *model* is sound; a Rust conformance test ties it to the real code.

- **Combiner** (`exhaustive_soundness_matches_lean_model`, `logji/src/reasoning.rs`): checks the
  real Rust functions over all 10×10 inputs. The domain is finite, so exhaustive conformance + the
  model proof give a **complete** guarantee.
- **Stratification** (`check_stratification_matches_proven_criterion`, `logji/src/rules.rs`):
  checks the real Tarjan-based `check_stratification` agrees with a naive reachability
  implementation of the proven criterion, over hand-crafted + deterministically-randomized
  graphs. Graphs are unbounded, so this is a **corpus** conformance test (not exhaustive), and it
  conformance-tests `compute_sccs` rather than proving it.

Keep the two sides in lock-step: when a Rust component changes, update both its `.lean` model and
its conformance test.

## Roadmap (remaining Track B)

Next soundness-critical slices, in rough tractability order: **verifying Tarjan `compute_sccs`**
itself (currently only conformance-tested), the one-directional unifier (`logji/src/kb.rs`), rule
firing, and ultimately the headline theorem — *a recorded proof trace ⇒ the conclusion holds in
the stratified/perfect model*.
