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

## Model ↔ code correspondence

A Lean proof guarantees the *model* is sound. The gap to the Rust is closed by the
**exhaustive** conformance test `exhaustive_soundness_matches_lean_model` in
`logji/src/reasoning.rs` (`mod combiner_tests`), which checks the real Rust functions satisfy
the same properties over all 10×10 inputs. The combiner's domain is finite, so exhaustive
conformance + a proof of the model's properties together give a **complete** guarantee of the
Rust combiner's behavior — not a sampled one. Keep the two in lock-step: when the Rust combiner
changes, update both `Combiner.lean` and the conformance test.

## Roadmap (remaining Track B)

Next soundness-critical slices, in rough tractability order: the NAF stratification check
(Tarjan SCC, `logji/src/rules.rs`), the one-directional unifier (`logji/src/kb.rs`), rule
firing, and ultimately the headline theorem — *a recorded proof trace ⇒ the conclusion holds
in the stratified/perfect model*.
