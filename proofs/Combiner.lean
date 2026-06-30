/-
  Mechanized soundness proof of nibli's four-valued verdict combiner (Track B, phase 1).

  This formalizes the pure combiner functions from `logji/src/reasoning.rs` and proves the
  soundness-critical algebra: the combiner can never FABRICATE a definitive verdict (report
  TRUE/FALSE when the inputs do not justify it) nor SWALLOW a non-definitive sibling — the
  exact failure the historical bug had (commit 93bb900: `True ∧ Unknown` collapsed to `False`).

  Correspondence (each `def` mirrors a Rust fn, verbatim behavior):
    combineIndeterminate  ← logji/src/reasoning.rs  combine_indeterminate (:184)
    combineConjunction    ← logji/src/reasoning.rs  combine_conjunction   (:195)
    combineDisjunction    ← logji/src/reasoning.rs  combine_disjunction   (:205)
    negateResult          ← logji/src/reasoning.rs  negate_result         (:228)
  QueryResult/UnknownReason/ResourceKind mirror `nibli-types/src/logic.rs`.

  The model↔code gap is closed by the EXHAUSTIVE conformance test in logji's `combiner_tests`
  (`logji/src/reasoning.rs`), which asserts the real Rust functions satisfy these same
  properties over all 10×10 inputs. The combiner's domain is finite, so a proof of the model
  plus exhaustive conformance is a COMPLETE guarantee, not a sampled one.

  Checked by `lean proofs/Combiner.lean` (`just verify-proofs`). No mathlib; the Lean prelude
  suffices. The unused-simp-args linter is cosmetic here (some `cases` branches reduce before
  simp needs the unfolding lemmas), so it is disabled.
-/

set_option linter.unusedSimpArgs false

namespace Nibli

/-- Why a verdict is `Unknown`. Mirrors `nibli_types::logic::UnknownReason`. -/
inductive UnknownReason
  | cycleCut
  | incompleteKnowledge
  | nafDependent
  | backendUnavailable
  | nonFinite
  deriving DecidableEq, Repr

/-- Which resource bound was hit. Mirrors `nibli_types::logic::ResourceKind`. -/
inductive ResourceKind
  | depth
  | fuel
  | memory
  deriving DecidableEq, Repr

/-- The four-valued verdict. Mirrors `nibli_types::logic::QueryResult`. `tt`/`ff` avoid a
    clash with the `Bool` literals `true`/`false`. -/
inductive QueryResult
  | tt
  | ff
  | unknown (r : UnknownReason)
  | resourceExceeded (k : ResourceKind)
  deriving DecidableEq, Repr

open QueryResult

/-- The verdict is definitive (a real TRUE/FALSE), not a non-answer. -/
def isDefinitive : QueryResult → Bool
  | tt => true
  | ff => true
  | _ => false

/-- Coarse verdict class: `tt`↦0, `ff`↦1, `unknown _`↦2, `resourceExceeded _`↦3. Used to
    state the properties that hold up to the carried reason/kind. -/
def vclass : QueryResult → Nat
  | tt => 0
  | ff => 1
  | unknown _ => 2
  | resourceExceeded _ => 3

/-- `combine_indeterminate` (reasoning.rs:184): the non-definitive region of And/Or.
    `ResourceExceeded` outranks `Unknown`; within a rank the LEFT operand wins. The final
    arm is unreachable from the And/Or guards (both operands definitive) but keeps the
    function total. -/
def combineIndeterminate : QueryResult → QueryResult → QueryResult
  | resourceExceeded k, _ => resourceExceeded k
  | _, resourceExceeded k => resourceExceeded k
  | unknown r, _ => unknown r
  | _, unknown r => unknown r
  | _, _ => ff

/-- `combine_conjunction` (reasoning.rs:195): `False` if either operand is `False`; `True`
    if both are `True`; otherwise the indeterminate combination. -/
def combineConjunction : QueryResult → QueryResult → QueryResult
  | ff, _ => ff
  | _, ff => ff
  | tt, tt => tt
  | a, b => combineIndeterminate a b

/-- `combine_disjunction` (reasoning.rs:205): `True` if either operand is `True`; `False` if
    both are `False`; otherwise the indeterminate combination. -/
def combineDisjunction : QueryResult → QueryResult → QueryResult
  | tt, _ => tt
  | _, tt => tt
  | ff, ff => ff
  | a, b => combineIndeterminate a b

/-- `negate_result` (reasoning.rs:228): NAF negation. `¬False = True` is a successful
    closed-world conclusion; negating a non-definitive sub-goal yields `Unknown(NafDependent)`;
    `ResourceExceeded` is polarity-independent. -/
def negateResult : QueryResult → QueryResult
  | tt => ff
  | ff => tt
  | unknown _ => unknown UnknownReason.nafDependent
  | resourceExceeded k => resourceExceeded k

/- ──────────────────────────────────────────────────────────────────────────
   1. The historical bug, as named regressions (instances of the soundness
      characterization below, pinned separately to match the Rust regression tests).
   ────────────────────────────────────────────────────────────────────────── -/

/-- `True ∧ Unknown = Unknown` (right operand). The exact bug: a definitive-True operand
    must NOT swallow a non-definitive sibling. -/
theorem conj_true_unknown_right (r : UnknownReason) :
    combineConjunction tt (unknown r) = unknown r := rfl

/-- `Unknown ∧ True = Unknown` (left operand). -/
theorem conj_unknown_true_left (r : UnknownReason) :
    combineConjunction (unknown r) tt = unknown r := rfl

/-- `False ∨ Unknown = Unknown` (right operand) — the disjunction side of the same bug. -/
theorem disj_false_unknown_right (r : UnknownReason) :
    combineDisjunction ff (unknown r) = unknown r := rfl

/-- `Unknown ∨ False = Unknown` (left operand). -/
theorem disj_unknown_false_left (r : UnknownReason) :
    combineDisjunction (unknown r) ff = unknown r := rfl

/- ──────────────────────────────────────────────────────────────────────────
   2. Soundness characterization: the combiner outputs a definitive verdict in EXACTLY
      the classically-correct situations. No fabrication, no swallowing.
   ────────────────────────────────────────────────────────────────────────── -/

/-- Conjunction is `True` iff both operands are `True`. -/
theorem conj_true_iff (a b : QueryResult) :
    combineConjunction a b = tt ↔ a = tt ∧ b = tt := by
  cases a <;> cases b <;> simp [combineConjunction, combineIndeterminate]

/-- Conjunction is `False` iff some operand is `False`. -/
theorem conj_false_iff (a b : QueryResult) :
    combineConjunction a b = ff ↔ a = ff ∨ b = ff := by
  cases a <;> cases b <;> simp [combineConjunction, combineIndeterminate]

/-- Disjunction is `True` iff some operand is `True`. -/
theorem disj_true_iff (a b : QueryResult) :
    combineDisjunction a b = tt ↔ a = tt ∨ b = tt := by
  cases a <;> cases b <;> simp [combineDisjunction, combineIndeterminate]

/-- Disjunction is `False` iff both operands are `False`. -/
theorem disj_false_iff (a b : QueryResult) :
    combineDisjunction a b = ff ↔ a = ff ∧ b = ff := by
  cases a <;> cases b <;> simp [combineDisjunction, combineIndeterminate]

/-- Indeterminacy propagation (corollary): a non-definitive conjunction means at least one
    operand was non-definitive — definite inputs are never turned indefinite, and (with the
    iffs above) an indefinite operand is never silently turned definite. -/
theorem conj_nondefinitive (a b : QueryResult)
    (h : isDefinitive (combineConjunction a b) = false) :
    isDefinitive a = false ∨ isDefinitive b = false := by
  cases a <;> cases b <;>
    simp_all [combineConjunction, combineIndeterminate, isDefinitive]

theorem disj_nondefinitive (a b : QueryResult)
    (h : isDefinitive (combineDisjunction a b) = false) :
    isDefinitive a = false ∨ isDefinitive b = false := by
  cases a <;> cases b <;>
    simp_all [combineDisjunction, combineIndeterminate, isDefinitive]

/- ──────────────────────────────────────────────────────────────────────────
   3. Precedence in the indeterminate region: ResourceExceeded outranks Unknown,
      left operand wins ties.
   ────────────────────────────────────────────────────────────────────────── -/

/-- A left `ResourceExceeded` always wins (carries its own kind). -/
theorem indet_re_left (k : ResourceKind) (b : QueryResult) :
    combineIndeterminate (resourceExceeded k) b = resourceExceeded k := rfl

/-- A right `ResourceExceeded` wins when the left operand is not itself `ResourceExceeded`. -/
theorem indet_re_right (a : QueryResult) (k : ResourceKind)
    (h : ∀ k', a ≠ resourceExceeded k') :
    combineIndeterminate a (resourceExceeded k) = resourceExceeded k := by
  cases a <;> simp_all [combineIndeterminate]

/-- The carried reason is LEFT-biased, so the combiner is NOT commutative on the reason
    (only on the verdict class — see `conj_vclass_comm`). Concrete witness. -/
theorem indet_left_biased :
    combineIndeterminate (unknown UnknownReason.cycleCut) (unknown UnknownReason.nonFinite)
      ≠ combineIndeterminate (unknown UnknownReason.nonFinite) (unknown UnknownReason.cycleCut) := by
  decide

/-- But And IS commutative on the verdict class. -/
theorem conj_vclass_comm (a b : QueryResult) :
    vclass (combineConjunction a b) = vclass (combineConjunction b a) := by
  cases a <;> cases b <;> rfl

/-- And so is Or. -/
theorem disj_vclass_comm (a b : QueryResult) :
    vclass (combineDisjunction a b) = vclass (combineDisjunction b a) := by
  cases a <;> cases b <;> rfl

/- ──────────────────────────────────────────────────────────────────────────
   4. Negation (NAF).
   ────────────────────────────────────────────────────────────────────────── -/

theorem neg_true : negateResult tt = ff := rfl
theorem neg_false : negateResult ff = tt := rfl
theorem neg_unknown (r : UnknownReason) :
    negateResult (unknown r) = unknown UnknownReason.nafDependent := rfl
theorem neg_re (k : ResourceKind) :
    negateResult (resourceExceeded k) = resourceExceeded k := rfl

/-- Negation never fabricates a verdict: a non-definitive input stays non-definitive. -/
theorem neg_preserves_indefinite (a : QueryResult)
    (h : isDefinitive a = false) : isDefinitive (negateResult a) = false := by
  cases a <;> simp_all [negateResult, isDefinitive]

/-- Negation is involutive on the definitive verdicts. -/
theorem neg_neg_true : negateResult (negateResult tt) = tt := rfl
theorem neg_neg_false : negateResult (negateResult ff) = ff := rfl

/-- ...but NOT involutive on `Unknown`: the reason collapses to `NafDependent` and stays
    there (the documented behavior, not an oversight). -/
theorem neg_not_involutive_on_unknown :
    negateResult (negateResult (unknown UnknownReason.cycleCut))
      = unknown UnknownReason.nafDependent := rfl

end Nibli
