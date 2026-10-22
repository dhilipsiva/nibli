import Input.Funs

/- These theorems refer directly to freshly extracted production definitions.
   They establish the verdict algebra, not compiler/checker equivalence or the
   correctness of the callers, evaluator, Rust compiler, or extraction tools. -/
namespace NibliSelfCheck

open Aeneas.Std nibli_reason nibli_types.logic

theorem conjunction_total (a b : QueryResult) :
    ∃ result, reasoning.combine_conjunction a b = .ok result := by
  cases a <;> cases b <;>
    simp [reasoning.combine_conjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem disjunction_total (a b : QueryResult) :
    ∃ result, reasoning.combine_disjunction a b = .ok result := by
  cases a <;> cases b <;>
    simp [reasoning.combine_disjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem negation_total (a : QueryResult) :
    ∃ result, reasoning.negate_result a = .ok result := by
  cases a <;> exact ⟨_, rfl⟩

theorem conjunction_true_iff (a b : QueryResult) :
    reasoning.combine_conjunction a b = .ok .True ↔ a = .True ∧ b = .True := by
  cases a <;> cases b <;>
    simp [reasoning.combine_conjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem conjunction_false_iff (a b : QueryResult) :
    reasoning.combine_conjunction a b = .ok .False ↔ a = .False ∨ b = .False := by
  cases a <;> cases b <;>
    simp [reasoning.combine_conjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem disjunction_true_iff (a b : QueryResult) :
    reasoning.combine_disjunction a b = .ok .True ↔ a = .True ∨ b = .True := by
  cases a <;> cases b <;>
    simp [reasoning.combine_disjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem disjunction_false_iff (a b : QueryResult) :
    reasoning.combine_disjunction a b = .ok .False ↔ a = .False ∧ b = .False := by
  cases a <;> cases b <;>
    simp [reasoning.combine_disjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem conjunction_true_identity (a : QueryResult) :
    reasoning.combine_conjunction .True a = .ok a ∧
    reasoning.combine_conjunction a .True = .ok a := by
  cases a <;>
    simp [reasoning.combine_conjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem disjunction_false_identity (a : QueryResult) :
    reasoning.combine_disjunction .False a = .ok a ∧
    reasoning.combine_disjunction a .False = .ok a := by
  cases a <;>
    simp [reasoning.combine_disjunction, QueryResult.is_false,
      QueryResult.is_true, reasoning.combine_indeterminate]

theorem resource_precedes_unknown (kind : ResourceKind) (reason : UnknownReason) :
    reasoning.combine_conjunction (.ResourceExceeded kind) (.Unknown reason) =
      .ok (.ResourceExceeded kind) ∧
    reasoning.combine_conjunction (.Unknown reason) (.ResourceExceeded kind) =
      .ok (.ResourceExceeded kind) ∧
    reasoning.combine_disjunction (.ResourceExceeded kind) (.Unknown reason) =
      .ok (.ResourceExceeded kind) ∧
    reasoning.combine_disjunction (.Unknown reason) (.ResourceExceeded kind) =
      .ok (.ResourceExceeded kind) := by
  simp [reasoning.combine_conjunction, reasoning.combine_disjunction,
    QueryResult.is_false, QueryResult.is_true, reasoning.combine_indeterminate]

theorem indeterminate_reasons_left_biased (a b : UnknownReason) (x y : ResourceKind) :
    reasoning.combine_conjunction (.Unknown a) (.Unknown b) = .ok (.Unknown a) ∧
    reasoning.combine_disjunction (.Unknown a) (.Unknown b) = .ok (.Unknown a) ∧
    reasoning.combine_conjunction (.ResourceExceeded x) (.ResourceExceeded y) =
      .ok (.ResourceExceeded x) ∧
    reasoning.combine_disjunction (.ResourceExceeded x) (.ResourceExceeded y) =
      .ok (.ResourceExceeded x) := by
  simp [reasoning.combine_conjunction, reasoning.combine_disjunction,
    QueryResult.is_false, QueryResult.is_true, reasoning.combine_indeterminate]

theorem negation_true_iff (a : QueryResult) :
    reasoning.negate_result a = .ok .True ↔ a = .False := by
  cases a <;> simp [reasoning.negate_result]

theorem negation_false_iff (a : QueryResult) :
    reasoning.negate_result a = .ok .False ↔ a = .True := by
  cases a <;> simp [reasoning.negate_result]

theorem negation_preserves_indeterminacy (reason : UnknownReason) (kind : ResourceKind) :
    reasoning.negate_result (.Unknown reason) = .ok (.Unknown .NafDependent) ∧
    reasoning.negate_result (.ResourceExceeded kind) = .ok (.ResourceExceeded kind) := by
  exact ⟨rfl, rfl⟩

end NibliSelfCheck
