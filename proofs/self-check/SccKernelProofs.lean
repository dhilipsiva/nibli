import SccKernel.Funs

/- Proofs about the extracted production traversal. These local obligations
   are building blocks for SCC correctness, not a proof of the complete
   traversal or the predicate-name adapter. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow
open nibli_reason.dependency_graph

theorem pop_done (state : alloc.vec.Vec NodeState) (stack : Slice Usize)
    (length root : Usize) (component : alloc.vec.Vec Usize) :
    pop_component_loop.body stack root state length component true =
      .ok (.done (state, length, component)) := by
  simp [pop_component_loop.body]

theorem pop_step (state : alloc.vec.Vec NodeState) (stack : Slice Usize)
    (length root member : Usize) (component : alloc.vec.Vec Usize)
    (entry : NodeState)
    (hpositive : 0 < length.val)
    (htop : stack.val[length.val - 1]? = some member)
    (hentry : state.val[member.val]? = some entry)
    (hcapacity : component.length < Usize.max) :
    pop_component_loop.body stack root state length component false ⦃ result =>
      ∃ remaining output,
        remaining.val + 1 = length.val ∧
        output.val = component.val ++ [member] ∧
        result = .cont (state.set member { entry with on_stack := false },
          remaining, output, decide (member = root)) ⦄ := by
  have htop_bound : length.val - 1 < stack.length := by
    exact List.getElem?_eq_some_iff.mp htop |>.1
  have hentry_bound : member.val < state.length := by
    exact List.getElem?_eq_some_iff.mp hentry |>.1
  unfold pop_component_loop.body
  simp only [Bool.false_eq_true, ↓reduceIte]
  step as ⟨remaining, hremaining⟩
  step as ⟨top, htop'⟩
  have htop_eq : top = member := by grind
  subst top
  step as ⟨old, back, hold, hback⟩
  step as ⟨output, houtput⟩
  have hentry_value : state.val[member.val] = entry :=
    (List.getElem?_eq_some_iff.mp hentry).2
  have hold_eq : old = entry := by simpa [htop_eq, hentry_value] using hold
  refine ⟨remaining, output, by omega, ?_, ?_⟩
  · simpa [htop_eq] using houtput
  · simp [htop_eq, hback, hold_eq]

private theorem suffix_step {α : Type} (items : List α) (length cursor : Nat)
    (member : α) (hpositive : 0 < cursor) (hcursor : cursor ≤ length)
    (hlength : length ≤ items.length) (hmember : items[cursor - 1]? = some member) :
    ((items.take length).drop (cursor - 1)).reverse =
      ((items.take length).drop cursor).reverse ++ [member] := by
  have hbound : cursor - 1 < (items.take length).length := by
    simp only [List.length_take]
    omega
  have hlookup : (items.take length)[cursor - 1]? = some member := by
    rw [List.getElem?_take_of_lt (by omega)]
    exact hmember
  have hvalue := (List.getElem?_eq_some_iff.mp hlookup).2
  have hcursor_eq : cursor - 1 + 1 = cursor := by omega
  rw [List.drop_eq_getElem_cons hbound, hvalue, hcursor_eq, List.reverse_cons]

theorem pop_component_total (state : alloc.vec.Vec NodeState) (stack : Slice Usize)
    (length root : Usize) (position : Nat)
    (hposition : position < length.val)
    (hlength : length.val ≤ stack.length)
    (hroot : stack.val[position]? = some root)
    (hlast : ∀ i, position < i → i < length.val → stack.val[i]? ≠ some root)
    (htargets : ∀ i, i < length.val → ∀ member,
      stack.val[i]? = some member → member.val < state.length) :
    pop_component state stack length root ⦃ updated remaining output =>
      updated.length = state.length ∧ remaining.val = position ∧
      output.length + position = length.val ∧
      output.val = ((stack.val.take length.val).drop position).reverse ⦄ := by
  let inv := fun (current : alloc.vec.Vec NodeState × Usize × alloc.vec.Vec Usize × Bool) =>
    match current with
    | (updated, remaining, output, complete) =>
      updated.length = state.length ∧ position ≤ remaining.val ∧
      remaining.val ≤ length.val ∧ output.length + remaining.val = length.val ∧
      (complete = true ↔ remaining.val = position) ∧
      output.val = ((stack.val.take length.val).drop remaining.val).reverse
  unfold pop_component pop_component_loop
  apply loop.spec_decr_nat (measure := fun (_, remaining, _, _) => remaining.val)
    (inv := inv)
  · rintro ⟨updated, remaining, output, complete⟩ hinv
    rcases hinv with ⟨hsize, hlow, hhigh, hcount, hcomplete, horder⟩
    dsimp only
    cases complete with
    | true =>
      rw [pop_done]
      simp only [WP.spec_ok]
      have heq := hcomplete.mp rfl
      exact ⟨hsize, heq, by omega, by simpa [heq] using horder⟩
    | false =>
      have hpositive : 0 < remaining.val := by simp at hcomplete; omega
      have habove : position < remaining.val := by simp at hcomplete; omega
      have hbound : remaining.val - 1 < stack.val.length := by
        change remaining.val - 1 < stack.length
        omega
      let member := stack.val[remaining.val - 1]'hbound
      have hmember : stack.val[remaining.val - 1]? = some member := by simp [member]
      have hstate : member.val < updated.val.length := by
        change member.val < updated.length
        rw [hsize]
        exact htargets _ (by omega) member hmember
      let entry := updated.val[member.val]'hstate
      have hentry : updated.val[member.val]? = some entry := by simp [entry]
      have hcapacity : output.length < Usize.max := by scalar_tac
      apply WP.spec_mono (pop_step updated stack remaining root member output entry
        hpositive hmember hentry hcapacity)
      rintro result ⟨next, appended, hnext, happended, rfl⟩
      have hnew_length : appended.length = output.length + 1 := by
        simp [alloc.vec.Vec.length, happended]
      have hnew_order : appended.val =
          ((stack.val.take length.val).drop next.val).reverse := by
        have hnext_eq : next.val = remaining.val - 1 := by omega
        rw [hnext_eq, suffix_step stack.val length.val remaining.val member
          hpositive hhigh hlength hmember, happended, horder]
      have heq : member = root ↔ next.val = position := by
        constructor
        · intro equal
          by_contra different
          have habove' : position < remaining.val - 1 := by omega
          apply hlast _ habove' (by omega)
          simpa [equal] using hmember
        · intro equal
          have hindex : remaining.val - 1 = position := by omega
          rw [hindex] at hmember
          exact Option.some.inj (hmember.symm.trans hroot)
      change inv (_, next, appended, decide (member = root)) ∧ next.val < remaining.val
      constructor
      · dsimp only [inv]
        refine ⟨?_, by omega, by omega, by omega, ?_, hnew_order⟩
        · simpa using hsize
        · simpa using heq
      · omega
  · dsimp only [inv]
    refine ⟨rfl, Nat.le_of_lt hposition, Nat.le_refl _, ?_, ?_, ?_⟩
    · simp [alloc.vec.Vec.new]
    · simp only [Bool.false_eq_true, false_iff]
      omega
    · simp [alloc.vec.Vec.new]

end NibliSelfCheck.Scc
