module
public import Aeneas
@[expose] public section

/- Element-count checks shared by candidate collection bindings. These checks
   express the extracted machine-word representation bound. Concrete allocator
   layout, capacity and host resource failures are separate obligations. -/
namespace NibliSelfCheck.StdBounded

open Aeneas Aeneas.Std

def checkedList {T : Type} (entries : List T) : Result (List T) :=
  if entries.length ≤ Usize.max then .ok entries else .fail .maximumSizeExceeded

def checkedSlice {T : Type} (entries : List T) : Result (Slice T) :=
  if h : entries.length ≤ Usize.max then .ok (.from entries h) else .fail .maximumSizeExceeded

def checkedLength {T : Type} (entries : List T) : Result Usize :=
  if h : entries.length ≤ Usize.max then .ok (UScalar.ofNatCore entries.length (by scalar_tac))
  else .fail .maximumSizeExceeded

def lessEqual {T : Type} (cmp : T → T → Result Ordering) (left right : T) : Result Bool := do
  let order ← cmp left right
  .ok (order != .gt)

theorem checked_list_spec {T : Type} (entries : List T) (h : entries.length ≤ Usize.max) :
    checkedList entries ⦃ result => result = entries ⦄ := by simp [checkedList, h]

theorem checked_slice_spec {T : Type} (entries : List T) (h : entries.length ≤ Usize.max) :
    checkedSlice entries ⦃ result => result.val = entries ⦄ := by simp [checkedSlice, h]

theorem checked_length_spec {T : Type} (entries : List T) (h : entries.length ≤ Usize.max) :
    checkedLength entries ⦃ result => result.val = entries.length ⦄ := by simp [checkedLength, h]

theorem checked_list_overflow {T : Type} (entries : List T) (h : Usize.max < entries.length) :
    checkedList entries = .fail .maximumSizeExceeded := by simp [checkedList, Nat.not_le.mpr h]

theorem checked_slice_overflow {T : Type} (entries : List T) (h : Usize.max < entries.length) :
    checkedSlice entries = .fail .maximumSizeExceeded := by simp [checkedSlice, Nat.not_le.mpr h]

theorem checked_length_overflow {T : Type} (entries : List T) (h : Usize.max < entries.length) :
    checkedLength entries = .fail .maximumSizeExceeded := by simp [checkedLength, Nat.not_le.mpr h]

theorem less_equal_eq {T : Type} (cmp : T → T → Result Ordering) (left right : T) (order : Ordering)
    (h : cmp left right = .ok order) : lessEqual cmp left right = .ok (order != .gt) := by
  simp [lessEqual, h]

end NibliSelfCheck.StdBounded
