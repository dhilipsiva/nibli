module
public import Aeneas
public import Mathlib.Data.List.Sort
@[expose] public section

/- Candidate set and sort specifications. Their list representation records
   observable membership and ordering, not the implementation of Rust trees,
   hash tables or sorting routines. Comparisons remain monadic so failed or
   nonterminating user comparisons are not silently turned into successful ones. -/
namespace NibliSelfCheck.StdSetsSort

open Aeneas Aeneas.Std

def contains {T : Type} (test : T → Result Bool) : List T → Result Bool
  | [] => .ok false
  | first :: rest => do
    let found ← test first
    if found then .ok true else contains test rest

def setInsert {T : Type} (equal : T → T → Result Bool) (value : T) (entries : List T) :
    Result (Bool × List T) := do
  let found ← contains (fun current => equal current value) entries
  if found then .ok (false, entries) else .ok (true, entries ++ [value])

/-- Inserting before equal items makes this the stable sort representative. -/
def orderedInsert {T : Type} (le : T → T → Result Bool) (value : T) : List T → Result (List T)
  | [] => .ok [value]
  | first :: rest => do
    let before ← le value first
    if before then .ok (value :: first :: rest)
    else
      let updated ← orderedInsert le value rest
      .ok (first :: updated)

def sort {T : Type} (le : T → T → Result Bool) : List T → Result (List T)
  | [] => .ok []
  | first :: rest => do
    let sorted ← sort le rest
    orderedInsert le first sorted

def orderedSetInsert {T : Type} (equal le : T → T → Result Bool)
    (value : T) (entries : List T) : Result (Bool × List T) := do
  let found ← contains (fun current => equal current value) entries
  if found then .ok (false, entries)
  else
    let updated ← orderedInsert le value entries
    .ok (true, updated)

theorem contains_eq {T : Type} [DecidableEq T] (test : T → Result Bool) (value : T)
    (htest : ∀ current, test current = .ok (decide (current = value))) (entries : List T) :
    contains test entries = .ok (decide (value ∈ entries)) := by
  induction entries with
  | nil => simp [contains]
  | cons first rest ih =>
    simp only [contains, htest]
    by_cases h : first = value
    · simp [h]
    · simp [h, Ne.symm h, ih]

theorem set_insert_eq {T : Type} [DecidableEq T] (equal : T → T → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (value : T) (entries : List T) :
    setInsert equal value entries =
      .ok (if value ∈ entries then (false, entries) else (true, entries ++ [value])) := by
  simp only [setInsert, contains_eq _ value (fun current => hequal current value)]
  by_cases h : value ∈ entries <;> simp [h]

theorem set_insert_spec {T : Type} [DecidableEq T] (equal : T → T → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (value : T) (entries : List T) (hunique : entries.Nodup) :
    setInsert equal value entries ⦃ result => result.2.Nodup ∧
      (result.1 = true ↔ value ∉ entries) ∧
      (∀ query, query ∈ result.2 ↔ query = value ∨ query ∈ entries) ∧
      result.2.length = entries.length + if result.1 then 1 else 0 ⦄ := by
  rw [set_insert_eq equal hequal value entries]
  by_cases h : value ∈ entries
  · simp only [h, ↓reduceIte, WP.spec_ok]
    refine ⟨hunique, by simp, ?_, by simp⟩
    intro query
    constructor
    · exact Or.inr
    · rintro (rfl | hquery)
      · exact h
      · exact hquery
  · simp only [h, ↓reduceIte, WP.spec_ok]
    refine ⟨?_, by simp, ?_, by simp⟩
    · have hnot : ∀ current ∈ entries, current ≠ value := by
        intro current hcurrent heq
        exact h (heq ▸ hcurrent)
      simpa [List.nodup_append] using And.intro hunique hnot
    · intro query
      simp [or_comm]

theorem ordered_insert_eq {T : Type} (r : T → T → Prop) [DecidableRel r]
    (le : T → T → Result Bool) (hle : ∀ left right, le left right = .ok (decide (r left right)))
    (value : T) (entries : List T) :
    orderedInsert le value entries = .ok (List.orderedInsert r value entries) := by
  induction entries with
  | nil => simp [orderedInsert]
  | cons first rest ih =>
    simp only [orderedInsert, hle]
    by_cases h : r value first <;> simp [h, List.orderedInsert_cons, ih]

theorem sort_eq {T : Type} (r : T → T → Prop) [DecidableRel r]
    (le : T → T → Result Bool) (hle : ∀ left right, le left right = .ok (decide (r left right)))
    (entries : List T) : sort le entries = .ok (List.insertionSort r entries) := by
  induction entries with
  | nil => simp [sort]
  | cons first rest ih =>
    simp [sort, ih, ordered_insert_eq r le hle, List.insertionSort_cons]

/-- Sorting preserves every element with its multiplicity and produces an
    ordered sequence. The comparator's totality and transitivity are explicit. -/
theorem sort_spec {T : Type} (r : T → T → Prop) [DecidableRel r] [Std.Total r] [IsTrans T r]
    (le : T → T → Result Bool) (hle : ∀ left right, le left right = .ok (decide (r left right)))
    (entries : List T) : sort le entries ⦃ result =>
      result.Perm entries ∧ result.Pairwise r ∧ result.length = entries.length ⦄ := by
  rw [sort_eq r le hle entries]
  simp only [WP.spec_ok]
  exact ⟨List.perm_insertionSort r entries, List.pairwise_insertionSort r entries,
    List.length_insertionSort r entries⟩

theorem ordered_set_insert_eq {T : Type} [DecidableEq T] (r : T → T → Prop) [DecidableRel r]
    (equal le : T → T → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (hle : ∀ left right, le left right = .ok (decide (r left right)))
    (value : T) (entries : List T) : orderedSetInsert equal le value entries =
      .ok (if value ∈ entries then (false, entries) else (true, List.orderedInsert r value entries)) := by
  simp only [orderedSetInsert, contains_eq _ value (fun current => hequal current value)]
  by_cases h : value ∈ entries <;> simp [h, ordered_insert_eq r le hle]

theorem ordered_set_insert_spec {T : Type} [DecidableEq T] (r : T → T → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans T r] (equal le : T → T → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (hle : ∀ left right, le left right = .ok (decide (r left right)))
    (value : T) (entries : List T) (hunique : entries.Nodup) (hsorted : entries.Pairwise r) :
    orderedSetInsert equal le value entries ⦃ result => result.2.Nodup ∧ result.2.Pairwise r ∧
      (result.1 = true ↔ value ∉ entries) ∧
      (∀ query, query ∈ result.2 ↔ query = value ∨ query ∈ entries) ∧
      result.2.length = entries.length + if result.1 then 1 else 0 ⦄ := by
  rw [ordered_set_insert_eq r equal le hequal hle value entries]
  by_cases h : value ∈ entries
  · simp only [h, ↓reduceIte, WP.spec_ok]
    refine ⟨hunique, hsorted, by simp, ?_, by simp⟩
    intro query
    constructor
    · exact Or.inr
    · rintro (rfl | hquery)
      · exact h
      · exact hquery
  · simp only [h, ↓reduceIte, WP.spec_ok]
    refine ⟨?_, hsorted.orderedInsert value entries, by simp, ?_, ?_⟩
    · exact (List.perm_orderedInsert r value entries).nodup_iff.mpr (by simp [h, hunique])
    · intro query
      exact List.mem_orderedInsert r
    · simp [List.orderedInsert_length]

end NibliSelfCheck.StdSetsSort
