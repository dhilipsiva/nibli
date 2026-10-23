import Aeneas

/- Finite-map and iterator contracts for candidate library bindings. Entries
   retain an arbitrary input order: the model does not assume that HashMap
   iteration is sorted. These are library specifications, not proofs of Rust's
   hashing, allocation or table implementation. -/
namespace NibliSelfCheck.StdMaps

open Aeneas Aeneas.Std

def UniqueKeys {K V : Type} (entries : List (K × V)) : Prop :=
  (entries.map Prod.fst).Nodup

def lookupValue {K V : Type} [DecidableEq K] (key : K) : List (K × V) → Option V
  | [] => none
  | (current, value) :: rest => if current = key then some value else lookupValue key rest

/-- Updating an existing key preserves that key and its position. -/
def putValue {K V : Type} [DecidableEq K] (key : K) (value : V) : List (K × V) → List (K × V)
  | [] => [(key, value)]
  | (current, old) :: rest =>
    if current = key then (current, value) :: rest else (current, old) :: putValue key value rest

def lookup {K V : Type} (test : K → Result Bool) : List (K × V) → Result (Option V)
  | [] => .ok none
  | (key, value) :: rest => do
    let found ← test key
    if found then .ok (some value) else lookup test rest

def insert {K V : Type} (equal : K → K → Result Bool) (key : K) (value : V) :
    List (K × V) → Result (Option V × List (K × V))
  | [] => .ok (none, [(key, value)])
  | (current, old) :: rest => do
    let found ← equal current key
    if found then .ok (some old, (current, value) :: rest)
    else
      let (previous, updated) ← insert equal key value rest
      .ok (previous, (current, old) :: updated)

/-- A borrowed map iterator visits precisely its stored enumeration. No key
    ordering is required by this operation or its contract. -/
def next {T : Type} (remaining : List T) : Result (Option T × List T) :=
  match remaining with
  | [] => .ok (none, [])
  | first :: rest => .ok (some first, rest)

theorem lookup_value_none_iff {K V : Type} [DecidableEq K] (key : K) (entries : List (K × V)) :
    lookupValue key entries = none ↔ key ∉ entries.map Prod.fst := by
  induction entries with
  | nil => simp [lookupValue]
  | cons entry rest ih =>
    rcases entry with ⟨current, value⟩
    by_cases h : current = key
    · simp [lookupValue, h]
    · simp [lookupValue, h, Ne.symm h, ih]

theorem lookup_value_some_iff {K V : Type} [DecidableEq K] (key : K) (value : V)
    (entries : List (K × V)) (hunique : UniqueKeys entries) :
    lookupValue key entries = some value ↔ (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookupValue]
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    have hkeys : current ∉ rest.map Prod.fst ∧ UniqueKeys rest := by
      simpa [UniqueKeys] using hunique
    by_cases h : current = key
    · subst current
      have hmissing : (key, value) ∉ rest := by
        intro hmember
        exact hkeys.1 (List.mem_map_of_mem hmember)
      simp [lookupValue, hmissing, eq_comm]
    · simpa [lookupValue, h, Ne.symm h] using ih hkeys.2

theorem lookup_eq {K V : Type} [DecidableEq K] (test : K → Result Bool) (key : K)
    (hmatch : ∀ current, test current = .ok (decide (current = key))) (entries : List (K × V)) :
    lookup test entries = .ok (lookupValue key entries) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨current, value⟩
    simp only [lookup, hmatch]
    by_cases h : current = key <;> simp [lookupValue, h, ih]

theorem insert_eq {K V : Type} [DecidableEq K] (equal : K → K → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (key : K) (value : V) (entries : List (K × V)) :
    insert equal key value entries = .ok (lookupValue key entries, putValue key value entries) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    simp only [insert, hequal]
    by_cases h : current = key <;> simp [h, lookupValue, putValue, ih]

theorem put_value_keys {K V : Type} [DecidableEq K] (key query : K) (value : V)
    (entries : List (K × V)) :
    query ∈ (putValue key value entries).map Prod.fst ↔ query = key ∨ query ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [putValue]
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    by_cases h : current = key
    · subst current
      simp [putValue]
    · simp [putValue, h, ih, or_left_comm]

theorem put_value_unique {K V : Type} [DecidableEq K] (key : K) (value : V)
    (entries : List (K × V)) (hunique : UniqueKeys entries) :
    UniqueKeys (putValue key value entries) := by
  induction entries with
  | nil => simp [UniqueKeys, putValue]
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    have hkeys : current ∉ rest.map Prod.fst ∧ UniqueKeys rest := by
      simpa [UniqueKeys] using hunique
    by_cases h : current = key
    · simpa [UniqueKeys, putValue, h] using hunique
    · simp only [putValue, h, ↓reduceIte, UniqueKeys, List.map_cons, List.nodup_cons]
      exact ⟨by simpa [put_value_keys] using And.intro h hkeys.1, ih hkeys.2⟩

theorem put_value_lookup {K V : Type} [DecidableEq K] (key query : K) (value : V)
    (entries : List (K × V)) :
    lookupValue query (putValue key value entries) =
      if query = key then some value else lookupValue query entries := by
  induction entries with
  | nil =>
    by_cases h : query = key
    · simp [putValue, lookupValue, h]
    · simp [putValue, lookupValue, h, Ne.symm h]
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    by_cases hcurrent : current = key <;> by_cases hquery : query = key <;>
      by_cases heq : current = query <;> simp_all [putValue, lookupValue]

theorem put_value_length {K V : Type} [DecidableEq K] (key : K) (value : V)
    (entries : List (K × V)) :
    (putValue key value entries).length = entries.length + if (lookupValue key entries).isSome then 0 else 1 := by
  induction entries with
  | nil => simp [putValue, lookupValue]
  | cons entry rest ih =>
    rcases entry with ⟨current, old⟩
    by_cases h : current = key
    · simp [putValue, lookupValue, h]
    · simp only [putValue, lookupValue, h, ↓reduceIte, List.length_cons, ih]
      omega

/-- Inserting a map binding returns its former value, changes only that key,
    preserves key uniqueness and grows exactly when the key was absent. -/
theorem insert_spec {K V : Type} [DecidableEq K] (equal : K → K → Result Bool)
    (hequal : ∀ left right, equal left right = .ok (decide (left = right)))
    (key : K) (value : V) (entries : List (K × V)) (hunique : UniqueKeys entries) :
    insert equal key value entries ⦃ result =>
      result.1 = lookupValue key entries ∧ UniqueKeys result.2 ∧
      (∀ query, lookupValue query result.2 = if query = key then some value else lookupValue query entries) ∧
      result.2.length = entries.length + if result.1.isSome then 0 else 1 ⦄ := by
  rw [insert_eq equal hequal key value entries]
  simp only [WP.spec_ok]
  exact ⟨by trivial, put_value_unique key value entries hunique,
    fun query => put_value_lookup key query value entries, put_value_length key value entries⟩

theorem next_spec {T : Type} (remaining : List T) :
    next remaining ⦃ result => match result.1 with
      | none => remaining = [] ∧ result.2 = []
      | some first => remaining = first :: result.2 ∧ result.2.length < remaining.length ⦄ := by
  cases remaining <;> simp [next]

theorem lookup_spec {K V : Type} [DecidableEq K] (test : K → Result Bool) (key : K)
    (hmatch : ∀ current, test current = .ok (decide (current = key)))
    (entries : List (K × V)) (hunique : UniqueKeys entries) :
    lookup test entries ⦃ result =>
      (∀ value, result = some value ↔ (key, value) ∈ entries) ∧
      (result = none ↔ key ∉ entries.map Prod.fst) ⦄ := by
  rw [lookup_eq test key hmatch entries]
  simp only [WP.spec_ok]
  exact ⟨fun value => lookup_value_some_iff key value entries hunique, lookup_value_none_iff key entries⟩

theorem lookup_value_order_independent {K V : Type} [DecidableEq K] (key : K)
    (left right : List (K × V)) (hleft : UniqueKeys left) (hright : UniqueKeys right)
    (hperm : left.Perm right) : lookupValue key left = lookupValue key right := by
  cases hvalue : lookupValue key left with
  | none =>
    have hmissing := (lookup_value_none_iff key left).mp hvalue
    have hmissing' : key ∉ right.map Prod.fst := by
      simpa only [(hperm.map Prod.fst).mem_iff] using hmissing
    exact ((lookup_value_none_iff key right).mpr hmissing').symm
  | some value =>
    have hmember := (lookup_value_some_iff key value left hleft).mp hvalue
    exact ((lookup_value_some_iff key value right hright).mpr (hperm.mem_iff.mp hmember)).symm

end NibliSelfCheck.StdMaps
