import SccKernel.Funs

/- Contracts for the production named negative-edge scan, using the reviewed
   standard-library boundary. The graph adapter and evaluator are separate. -/
namespace NibliSelfCheck.Stratification

open Aeneas Aeneas.Std
open nibli_reason

local instance : Membership String
    (std.collections.hash.set.HashSet String std.hash.random.RandomState alloc.alloc.Global) :=
  inferInstanceAs (Membership String (List String))

abbrev NamedGraph := List (String × alloc.vec.Vec (String × Bool))

def remaining {T : Type} (iter : core.slice.iter.Iter T) : List T :=
  iter.slice.val.drop iter.i

theorem slice_next_spec {T : Type} (iter : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next iter ⦃ result =>
      match result.1 with
      | none => remaining iter = []
      | some value => remaining iter = value :: remaining result.2 ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  next h =>
    simp only [WP.spec_ok]
    exact List.drop_eq_getElem_cons h
  next h =>
    simp only [WP.spec_ok]
    exact List.drop_eq_nil_iff.mpr (Nat.le_of_not_lt h)

theorem vec_next_spec {T : Type} (iter : alloc.vec.into_iter.IntoIter T) :
    alloc.vec.into_iter.IteratorIntoIter.next iter ⦃ result =>
      match result.1 with
      | none => iter.val = []
      | some value => iter.val = value :: result.2.val ⦄ := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split <;> simp_all

theorem string_set_contains (members : List String) (value : String) :
    std.collections.hash.set.HashSet.contains (A := alloc.alloc.Global) alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (core.borrow.Borrow.Blanket String) alloc.string.String.Insts.CoreHashHash
      alloc.string.String.Insts.CoreCmpEq members value = .ok (decide (value ∈ members)) := by
  apply StdSetsSort.contains_eq
  intro current
  simp [core.borrow.Borrow.Blanket.borrow,
    alloc.string.String.Insts.CoreCmpPartialEqString.eq, StdStrings.equal]

theorem string_map_get (graph : NamedGraph) (vertex : String) :
    std.collections.hash.map.HashMap.get (A := alloc.alloc.Global) alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (core.borrow.Borrow.Blanket String) alloc.string.String.Insts.CoreHashHash
      alloc.string.String.Insts.CoreCmpEq graph vertex = .ok (StdMaps.lookupValue vertex graph) := by
  apply StdMaps.lookup_eq
  intro current
  simp [core.borrow.Borrow.Blanket.borrow,
    alloc.string.String.Insts.CoreCmpPartialEqString.eq, StdStrings.equal]

theorem string_set_insert (members : List String) (value : String)
    (hsize : members.length + 1 ≤ Usize.max) (hunique : members.Nodup) :
    std.collections.hash.set.HashSet.insert (A := alloc.alloc.Global) alloc.string.String.Insts.CoreCmpEq
      alloc.string.String.Insts.CoreHashHash
      std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher members value
      ⦃ result => result.2.Nodup ∧
        (∀ query, query ∈ result.2 ↔ query = value ∨ query ∈ members) ∧
        result.2.length ≤ members.length + 1 ⦄ := by
  unfold std.collections.hash.set.HashSet.insert
  simp only [std.collections.hash.set.HashSet, alloc.string.String.Insts.CoreCmpPartialEqString.eq]
  step with StdSetsSort.set_insert_spec StdStrings.equal (fun _ _ => rfl) value members hunique
    as ⟨fresh, updated, hunique, _, hmembers, hlength⟩
  have hlength : updated.length ≤ members.length + 1 := by
    rw [hlength]
    split <;> omega
  step with StdBounded.checked_list_spec updated (by omega) as ⟨actual, hactual⟩
  subst actual
  exact ⟨hunique, hmembers, hlength⟩

theorem build_members_total (iter : core.slice.iter.Iter String) (members : List String)
    (hsize : members.length + (remaining iter).length ≤ Usize.max)
    (hunique : members.Nodup)
    (hfits : ∀ vertex ∈ remaining iter, StdStrings.Fits vertex) :
    rules.check_stratification_loop0_loop0 iter members ⦃ result => result.Nodup ∧
      (∀ query, query ∈ result ↔ query ∈ members ∨ query ∈ remaining iter) ⦄ := by
  unfold rules.check_stratification_loop0_loop0
  apply loop.spec_decr_nat (measure := fun state => (remaining state.1).length)
    (inv := fun state => state.2.Nodup ∧
      state.2.length + (remaining state.1).length ≤ Usize.max ∧
      (∀ vertex ∈ remaining state.1, StdStrings.Fits vertex) ∧
      (∀ query, query ∈ state.2 ∨ query ∈ remaining state.1 ↔
        query ∈ members ∨ query ∈ remaining iter))
  · rintro ⟨current, collected⟩ ⟨hunique, hsize, hfits, hmembers⟩
    change List String at collected
    dsimp only at hunique hsize hfits hmembers
    unfold rules.check_stratification_loop0_loop0.body
    step with slice_next_spec current as ⟨value, next, hnext⟩
    cases value with
    | none =>
      simp only [WP.spec_ok]
      exact ⟨hunique, by simpa [hnext] using hmembers⟩
    | some vertex =>
      have hname := hfits vertex (by simp [hnext])
      have hrest : ∀ vertex ∈ remaining next, StdStrings.Fits vertex := by
        intro vertex hname
        exact hfits vertex (by simp [hnext, hname])
      have hlength : (remaining current).length = (remaining next).length + 1 := by simp [hnext]
      unfold alloc.string.String.Insts.CoreCloneClone.clone
      step with StdStrings.clone_spec vertex hname as ⟨actual, hactual⟩
      subst actual
      step with string_set_insert collected vertex (by omega) hunique
        as ⟨fresh, updated, hunique, hupdated, hbound⟩
      refine ⟨hunique, by omega, hrest, ?_, by omega⟩
      intro query
      rw [hupdated, ← hmembers, hnext]
      simp only [List.mem_cons]
      tauto
  · exact ⟨hunique, hsize, hfits, fun _ => Iff.rfl⟩

def diagnosticPrefix := "Unstratifiable negation: strongly-connected component containing '"

def diagnostic (source target : String) : String :=
  diagnosticPrefix ++ source ++ "' -> '" ++ target ++ "' (negative)"

theorem diagnostic_spec {T : Type} (source target : String)
    (hfits : StdStrings.Fits (diagnostic source target))
    (continuation : String → Result T) (post : T → Prop)
    (hpost : continuation (diagnostic source target) ⦃ post ⦄) :
    (do
      let message ← alloc.string.String.Insts.CoreConvertFromShared0Str.from (toStr diagnosticPrefix)
      let sourceView ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref source
      let message ← alloc.string.String.push_str message sourceView
      let message ← alloc.string.String.push_str message (toStr "' -> '")
      let targetView ← alloc.string.String.Insts.CoreOpsDerefDerefStr.deref target
      let message ← alloc.string.String.push_str message targetView
      let message ← alloc.string.String.push_str message (toStr "' (negative)")
      continuation message) ⦃ post ⦄ := by
  have hbound := hfits
  unfold StdStrings.Fits diagnostic at hbound
  simp only [String.utf8ByteSize_append] at hbound
  have hprefix : StdStrings.Fits diagnosticPrefix := by unfold StdStrings.Fits; omega
  have hsource : StdStrings.Fits source := by unfold StdStrings.Fits; omega
  have htarget : StdStrings.Fits target := by unfold StdStrings.Fits; omega
  have hfirst : StdStrings.Fits (diagnosticPrefix ++ source) := by
    simp only [StdStrings.Fits, String.utf8ByteSize_append]; omega
  have hsecond : StdStrings.Fits (diagnosticPrefix ++ source ++ "' -> '") := by
    simp only [StdStrings.Fits, String.utf8ByteSize_append]; omega
  have hthird : StdStrings.Fits (diagnosticPrefix ++ source ++ "' -> '" ++ target) := by
    simp only [StdStrings.Fits, String.utf8ByteSize_append]; omega
  have hprefixView : StdStrings.Represents (toStr diagnosticPrefix) diagnosticPrefix := by
    unfold StdStrings.Represents
    decide +kernel
  have hseparatorView : StdStrings.Represents (toStr "' -> '") "' -> '" := by
    unfold StdStrings.Represents
    decide +kernel
  have hsuffixView : StdStrings.Represents (toStr "' (negative)") "' (negative)" := by
    unfold StdStrings.Represents
    decide +kernel
  unfold alloc.string.String.Insts.CoreConvertFromShared0Str.from
    alloc.string.String.Insts.CoreOpsDerefDerefStr.deref alloc.string.String.push_str
  step with StdStrings.from_str_spec _ _ hprefixView hprefix as ⟨message, hmessage⟩
  subst message
  step with StdStrings.borrow_spec source hsource as ⟨sourceView, hview, _, _⟩
  step with StdStrings.push_str_spec _ source sourceView hview hfirst as ⟨message, hmessage, _⟩
  subst message
  step with StdStrings.push_str_spec _ _ _ hseparatorView hsecond as ⟨message, hmessage, _⟩
  subst message
  step with StdStrings.borrow_spec target htarget as ⟨targetView, hview, _, _⟩
  step with StdStrings.push_str_spec _ target targetView hview hthird as ⟨message, hmessage, _⟩
  subst message
  step with StdStrings.push_str_spec _ _ _ hsuffixView hfits as ⟨message, hmessage, _⟩
  subst message
  exact hpost

def firstEdge (members : List String) (source : String) : List (String × Bool) → Option String
  | [] => none
  | (target, negative) :: rest =>
      if negative = true ∧ target ∈ members then some (diagnostic source target)
      else firstEdge members source rest

def keepFirst (previous next : Option String) : Option String :=
  previous.orElse (fun _ => next)

theorem edge_scan_total (iter : core.slice.iter.Iter (String × Bool))
    (previous : Option String) (members : List String) (source : String)
    (hfits : ∀ target, (target, true) ∈ remaining iter → target ∈ members →
      StdStrings.Fits (diagnostic source target)) :
    rules.check_stratification_loop0_loop1_loop0 iter previous members source
      ⦃ result => result = keepFirst previous (firstEdge members source (remaining iter)) ⦄ := by
  unfold rules.check_stratification_loop0_loop1_loop0
  apply loop.spec_decr_nat (measure := fun state => (remaining state.1).length)
    (inv := fun state =>
      (∀ target, (target, true) ∈ remaining state.1 → target ∈ members →
        StdStrings.Fits (diagnostic source target)) ∧
      keepFirst state.2 (firstEdge members source (remaining state.1)) =
        keepFirst previous (firstEdge members source (remaining iter)))
  · rintro ⟨current, violation⟩ ⟨hfits, hresult⟩
    unfold rules.check_stratification_loop0_loop1_loop0.body
    step with slice_next_spec current as ⟨value, next, hnext⟩
    cases value with
    | none => simpa [hnext, firstEdge, keepFirst] using hresult
    | some edge =>
      rcases edge with ⟨target, negative⟩
      dsimp only
      have hrest : ∀ target, (target, true) ∈ remaining next → target ∈ members →
          StdStrings.Fits (diagnostic source target) := by
        intro target hedge hmember
        exact hfits target (by simp [hnext, hedge]) hmember
      have hlength : (remaining next).length < (remaining current).length := by simp [hnext]
      cases violation with
      | some message =>
        have heq : some message = keepFirst previous (firstEdge members source (remaining iter)) := by
          simpa [keepFirst] using hresult
        simpa [core.option.Option.is_none, keepFirst] using And.intro hrest (And.intro heq hlength)
      | none =>
        cases negative with
        | false =>
          have heq : firstEdge members source (remaining next) =
              keepFirst previous (firstEdge members source (remaining iter)) := by
            simpa [hnext, firstEdge, keepFirst] using hresult
          simpa [core.option.Option.is_none, keepFirst] using And.intro hrest (And.intro heq hlength)
        | true =>
          simp only [string_set_contains]
          by_cases hmember : target ∈ members
          · simp [hmember]
            apply diagnostic_spec source target (hfits target (by simp [hnext]) hmember)
            simp only [WP.spec_ok]
            refine ⟨hrest, ?_, hlength⟩
            simpa [hnext, firstEdge, keepFirst, hmember] using hresult
          · simp [hmember]
            exact ⟨hrest, by simpa [hnext, firstEdge, keepFirst, hmember] using hresult, hlength⟩
  · exact ⟨hfits, rfl⟩

theorem keep_first_assoc (left middle right : Option String) :
    keepFirst (keepFirst left middle) right = keepFirst left (keepFirst middle right) := by
  cases left <;> rfl

theorem keep_first_none_iff (left right : Option String) :
    keepFirst left right = none ↔ left = none ∧ right = none := by
  cases left <;> simp [keepFirst]

theorem first_edge_members (left right : List String) (source : String) (edges : List (String × Bool))
    (hmembers : ∀ vertex, vertex ∈ left ↔ vertex ∈ right) :
    firstEdge left source edges = firstEdge right source edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
    rcases edge with ⟨target, negative⟩
    simp only [firstEdge, hmembers, ih]

theorem first_edge_none_iff (members : List String) (source : String) (edges : List (String × Bool)) :
    firstEdge members source edges = none ↔
      ∀ target, (target, true) ∈ edges → target ∉ members := by
  induction edges with
  | nil => simp [firstEdge]
  | cons edge rest ih =>
    rcases edge with ⟨target, negative⟩
    cases negative with
    | false => simp [firstEdge, ih]
    | true => by_cases hmember : target ∈ members <;> simp [firstEdge, ih, hmember]

def firstNode (graph : NamedGraph) (members : List String) : List String → Option String
  | [] => none
  | source :: rest =>
      match StdMaps.lookupValue source graph with
      | none => firstNode graph members rest
      | some edges => keepFirst (firstEdge members source edges.val) (firstNode graph members rest)

def ScanFits (graph : NamedGraph) (members nodes : List String) : Prop :=
  ∀ source ∈ nodes, ∀ edges, StdMaps.lookupValue source graph = some edges →
    ∀ target, (target, true) ∈ edges.val → target ∈ members →
      StdStrings.Fits (diagnostic source target)

theorem node_scan_total (iter : core.slice.iter.Iter String)
    (graph : NamedGraph) (previous : Option String) (members : List String)
    (hfits : ScanFits graph members (remaining iter)) :
    rules.check_stratification_loop0_loop1 iter graph previous members ⦃ result =>
      result = keepFirst previous (firstNode graph members (remaining iter)) ⦄ := by
  unfold rules.check_stratification_loop0_loop1
  apply loop.spec_decr_nat (measure := fun state => (remaining state.1).length)
    (inv := fun state => ScanFits graph members (remaining state.1) ∧
      keepFirst state.2 (firstNode graph members (remaining state.1)) =
        keepFirst previous (firstNode graph members (remaining iter)))
  · rintro ⟨current, violation⟩ ⟨hfits, hresult⟩
    unfold rules.check_stratification_loop0_loop1.body
    step with slice_next_spec current as ⟨value, next, hnext⟩
    cases value with
    | none => simpa [hnext, firstNode, keepFirst] using hresult
    | some source =>
      have hrest : ScanFits graph members (remaining next) := by
        intro source hsource
        exact hfits source (by simp [hnext, hsource])
      have hlength : (remaining next).length < (remaining current).length := by simp [hnext]
      simp only [string_map_get]
      rw [bind_ok]
      cases hlookup : StdMaps.lookupValue source graph with
      | none =>
        change (Result.ok (ControlFlow.cont (next, violation)) :
          Result (ControlFlow (core.slice.iter.Iter String × Option String) (Option String))) ⦃ _ ⦄
        simp only [WP.spec_ok]
        exact ⟨hrest, by simpa [hnext, firstNode, hlookup] using hresult, hlength⟩
      | some edges =>
        dsimp only
        unfold SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
        rw [bind_ok]
        change (do
          let result ← rules.check_stratification_loop0_loop1_loop0 ⟨edges.deref, 0⟩ violation members source
          Result.ok (ControlFlow.cont (next, result))) ⦃ _ ⦄
        have hedges : ∀ target, (target, true) ∈ remaining ⟨edges.deref, 0⟩ → target ∈ members →
            StdStrings.Fits (diagnostic source target) := by
          simpa [remaining, alloc.vec.Vec.deref] using hfits source (by simp [hnext]) edges hlookup
        step with edge_scan_total ⟨edges.deref, 0⟩ violation members source hedges as ⟨result, hscan⟩
        subst result
        refine ⟨hrest, ?_, hlength⟩
        rw [hnext] at hresult
        simpa [firstNode, hlookup, remaining, alloc.vec.Vec.deref, keep_first_assoc] using hresult
  · exact ⟨hfits, rfl⟩

theorem first_node_members (graph : NamedGraph) (left right nodes : List String)
    (hmembers : ∀ vertex, vertex ∈ left ↔ vertex ∈ right) :
    firstNode graph left nodes = firstNode graph right nodes := by
  induction nodes with
  | nil => rfl
  | cons source rest ih =>
    simp only [firstNode]
    cases StdMaps.lookupValue source graph with
    | none => exact ih
    | some edges => simp only [first_edge_members left right source edges.val hmembers, ih]

theorem first_node_none_iff (graph : NamedGraph) (members nodes : List String) :
    firstNode graph members nodes = none ↔
      ∀ source ∈ nodes, ∀ edges, StdMaps.lookupValue source graph = some edges →
        ∀ target, (target, true) ∈ edges.val → target ∉ members := by
  induction nodes with
  | nil => simp [firstNode]
  | cons source rest ih =>
    cases hlookup : StdMaps.lookupValue source graph with
    | none => simp [firstNode, hlookup, ih]
    | some edges => simp [firstNode, hlookup, keep_first_none_iff, first_edge_none_iff, ih]

def firstComponent (graph : NamedGraph) : List (alloc.vec.Vec String) → Option String
  | [] => none
  | component :: rest =>
      keepFirst (firstNode graph component.val component.val) (firstComponent graph rest)

def ComponentFits (graph : NamedGraph) (component : alloc.vec.Vec String) : Prop :=
  (∀ source ∈ component.val, StdStrings.Fits source) ∧ ScanFits graph component.val component.val

/-- The actual outer scan terminates and preserves the exact diagnostic order:
    component order, then vertex order, then stored outgoing-edge order. -/
theorem component_scan_total (components : alloc.vec.Vec (alloc.vec.Vec String))
    (graph : NamedGraph) (previous : Option String)
    (hfits : ∀ component ∈ components.val, ComponentFits graph component) :
    rules.check_stratification_loop0 components graph previous ⦃ result =>
      result = keepFirst previous (firstComponent graph components.val) ⦄ := by
  unfold rules.check_stratification_loop0
  apply loop.spec_decr_nat (measure := fun state => state.1.val.length)
    (inv := fun state => (∀ component ∈ state.1.val, ComponentFits graph component) ∧
      keepFirst state.2 (firstComponent graph state.1.val) =
        keepFirst previous (firstComponent graph components.val))
  · rintro ⟨current, violation⟩ ⟨hfits, hresult⟩
    unfold rules.check_stratification_loop0.body
    step with vec_next_spec current as ⟨value, next, hnext⟩
    cases value with
    | none => simpa [hnext, firstComponent, keepFirst] using hresult
    | some component =>
      have hcomponent := hfits component (by simp [hnext])
      have hrest : ∀ component ∈ next.val, ComponentFits graph component := by
        intro component hcomponent
        exact hfits component (by simp [hnext, hcomponent])
      have hlength : next.val.length < current.val.length := by simp [hnext]
      cases violation with
      | some message =>
        have heq : some message = keepFirst previous (firstComponent graph components.val) := by
          simpa [keepFirst] using hresult
        simpa [core.option.Option.is_none, keepFirst] using And.intro hrest (And.intro heq hlength)
      | none =>
        simp only [Option.isNone_none, ↓reduceIte,
          std.collections.hash.set.HashSetTRandomStateGlobal.new,
          SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter, bind_ok]
        change (do
          let members ← (Result.ok [] : Result (List String))
          let members ← rules.check_stratification_loop0_loop0 ⟨component.deref, 0⟩ members
          let result ← rules.check_stratification_loop0_loop1 ⟨component.deref, 0⟩ graph none members
          Result.ok (ControlFlow.cont (next, result))) ⦃ _ ⦄
        rw [bind_ok]
        have hbound : ([] : List String).length + (remaining ⟨component.deref, 0⟩).length ≤ Usize.max := by
          simp [remaining, alloc.vec.Vec.deref]
        have hnames : ∀ source ∈ remaining ⟨component.deref, 0⟩, StdStrings.Fits source := by
          simpa [remaining, alloc.vec.Vec.deref] using hcomponent.1
        step with build_members_total ⟨component.deref, 0⟩ [] hbound (by simp) hnames
          as ⟨members, _, hmembers⟩
        have hmembers : ∀ source, source ∈ members ↔ source ∈ component.val := by
          simpa [remaining, alloc.vec.Vec.deref] using hmembers
        have hscan : ScanFits graph members (remaining ⟨component.deref, 0⟩) := by
          intro source hsource edges hedges target htarget hmember
          apply hcomponent.2 source _ edges hedges target htarget ((hmembers target).mp hmember)
          simpa [remaining, alloc.vec.Vec.deref] using hsource
        step with node_scan_total ⟨component.deref, 0⟩ graph none members hscan as ⟨result, hscan⟩
        subst result
        refine ⟨hrest, ?_, hlength⟩
        rw [hnext] at hresult
        simpa [firstComponent, remaining, alloc.vec.Vec.deref, keepFirst,
          first_node_members graph members component.val component.val hmembers] using hresult
  · exact ⟨hfits, rfl⟩

def NegativeEdge (graph : NamedGraph) (source target : String) : Prop :=
  ∃ edges, (source, edges) ∈ graph ∧ (target, true) ∈ edges.val

def InternalNegative (graph : NamedGraph) (components : List (alloc.vec.Vec String)) : Prop :=
  ∃ component ∈ components, ∃ source ∈ component.val, ∃ target ∈ component.val,
    NegativeEdge graph source target

theorem first_component_none_iff (graph : NamedGraph) (components : List (alloc.vec.Vec String))
    (hunique : StdMaps.UniqueKeys graph) :
    firstComponent graph components = none ↔ ¬ InternalNegative graph components := by
  have hnodes (component : alloc.vec.Vec String) :
      firstNode graph component.val component.val = none ↔
        ¬ ∃ source ∈ component.val, ∃ target ∈ component.val, NegativeEdge graph source target := by
    rw [first_node_none_iff]
    constructor
    · intro hnone
      rintro ⟨source, hsource, target, htarget, edges, hedges, hnegative⟩
      exact hnone source hsource edges ((StdMaps.lookup_value_some_iff source edges graph hunique).mpr hedges)
        target hnegative htarget
    · intro hnone source hsource edges hedges target hnegative htarget
      exact hnone ⟨source, hsource, target, htarget, edges,
        (StdMaps.lookup_value_some_iff source edges graph hunique).mp hedges, hnegative⟩
  induction components with
  | nil => simp [firstComponent, InternalNegative]
  | cons component rest ih =>
    simp only [firstComponent, keep_first_none_iff, hnodes, ih]
    simp [InternalNegative]

/-- This result is about the complete native negative-edge scan. Establishing
    that the adapter supplies the correct SCCs is a separate theorem. -/
theorem component_scan_criterion (components : alloc.vec.Vec (alloc.vec.Vec String))
    (graph : NamedGraph) (hunique : StdMaps.UniqueKeys graph)
    (hfits : ∀ component ∈ components.val, ComponentFits graph component) :
    rules.check_stratification_loop0 components graph none ⦃ result =>
      result = firstComponent graph components.val ∧
      (result = none ↔ ¬ InternalNegative graph components.val) ⦄ := by
  apply WP.spec_mono (component_scan_total components graph none hfits)
  intro result hresult
  have heq : result = firstComponent graph components.val := by simpa [keepFirst] using hresult
  exact ⟨heq, heq ▸ first_component_none_iff graph components.val hunique⟩

end NibliSelfCheck.Stratification
