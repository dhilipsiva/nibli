import SccKernel.Funs

/- Graph obligations for the production indexed Tarjan traversal. The graph
   relation reads the extracted input directly; there is no second SCC algorithm.
   The DFS must establish RootFrontier before its root branch may use the sealing
   theorem below. -/
namespace NibliSelfCheck.Scc

open Aeneas.Std
open nibli_reason.dependency_graph

def Edge (graph : Slice (alloc.vec.Vec Usize)) (source target : Usize) : Prop :=
  ∃ successors, graph.val[source.val]? = some successors ∧ target ∈ successors.val

abbrev Reach (graph : Slice (alloc.vec.Vec Usize)) := Relation.ReflTransGen (Edge graph)

def Closed (graph : Slice (alloc.vec.Vec Usize)) (vertices : Usize → Prop) : Prop :=
  ∀ source target, vertices source → Edge graph source target → vertices target

/-- A nonempty vertex set that is exactly one mutual-reachability class. -/
def IsScc (graph : Slice (alloc.vec.Vec Usize)) (vertices : List Usize) : Prop :=
  vertices ≠ [] ∧ (∀ vertex ∈ vertices, vertex.val < graph.length) ∧
    ∀ source ∈ vertices, ∀ target,
    target ∈ vertices ↔ Reach graph source target ∧ Reach graph target source

theorem reach_closed (graph : Slice (alloc.vec.Vec Usize)) (vertices : Usize → Prop)
    (hclosed : Closed graph vertices) {source target : Usize}
    (hsource : vertices source) (hpath : Reach graph source target) : vertices target := by
  induction hpath with
  | refl => exact hsource
  | tail _ hedge ih => exact hclosed _ _ ih hedge

theorem seal_component (graph : Slice (alloc.vec.Vec Usize))
    (block : List Usize) (finished : Usize → Prop) (root : Usize)
    (hroot : root ∈ block)
    (hvalid : ∀ vertex ∈ block, vertex.val < graph.length)
    (hforward : ∀ vertex ∈ block, Reach graph root vertex)
    (hreturn : ∀ vertex ∈ block, Reach graph vertex root)
    (hdisjoint : ∀ vertex ∈ block, ¬ finished vertex)
    (hclosed : Closed graph finished)
    (hboundary : ∀ source ∈ block, ∀ target,
      Edge graph source target → target ∈ block ∨ finished target) : IsScc graph block := by
  have hunion : Closed graph (fun vertex => vertex ∈ block ∨ finished vertex) := by
    intro source target hsource hedge
    rcases hsource with hsource | hsource
    · exact hboundary source hsource target hedge
    · exact Or.inr (hclosed source target hsource hedge)
  refine ⟨?_, hvalid, ?_⟩
  · intro hempty
    simp [hempty] at hroot
  · intro source hsource target
    constructor
    · intro htarget
      exact ⟨(hreturn source hsource).trans (hforward target htarget),
        (hreturn target htarget).trans (hforward source hsource)⟩
    · rintro ⟨hout, hback⟩
      rcases reach_closed graph _ hunion (Or.inl hsource) hout with hin | hdone
      · exact hin
      · exact False.elim (hdisjoint source hsource (reach_closed graph _ hclosed hdone hback))

def rank (state : alloc.vec.Vec NodeState) (vertex : Usize) : Nat :=
  (((state.val[vertex.val]?).bind (fun entry => entry.index)).map (fun index => index.val)).getD 0

def lowlink (state : alloc.vec.Vec NodeState) (vertex : Usize) : Nat :=
  ((state.val[vertex.val]?).map (fun entry => entry.lowlink.val)).getD 0

/-- Strict discovery order identifies the emitted suffix without running a
    second traversal or assuming anything about SCC membership. -/
theorem rank_suffix_membership (state : alloc.vec.Vec NodeState)
    (active : List Usize) (position : Nat) (root : Usize)
    (hroot : active[position]? = some root)
    (horder : active.Pairwise (fun left right => rank state left < rank state right))
    (vertex : Usize) :
    vertex ∈ active.drop position ↔ vertex ∈ active ∧ rank state root ≤ rank state vertex := by
  obtain ⟨hposition, hvalue⟩ := List.getElem?_eq_some_iff.mp hroot
  constructor
  · intro hmember
    refine ⟨List.mem_of_mem_drop hmember, ?_⟩
    obtain ⟨offset, hbound, heq⟩ := List.mem_drop_iff_getElem.mp hmember
    by_cases hzero : offset = 0
    · subst offset
      simp only [Nat.add_zero] at heq
      rw [← heq, hvalue]
    · have hlt := horder.rel_getElem_of_lt hposition (by omega : position + offset < active.length)
        (by omega : position < position + offset)
      rw [hvalue, heq] at hlt
      omega
  · rintro ⟨hmember, hrank⟩
    obtain ⟨index, hbound, heq⟩ := List.mem_iff_getElem.mp hmember
    have habove : position ≤ index := by
      by_contra h
      have hlt := horder.rel_getElem_of_lt hbound hposition (by omega : index < position)
      rw [heq, hvalue] at hlt
      omega
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨index - position, by omega, ?_⟩
    simpa [Nat.add_sub_of_le habove] using heq

theorem scc_of_same_members (graph : Slice (alloc.vec.Vec Usize))
    (left right : List Usize) (hmembers : ∀ vertex, vertex ∈ left ↔ vertex ∈ right)
    (hscc : IsScc graph left) : IsScc graph right := by
  refine ⟨?_, ?_, ?_⟩
  · intro hempty
    apply hscc.1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro vertex hvertex
    simpa [hempty] using (hmembers vertex).mp hvertex
  · intro vertex hvertex
    exact hscc.2.1 vertex ((hmembers vertex).mpr hvertex)
  · intro source hsource target
    exact (hmembers target).symm.trans (hscc.2.2 source ((hmembers source).mpr hsource) target)

theorem rank_prefix_membership (state : alloc.vec.Vec NodeState)
    (active : List Usize) (position : Nat)
    (horder : active.Pairwise (fun left right => rank state left < rank state right))
    (vertex : Usize) :
    vertex ∈ active.take position ↔ vertex ∈ active ∧ vertex ∉ active.drop position := by
  constructor
  · intro hprefix
    refine ⟨List.mem_of_mem_take hprefix, ?_⟩
    intro hsuffix
    have hlt := horder.rel_of_mem_take_of_mem_drop hprefix hsuffix
    omega
  · rintro ⟨hmember, hmissing⟩
    rw [← List.take_append_drop position active] at hmember
    exact (List.mem_append.mp hmember).resolve_right hmissing

/-- The graph-specific obligations at a completed top DFS frame. `gray` is the
    live DFS stack; `active` is the live Tarjan stack; finished components form a
    forward-closed set. Ranks and lowlinks come from the actual Rust state. -/
structure RootFrontier (graph : Slice (alloc.vec.Vec Usize))
    (state : alloc.vec.Vec NodeState) (active gray : List Usize)
    (finished : Usize → Prop) (root : Usize) : Prop where
  root_active : root ∈ active
  active_valid : ∀ vertex ∈ active, vertex.val < graph.length
  root_gray : root ∈ gray
  topmost : ∀ vertex ∈ gray, rank state vertex ≤ rank state root
  reaches_later : ∀ ancestor ∈ gray, ∀ vertex ∈ active,
    rank state ancestor ≤ rank state vertex → Reach graph ancestor vertex
  returns_to_gray : ∀ vertex ∈ active, ∃ ancestor ∈ gray,
    rank state ancestor ≤ rank state vertex ∧ Reach graph vertex ancestor
  processed : ∀ source ∈ active, rank state root ≤ rank state source →
    ∀ target, Edge graph source target → target ∈ active ∨ finished target
  lowlink_bound : ∀ source ∈ active, rank state root ≤ rank state source →
    ∀ target ∈ active, Edge graph source target → lowlink state root ≤ rank state target
  root_test : lowlink state root = rank state root
  disjoint : ∀ vertex ∈ active, ¬ finished vertex
  finished_closed : Closed graph finished

theorem root_frontier_scc (graph : Slice (alloc.vec.Vec Usize))
    (state : alloc.vec.Vec NodeState) (active gray : List Usize)
    (finished : Usize → Prop) (root : Usize)
    (h : RootFrontier graph state active gray finished root) :
    IsScc graph (active.filter (fun vertex => decide (rank state root ≤ rank state vertex))) := by
  apply seal_component graph _ finished root
  · simp [h.root_active]
  · intro vertex hvertex
    exact h.active_valid vertex (List.mem_filter.mp hvertex).1
  · intro vertex hvertex
    obtain ⟨hactive, hrank⟩ := List.mem_filter.mp hvertex
    exact h.reaches_later root h.root_gray vertex hactive (by simpa using hrank)
  · intro vertex hvertex
    have hactive := (List.mem_filter.mp hvertex).1
    obtain ⟨ancestor, hgray, _, hback⟩ := h.returns_to_gray vertex hactive
    exact hback.trans (h.reaches_later ancestor hgray root h.root_active (h.topmost ancestor hgray))
  · intro vertex hvertex
    exact h.disjoint vertex (List.mem_filter.mp hvertex).1
  · exact h.finished_closed
  · intro source hsource target hedge
    obtain ⟨hactive, hrank⟩ := List.mem_filter.mp hsource
    have hrank' : rank state root ≤ rank state source := by simpa using hrank
    rcases h.processed source hactive hrank' target hedge with htarget | hdone
    · apply Or.inl
      apply List.mem_filter.mpr
      refine ⟨htarget, ?_⟩
      have hbound := h.lowlink_bound source hactive hrank' target htarget hedge
      simpa [h.root_test] using hbound
    · exact Or.inr hdone

theorem root_frontier_closed (graph : Slice (alloc.vec.Vec Usize))
    (state : alloc.vec.Vec NodeState) (active gray : List Usize)
    (finished : Usize → Prop) (root : Usize)
    (h : RootFrontier graph state active gray finished root) :
    Closed graph (fun vertex =>
      vertex ∈ active.filter (fun vertex => decide (rank state root ≤ rank state vertex)) ∨
        finished vertex) := by
  intro source target hsource hedge
  rcases hsource with hsource | hsource
  · obtain ⟨hactive, hrank⟩ := List.mem_filter.mp hsource
    have hrank' : rank state root ≤ rank state source := by simpa using hrank
    rcases h.processed source hactive hrank' target hedge with htarget | hdone
    · apply Or.inl
      apply List.mem_filter.mpr
      refine ⟨htarget, ?_⟩
      have hbound := h.lowlink_bound source hactive hrank' target htarget hedge
      simpa [h.root_test] using hbound
    · exact Or.inr hdone
  · exact Or.inr (h.finished_closed source target hsource hedge)

end NibliSelfCheck.Scc
