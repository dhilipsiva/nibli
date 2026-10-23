import SccTermination

/- The outer traversal starts DFS trees and covers every graph vertex. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow
open nibli_reason.dependency_graph

private theorem take_set_zero {α : Type} (values : List α) (value : α) (h : 0 < values.length) :
    (values.set 0 value).take 1 = [value] := by
  cases values with
  | nil => simp at h
  | cons first rest => rfl

def startState (s : DfsState) (root next : Usize) : DfsState := { s with
  state := s.state.set root { index := some s.next_index, lowlink := s.next_index, on_stack := true }
  stack := s.stack.set 0#usize root
  stack_len := 1#usize
  work := s.work.set 0#usize { node := root, cursor := 0#usize }
  depth := 1#usize
  next_index := next }

theorem start_invariant (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (root next : Usize) (entry : NodeState)
    (hempty : s.depth = 0#usize) (hentry : s.state.val[root.val]? = some entry)
    (hnew : entry.index = none) (hnext : next.val = s.next_index.val + 1) :
    DfsInvariant graph (startState s root next) ∧
      PreservesDiscovery s.state (startState s root next).state ∧
      Discovered (startState s root next).state root := by
  let updated := startState s root next
  let fresh : NodeState := { index := some s.next_index, lowlink := s.next_index, on_stack := true }
  have hroot_bound := (List.getElem?_eq_some_iff.mp hentry).1
  have hgraph_bound : root.val < graph.length := by
    simpa [← h.state_size] using hroot_bound
  have hstack_bound : 0 < s.stack.length := by rw [h.stack_size]; omega
  have hwork_bound : 0 < s.work.length := by rw [h.work_size]; omega
  obtain ⟨hstack_empty, hcolors⟩ := invariant_empty_dfs graph s h hempty
  have hactive_empty : s.active = [] := by simp [DfsState.active, hstack_empty]
  have hactive : updated.active = [root] := by
    simpa [updated, startState, DfsState.active, alloc.vec.Vec.set_val_eq] using
      take_set_zero s.stack.val root hstack_bound
  have hframes : updated.frames = [{ node := root, cursor := 0#usize }] := by
    simpa [updated, startState, DfsState.frames, alloc.vec.Vec.set_val_eq] using
      take_set_zero s.work.val { node := root, cursor := 0#usize } hwork_bound
  have hgray : updated.gray = [root] := by
    change updated.frames.map (fun frame => frame.node) = _
    simp [hframes]
  have hfinished : updated.finished = s.finished := rfl
  have hnot_seen : ¬ Discovered s.state root := by
    rintro ⟨old, index, hold, hindex⟩
    have heq : old = entry := Option.some.inj (hold.symm.trans hentry)
    simp [heq, hnew] at hindex
  have hlookup : ∀ (vertex : Usize), updated.state.val[vertex.val]? =
      if vertex = root then some fresh else s.state.val[vertex.val]? := by
    intro vertex
    change (s.state.set root fresh).val[vertex.val]? = _
    rw [alloc.vec.Vec.set_val_eq]
    by_cases heq : vertex = root
    · subst vertex
      simp [hroot_bound]
    · have hne : root.val ≠ vertex.val := fun equal => heq (UScalar.eq_of_val_eq equal.symm)
      simp [heq, List.getElem?_set_ne hne]
  have hdiscovered : ∀ vertex, Discovered updated.state vertex ↔
      vertex = root ∨ Discovered s.state vertex := by
    intro vertex
    by_cases heq : vertex = root
    · subst vertex
      simp [Discovered, hlookup, fresh]
    · simp [Discovered, hlookup, heq]
  have hrank : rank updated.state root = s.next_index.val := by simp [rank, hlookup, fresh]
  have hlowlink : lowlink updated.state root = s.next_index.val := by simp [lowlink, hlookup, fresh]
  refine ⟨?_, fun vertex hvertex => (hdiscovered vertex).mpr (Or.inr hvertex),
    (hdiscovered root).mpr (Or.inl rfl)⟩
  change DfsInvariant graph updated
  refine {
    graph_valid := h.graph_valid
    state_size := by simpa [updated, startState] using h.state_size
    stack_size := by simpa [updated, startState] using h.stack_size
    work_size := by simpa [updated, startState] using h.work_size
    stack_bound := by simpa [updated, startState] using (show 1 ≤ s.stack.length by omega)
    work_bound := by simpa [updated, startState] using (show 1 ≤ s.work.length by omega)
    component_count := by
      change s.components.length + 1 ≤ next.val
      have := h.component_count
      omega
    discovery_count := ?_
    indices_bounded := ?_
    indices_unique := ?_
    lowlinks_bounded := ?_
    flags := ?_
    ordered := by simp [hactive]
    gray_sublist := by simp [hgray, hactive]
    frame_bounds := ?_
    colors := ?_
    disjoint := ?_
    components_unique := h.components_unique
    components_correct := h.components_correct
    finished_closed := h.finished_closed
    reaches_later := ?_
    returns_to_gray := ?_
    lowlink_witness := ?_
    processed := ?_ }
  · change next.val = ((s.state.set root fresh).val.filter (fun entry => entry.index.isSome)).length
    rw [alloc.vec.Vec.set_val_eq, ← List.countP_eq_length_filter, List.countP_set hroot_bound]
    simpa [fresh, (List.getElem?_eq_some_iff.mp hentry).2, hnew,
      List.countP_eq_length_filter, ← h.discovery_count] using hnext
  · intro vertex current index hcurrent hindex
    rw [hlookup] at hcurrent
    by_cases heq : vertex = root
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hcurrent
      have hi : index = s.next_index := by simpa [← hcurrent, fresh] using hindex.symm
      change index.val < next.val
      rw [hi, hnext]
      omega
    · simp only [heq, ↓reduceIte] at hcurrent
      have := h.indices_bounded vertex current index hcurrent hindex
      change index.val < next.val
      omega
  · intro left right le re index hleft hright hle hre
    rw [hlookup] at hleft hright
    by_cases hl : left = root <;> by_cases hr : right = root
    · exact hl.trans hr.symm
    · simp only [hl, ↓reduceIte, Option.some.injEq] at hleft
      simp only [hr, ↓reduceIte] at hright
      have hi : index = s.next_index := by simpa [← hleft, fresh] using hle.symm
      have := h.indices_bounded right re index hright hre
      simp [hi] at this
    · simp only [hr, ↓reduceIte, Option.some.injEq] at hright
      simp only [hl, ↓reduceIte] at hleft
      have hi : index = s.next_index := by simpa [← hright, fresh] using hre.symm
      have := h.indices_bounded left le index hleft hle
      simp [hi] at this
    · simp only [hl, ↓reduceIte] at hleft
      simp only [hr, ↓reduceIte] at hright
      exact h.indices_unique left right le re index hleft hright hle hre
  · intro vertex current index hcurrent hindex
    rw [hlookup] at hcurrent
    by_cases heq : vertex = root
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hcurrent
      have hi : index = s.next_index := by simpa [← hcurrent, fresh] using hindex.symm
      simp [← hcurrent, fresh, hi]
    · simp only [heq, ↓reduceIte] at hcurrent
      exact h.lowlinks_bounded vertex current index hcurrent hindex
  · intro vertex current hcurrent
    rw [hlookup] at hcurrent
    by_cases heq : vertex = root
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hcurrent
      simp [← hcurrent, fresh, hactive, heq]
    · simp only [heq, ↓reduceIte] at hcurrent
      simpa [hactive, heq, hactive_empty] using h.flags vertex current hcurrent
  · intro frame hframe
    have heq : frame = { node := root, cursor := 0#usize } := by simpa [hframes] using hframe
    subst frame
    exact ⟨graph.val[root.val]'hgraph_bound, by simp, by simp⟩
  · intro vertex
    rw [hdiscovered, hactive, hfinished, hcolors]
    simp
  · intro vertex hvertex hdone
    have heq : vertex = root := by simpa [hactive] using hvertex
    subst vertex
    exact hnot_seen ((hcolors root).mpr hdone)
  · intro ancestor hancestor vertex hvertex _
    have ha : ancestor = root := by simpa [hgray] using hancestor
    have hv : vertex = root := by simpa [hactive] using hvertex
    simp [ha, hv, Relation.ReflTransGen.refl]
  · intro vertex hvertex
    have hv : vertex = root := by simpa [hactive] using hvertex
    refine ⟨root, by simp [hgray], ?_, ?_⟩
    · simp [hv]
    · simp [hv, Relation.ReflTransGen.refl]
  · intro frame hframe
    have heq : frame = { node := root, cursor := 0#usize } := by simpa [hframes] using hframe
    subst frame
    exact ⟨root, by simp [hactive], by simp [hlowlink, hrank], Relation.ReflTransGen.refl⟩
  · intro frame hframe vertex howner neighbor hprocessed
    have heq : frame = { node := root, cursor := 0#usize } := by simpa [hframes] using hframe
    have hv : vertex = root := by simpa [hactive] using howner.1
    subst frame vertex
    obtain ⟨_, _, himpossible⟩ := hprocessed.2.resolve_left (by simp)
    simp at himpossible

structure ScanState where
  dfs : DfsState
  start : Usize

abbrev ScanTuple := alloc.vec.Vec NodeState × alloc.vec.Vec Usize × Usize ×
  alloc.vec.Vec Frame × Usize × alloc.vec.Vec (alloc.vec.Vec Usize) × Usize × Usize

def ScanState.pack (s : ScanState) : ScanTuple :=
  (s.dfs.state, s.dfs.stack, s.dfs.stack_len, s.dfs.work, s.dfs.depth,
    s.dfs.components, s.dfs.next_index, s.start)

def unpackScan (tuple : ScanTuple) : ScanState := {
  dfs := {
    state := tuple.1, stack := tuple.2.1, stack_len := tuple.2.2.1,
    work := tuple.2.2.2.1, depth := tuple.2.2.2.2.1,
    components := tuple.2.2.2.2.2.1, next_index := tuple.2.2.2.2.2.2.1 }
  start := tuple.2.2.2.2.2.2.2 }

def scan_body (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState) :
    Result (ControlFlow ScanTuple (alloc.vec.Vec (alloc.vec.Vec Usize))) :=
  compute_sccs_loop0.body graph s.dfs.state s.dfs.stack s.dfs.stack_len s.dfs.work
    s.dfs.depth s.dfs.components s.dfs.next_index s.start

private theorem scan_fresh (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (start : Usize) (entry : NodeState)
    (hempty : s.depth = 0#usize) (hentry : s.state.val[start.val]? = some entry)
    (hnew : entry.index = none) (hstart : start.val < graph.length) :
    scan_body graph ⟨s, start⟩ ⦃ result => ∃ updated next_start,
      DfsInvariant graph updated ∧ updated.depth = 0#usize ∧
      PreservesDiscovery s.state updated.state ∧ Discovered updated.state start ∧
      next_start.val = start.val + 1 ∧ result = .cont (ScanState.pack ⟨updated, next_start⟩) ⦄ := by
  have hstack_empty := (invariant_empty_dfs graph s h hempty).1
  have hentry_bound : start.val < s.state.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hnext_bound : s.next_index.val < s.state.length := by
    rw [h.discovery_count]
    apply List.length_filter_lt_length_iff_exists.mpr
    refine ⟨entry, List.mem_iff_getElem?.mpr ⟨start.val, hentry⟩, ?_⟩
    simp [hnew]
  have hnext_machine : s.next_index.val < Usize.max := Nat.lt_of_lt_of_le hnext_bound s.state.property
  have hstart_machine : start.val < Usize.max := Nat.lt_of_lt_of_le hstart graph.property
  have hstack_bound : 0 < s.stack.length := by rw [h.stack_size]; omega
  have hwork_bound : 0 < s.work.length := by rw [h.work_size]; omega
  have htest : start < Slice.len graph := by scalar_tac
  unfold scan_body compute_sccs_loop0.body
  simp only [htest, ↓reduceIte]
  step as ⟨actual, hactual⟩
  have heq : actual = entry := by simpa [(List.getElem?_eq_some_iff.mp hentry).2] using hactual
  subst actual
  simp only [(List.getElem?_eq_some_iff.mp hentry).2, hnew, Option.isNone, ↓reduceIte,
    hstack_empty, hempty]
  step as ⟨old, state_back, hold, hstate_back⟩
  step as ⟨next, hnext⟩
  step as ⟨old_stack, stack_back, hold_stack, hstack_back⟩
  step as ⟨stack_len, hstack_len⟩
  step as ⟨old_work, work_back, hold_work, hwork_back⟩
  step as ⟨depth, hdepth⟩
  have hstack_one : stack_len = 1#usize := by scalar_tac
  have hdepth_one : depth = 1#usize := by scalar_tac
  subst stack_len depth
  simp only [hstate_back, hstack_back, hwork_back]
  have hstart_inv := start_invariant graph s h start next entry hempty hentry hnew hnext
  have hdfs := dfs_total graph (startState s start next) hstart_inv.1
  simp only [startState] at hdfs
  step with hdfs as ⟨state, stack, stack_len, work, depth, components, next_index,
    hinvariant, hdepth, hstack, hpreserved⟩
  let updated : DfsState := ⟨state, stack, stack_len, work, depth, components, next_index⟩
  step as ⟨next_start, hnext_start⟩
  refine ⟨updated, next_start, hinvariant, hdepth, ?_, ?_, hnext_start, ?_⟩
  · exact fun vertex hvertex => hpreserved vertex (hstart_inv.2.1 vertex hvertex)
  · exact hpreserved start hstart_inv.2.2
  · rfl

private theorem scan_seen (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (start : Usize) (entry : NodeState) (index : Usize)
    (hentry : s.state.val[start.val]? = some entry) (hseen : entry.index = some index)
    (hstart : start.val < graph.length) :
    scan_body graph ⟨s, start⟩ ⦃ result => ∃ next_start,
      next_start.val = start.val + 1 ∧ result = .cont (ScanState.pack ⟨s, next_start⟩) ⦄ := by
  have hentry_bound : start.val < s.state.length := (List.getElem?_eq_some_iff.mp hentry).1
  have hstart_machine : start.val < Usize.max := Nat.lt_of_lt_of_le hstart graph.property
  have htest : start < Slice.len graph := by scalar_tac
  unfold scan_body compute_sccs_loop0.body
  simp only [htest, ↓reduceIte]
  step as ⟨actual, hactual⟩
  have heq : actual = entry := by simpa [(List.getElem?_eq_some_iff.mp hentry).2] using hactual
  subst actual
  simp [(List.getElem?_eq_some_iff.mp hentry).2, hseen]
  step as ⟨next_start, hnext_start⟩
  exact ⟨next_start, hnext_start, rfl⟩

structure ScanInvariant (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState) : Prop where
  dfs_invariant : DfsInvariant graph s.dfs
  empty : s.dfs.depth = 0#usize
  bound : s.start.val ≤ graph.length
  covered : ∀ vertex : Usize, vertex.val < s.start.val → Discovered s.dfs.state vertex

/-- Every component is a nonempty, valid maximal SCC; vertices occur exactly
    once across the output and the output covers the complete graph. -/
def IsSccPartition (graph : Slice (alloc.vec.Vec Usize))
    (components : alloc.vec.Vec (alloc.vec.Vec Usize)) : Prop :=
  (components.val.flatMap (fun component => component.val)).Nodup ∧
  (∀ component ∈ components.val, IsScc graph component.val) ∧
  ∀ vertex : Usize, vertex.val < graph.length ↔
    ∃ component ∈ components.val, vertex ∈ component.val

private theorem scan_partition (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState)
    (h : ScanInvariant graph s) (hcomplete : graph.length ≤ s.start.val) :
    IsSccPartition graph s.dfs.components := by
  refine ⟨h.dfs_invariant.components_unique, h.dfs_invariant.components_correct, ?_⟩
  intro vertex
  constructor
  · intro hvertex
    have hseen := h.covered vertex (by omega)
    exact ((invariant_empty_dfs graph s.dfs h.dfs_invariant h.empty).2 vertex).mp hseen
  · rintro ⟨component, hcomponent, hvertex⟩
    exact (h.dfs_invariant.components_correct component hcomponent).2.1 vertex hvertex

private theorem scan_advance (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState)
    (h : ScanInvariant graph s) (updated : DfsState) (next_start : Usize)
    (hinvariant : DfsInvariant graph updated) (hempty : updated.depth = 0#usize)
    (hpreserved : PreservesDiscovery s.dfs.state updated.state)
    (hcurrent : Discovered updated.state s.start)
    (hnext : next_start.val = s.start.val + 1) (hstart : s.start.val < graph.length) :
    ScanInvariant graph ⟨updated, next_start⟩ := by
  refine ⟨hinvariant, hempty, ?_, ?_⟩
  · change next_start.val ≤ graph.length
    omega
  · intro vertex hvertex
    change vertex.val < next_start.val at hvertex
    by_cases heq : vertex = s.start
    · simpa [heq] using hcurrent
    · have hne : vertex.val ≠ s.start.val := fun equal => heq (UScalar.eq_of_val_eq equal)
      exact hpreserved vertex (h.covered vertex (by omega))

theorem scan_step (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState)
    (h : ScanInvariant graph s) :
    scan_body graph s ⦃ result => match result with
      | .done components => IsSccPartition graph components
      | .cont tuple => ScanInvariant graph (unpackScan tuple) ∧
          graph.length - (unpackScan tuple).start.val < graph.length - s.start.val ⦄ := by
  by_cases hstart : s.start.val < graph.length
  · have hentry_bound : s.start.val < s.dfs.state.val.length := by
      change s.start.val < s.dfs.state.length
      rw [h.dfs_invariant.state_size]
      exact hstart
    let entry := s.dfs.state.val[s.start.val]'hentry_bound
    have hentry : s.dfs.state.val[s.start.val]? = some entry := by simp [entry]
    cases hseen : entry.index with
    | none =>
      apply WP.spec_mono (scan_fresh graph s.dfs h.dfs_invariant s.start entry h.empty hentry hseen hstart)
      rintro result ⟨updated, next_start, hinvariant, hempty, hpreserved, hcurrent, hnext, rfl⟩
      refine ⟨scan_advance graph s h updated next_start hinvariant hempty hpreserved hcurrent hnext hstart, ?_⟩
      change graph.length - next_start.val < graph.length - s.start.val
      omega
    | some index =>
      apply WP.spec_mono (scan_seen graph s.dfs s.start entry index hentry hseen hstart)
      rintro result ⟨next_start, hnext, rfl⟩
      refine ⟨scan_advance graph s h s.dfs next_start h.dfs_invariant h.empty
        (fun _ hvertex => hvertex) ⟨entry, index, hentry, hseen⟩ hnext hstart, ?_⟩
      change graph.length - next_start.val < graph.length - s.start.val
      omega
  · have htest : ¬ s.start < Slice.len graph := by scalar_tac
    unfold scan_body compute_sccs_loop0.body
    simp only [htest, ↓reduceIte, WP.spec_ok]
    exact scan_partition graph s h (by omega)

theorem scan_total (graph : Slice (alloc.vec.Vec Usize)) (s : ScanState)
    (h : ScanInvariant graph s) :
    compute_sccs_loop0 graph s.dfs.state s.dfs.stack s.dfs.stack_len s.dfs.work s.dfs.depth
      s.dfs.components s.dfs.next_index s.start ⦃ components => IsSccPartition graph components ⦄ := by
  unfold compute_sccs_loop0
  apply loop.spec_decr_nat (measure := fun tuple => graph.length - (unpackScan tuple).start.val)
    (inv := fun tuple => ScanInvariant graph (unpackScan tuple))
  · intro tuple hinvariant
    rcases tuple with ⟨state, stack, stack_len, work, depth, components, next_index, start⟩
    apply WP.spec_mono
      (scan_step graph (unpackScan (state, stack, stack_len, work, depth, components, next_index, start)) hinvariant)
    intro result hresult
    cases result with
    | done components => exact hresult
    | cont tuple => exact hresult
  · exact h

/-- Total correctness of the extracted production indexed Tarjan kernel. The
    only graph precondition is that every edge target is in bounds. -/
theorem compute_sccs_correct (graph : Slice (alloc.vec.Vec Usize)) (hgraph : ValidGraph graph) :
    compute_sccs graph ⦃ components => IsSccPartition graph components ⦄ := by
  apply compute_sccs_initialize graph hgraph
  intro state stack work hinvariant
  apply scan_total graph ⟨initialState state stack work, 0#usize⟩
  refine ⟨hinvariant, rfl, by simp, ?_⟩
  intro vertex hvertex
  simp at hvertex

end NibliSelfCheck.Scc
