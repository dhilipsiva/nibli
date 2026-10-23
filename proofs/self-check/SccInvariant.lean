import SccKernelProofs

/- State invariants for the production traversal. Their definitions are proof
   obligations, not certificates: initialization and every transition must
   establish them before they can justify the complete traversal. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow
open nibli_reason.dependency_graph

def DfsState.frames (s : DfsState) : List Frame := s.work.val.take s.depth.val

def Discovered (state : alloc.vec.Vec NodeState) (vertex : Usize) : Prop :=
  ∃ entry index, state.val[vertex.val]? = some entry ∧ entry.index = some index

def ValidGraph (graph : Slice (alloc.vec.Vec Usize)) : Prop :=
  ∀ (source : Nat) (successors : alloc.vec.Vec Usize), graph.val[source]? = some successors →
    ∀ (target : Usize), target ∈ successors.val → target.val < graph.length

/-- The active interval owned by a live frame excludes all later live frames
    and their descendants. Finished descendants still on the Tarjan stack are
    included in the interval of their nearest live ancestor. -/
def Owns (s : DfsState) (owner vertex : Usize) : Prop :=
  vertex ∈ s.active ∧ rank s.state owner ≤ rank s.state vertex ∧
    ∀ later ∈ s.gray, rank s.state owner < rank s.state later →
      rank s.state vertex < rank s.state later

def ProcessedEdge (graph : Slice (alloc.vec.Vec Usize)) (frame : Frame)
    (source target : Usize) : Prop :=
  Edge graph source target ∧ (source ≠ frame.node ∨
    ∃ successors, graph.val[source.val]? = some successors ∧
      target ∈ successors.val.take frame.cursor.val)

structure DfsInvariant (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState) : Prop where
  graph_valid : ValidGraph graph
  state_size : s.state.length = graph.length
  stack_size : s.stack.length = graph.length
  work_size : s.work.length = graph.length
  stack_bound : s.stack_len.val ≤ s.stack.length
  work_bound : s.depth.val ≤ s.work.length
  component_count : s.components.length + s.stack_len.val ≤ s.next_index.val
  discovery_count : s.next_index.val =
    (s.state.val.filter (fun entry => entry.index.isSome)).length
  indices_bounded : ∀ (vertex : Usize) (entry : NodeState) (index : Usize),
    s.state.val[vertex.val]? = some entry →
    entry.index = some index → index.val < s.next_index.val
  indices_unique : ∀ (left right : Usize) (le re : NodeState) (index : Usize),
    s.state.val[left.val]? = some le → s.state.val[right.val]? = some re →
    le.index = some index → re.index = some index → left = right
  lowlinks_bounded : ∀ (vertex : Usize) (entry : NodeState) (index : Usize),
    s.state.val[vertex.val]? = some entry →
    entry.index = some index → entry.lowlink.val ≤ index.val
  flags : StackFlags s.state s.active
  ordered : s.active.Pairwise (fun left right => rank s.state left < rank s.state right)
  gray_sublist : List.Sublist s.gray s.active
  frame_bounds : ∀ frame ∈ s.frames, ∃ successors,
    graph.val[frame.node.val]? = some successors ∧ frame.cursor.val ≤ successors.length
  colors : ∀ vertex, Discovered s.state vertex ↔ vertex ∈ s.active ∨ s.finished vertex
  disjoint : ∀ vertex ∈ s.active, ¬ s.finished vertex
  components_unique : (s.components.val.flatMap (fun component => component.val)).Nodup
  components_correct : ∀ component ∈ s.components.val, IsScc graph component.val
  finished_closed : Closed graph s.finished
  reaches_later : ∀ ancestor ∈ s.gray, ∀ vertex ∈ s.active,
    rank s.state ancestor ≤ rank s.state vertex → Reach graph ancestor vertex
  returns_to_gray : ∀ vertex ∈ s.active, ∃ ancestor ∈ s.gray,
    rank s.state ancestor ≤ rank s.state vertex ∧ Reach graph vertex ancestor
  lowlink_witness : ∀ frame ∈ s.frames, ∃ vertex ∈ s.active,
    lowlink s.state frame.node = rank s.state vertex ∧ Reach graph frame.node vertex
  processed : ∀ frame ∈ s.frames, ∀ source, Owns s frame.node source →
    ∀ target, ProcessedEdge graph frame source target →
      (target ∈ s.active ∨ s.finished target) ∧
      (target ∈ s.active → lowlink s.state frame.node ≤ rank s.state target)

private theorem active_valid (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (vertex : Usize) (hactive : vertex ∈ s.active) :
    vertex.val < graph.length := by
  obtain ⟨entry, index, hentry, _⟩ := (h.colors vertex).mpr (Or.inl hactive)
  have hbound : vertex.val < s.state.length := (List.getElem?_eq_some_iff.mp hentry).1
  simpa [h.state_size] using hbound

private theorem top_frame_member (s : DfsState) (frame : Frame)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame) : frame ∈ s.frames := by
  apply List.mem_iff_getElem?.mpr
  refine ⟨s.depth.val - 1, ?_⟩
  dsimp only [DfsState.frames]
  rw [List.getElem?_take_of_lt (by omega)]
  exact hframe

private theorem topmost_rank (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (frame : Frame)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame) :
    ∀ vertex ∈ s.gray, rank s.state vertex ≤ rank s.state frame.node := by
  have hlength : s.gray.length = s.depth.val := by
    simp [DfsState.gray, List.length_take, Nat.min_eq_left h.work_bound]
  have htop : s.gray[s.depth.val - 1]? = some frame.node := by
    simp only [DfsState.gray, List.getElem?_map]
    rw [List.getElem?_take_of_lt (by omega), hframe]
    rfl
  have hgray_order := h.ordered.sublist h.gray_sublist
  intro vertex hvertex
  obtain ⟨position, hposition, hvalue⟩ := List.mem_iff_getElem.mp hvertex
  by_cases heq : position = s.depth.val - 1
  · have hsame : vertex = frame.node := by
      subst position
      exact hvalue.symm.trans (List.getElem?_eq_some_iff.mp htop).2
    simp [hsame]
  · have hlt : position < s.depth.val - 1 := by omega
    have h := hgray_order.rel_getElem_of_lt hposition
      (List.getElem?_eq_some_iff.mp htop).1 hlt
    rw [hvalue, (List.getElem?_eq_some_iff.mp htop).2] at h
    omega

theorem invariant_root_ready (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (frame : Frame) (successors : alloc.vec.Vec Usize)
    (source : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (hfinished : successors.length ≤ frame.cursor.val)
    (hsource : s.state.val[frame.node.val]? = some source)
    (hroot : source.index = some source.lowlink) :
    Nonempty (EmissionReady graph s frame.node) := by
  have hframe_mem := top_frame_member s frame hpositive hframe
  have hgray : frame.node ∈ s.gray := by
    apply List.mem_map.mpr
    exact ⟨frame, hframe_mem, rfl⟩
  have hactive := h.gray_sublist.subset hgray
  have htop := topmost_rank graph s h frame hpositive hframe
  have howns : ∀ vertex ∈ s.active, rank s.state frame.node ≤ rank s.state vertex →
      Owns s frame.node vertex := by
    intro vertex hvertex hrank
    refine ⟨hvertex, hrank, ?_⟩
    intro later hlater hstrict
    have := htop later hlater
    omega
  have hprocessed : ∀ vertex target, Edge graph vertex target →
      ProcessedEdge graph frame vertex target := by
    intro vertex target hedge
    refine ⟨hedge, ?_⟩
    by_cases heq : vertex = frame.node
    · subst vertex
      obtain ⟨neighbors, hneighbors, htarget⟩ := hedge
      have heq : neighbors = successors := Option.some.inj (hneighbors.symm.trans hedges)
      subst neighbors
      right
      refine ⟨successors, hedges, ?_⟩
      simpa [List.take_of_length_le hfinished] using htarget
    · exact Or.inl heq
  have hfrontier : RootFrontier graph s.state s.active s.gray s.finished frame.node := {
    root_active := hactive
    active_valid := active_valid graph s h
    root_gray := hgray
    topmost := htop
    reaches_later := h.reaches_later
    returns_to_gray := h.returns_to_gray
    processed := fun vertex hvertex hrank target hedge =>
      (h.processed frame hframe_mem vertex (howns vertex hvertex hrank) target
        (hprocessed vertex target hedge)).1
    lowlink_bound := fun vertex hvertex hrank target htarget hedge =>
      (h.processed frame hframe_mem vertex (howns vertex hvertex hrank) target
        (hprocessed vertex target hedge)).2 htarget
    root_test := by simp [rank, lowlink, hsource, hroot]
    disjoint := h.disjoint
    finished_closed := h.finished_closed }
  obtain ⟨position, hposition⟩ := List.mem_iff_getElem?.mp hactive
  have hposition_bound : position < s.stack_len.val := by
    have := (List.getElem?_eq_some_iff.mp hposition).1
    simp only [DfsState.active, List.length_take] at this
    omega
  have hroot_position : s.stack.val[position]? = some frame.node := by
    simpa [DfsState.active, List.getElem?_take_of_lt hposition_bound] using hposition
  refine ⟨{
    position := position
    position_bound := hposition_bound
    stack_bound := h.stack_bound
    root_position := hroot_position
    target_bounds := ?_
    flags := h.flags
    ordered := h.ordered
    frontier := hfrontier }⟩
  intro index hindex vertex hlookup
  have hmember : vertex ∈ s.active := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨index, ?_⟩
    simpa [DfsState.active, List.getElem?_take_of_lt hindex] using hlookup
  rw [h.state_size]
  exact active_valid graph s h vertex hmember

def initialState (state : alloc.vec.Vec NodeState) (stack : alloc.vec.Vec Usize)
    (work : alloc.vec.Vec Frame) : DfsState := {
  state := state, stack := stack, stack_len := 0#usize, work := work,
  depth := 0#usize, components := alloc.vec.Vec.new _, next_index := 0#usize }

theorem initial_invariant (graph : Slice (alloc.vec.Vec Usize)) (hgraph : ValidGraph graph)
    (state : alloc.vec.Vec NodeState) (stack : alloc.vec.Vec Usize) (work : alloc.vec.Vec Frame)
    (hstate : state.val = List.replicate graph.length
      { index := none, lowlink := 0#usize, on_stack := false })
    (hstack : stack.length = graph.length) (hwork : work.length = graph.length) :
    DfsInvariant graph (initialState state stack work) := by
  have hentry : ∀ (vertex : Usize) (entry : NodeState), state.val[vertex.val]? = some entry →
      entry = { index := none, lowlink := 0#usize, on_stack := false } := by
    intro vertex entry hlookup
    apply List.eq_of_mem_replicate
    rw [← hstate]
    exact List.mem_iff_getElem?.mpr ⟨vertex.val, hlookup⟩
  have hnone : ∀ vertex, ¬ Discovered state vertex := by
    rintro vertex ⟨entry, index, hlookup, hindex⟩
    rw [hentry vertex entry hlookup] at hindex
    cases hindex
  refine {
    graph_valid := hgraph
    state_size := by simp [initialState, alloc.vec.Vec.length, hstate]
    stack_size := hstack
    work_size := hwork
    stack_bound := by simp [initialState]
    work_bound := by simp [initialState]
    component_count := by simp [initialState]
    discovery_count := by simp [initialState, hstate]
    indices_bounded := ?_
    indices_unique := ?_
    lowlinks_bounded := ?_
    flags := ?_
    ordered := by simp [initialState, DfsState.active]
    gray_sublist := by simp [initialState, DfsState.gray, DfsState.active]
    frame_bounds := by simp [initialState, DfsState.frames]
    colors := by simp [initialState, DfsState.active, DfsState.finished, hnone]
    disjoint := by simp [initialState, DfsState.active]
    components_unique := by simp [initialState]
    components_correct := by simp [initialState]
    finished_closed := by simp [Closed, initialState, DfsState.finished]
    reaches_later := by simp [initialState, DfsState.gray]
    returns_to_gray := by simp [initialState, DfsState.active]
    lowlink_witness := by simp [initialState, DfsState.frames]
    processed := by simp [initialState, DfsState.frames] }
  · intro vertex entry index hlookup hindex
    exact False.elim (hnone vertex ⟨entry, index, hlookup, hindex⟩)
  · intro left right le re index hleft _ hindex _
    exact False.elim (hnone left ⟨le, index, hleft, hindex⟩)
  · intro vertex entry index hlookup hindex
    exact False.elim (hnone vertex ⟨entry, index, hlookup, hindex⟩)
  · intro vertex entry hlookup
    rw [hentry vertex entry hlookup]
    simp [initialState, DfsState.active]

/-- The production allocator/clone prefix establishes the invariant. The
    outer-loop proof supplied by the caller is still a separate obligation. -/
theorem compute_sccs_initialize (graph : Slice (alloc.vec.Vec Usize))
    (hgraph : ValidGraph graph) (post : alloc.vec.Vec (alloc.vec.Vec Usize) → Prop)
    (hloop : ∀ state stack work, DfsInvariant graph (initialState state stack work) →
      compute_sccs_loop0 graph state stack 0#usize work 0#usize
        (alloc.vec.Vec.new _) 0#usize 0#usize ⦃ post ⦄) :
    compute_sccs graph ⦃ post ⦄ := by
  unfold compute_sccs
  step with alloc.vec.from_elem_spec NodeState.Insts.CoreCloneClone _ _ (by rfl)
    as ⟨state, hstate, hstate_size⟩
  step with alloc.vec.from_elem_spec core.clone.CloneUsize _ _ (by rfl)
    as ⟨stack, hstack, hstack_size⟩
  step with alloc.vec.from_elem_spec Frame.Insts.CoreCloneClone _ _ (by rfl)
    as ⟨work, hwork, hwork_size⟩
  apply hloop state stack work
  exact initial_invariant graph hgraph state stack work hstate hstack_size hwork_size

private theorem frame_discovered (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (frame : Frame) (hframe : frame ∈ s.frames) :
    Discovered s.state frame.node := by
  apply (h.colors frame.node).mpr
  apply Or.inl
  apply h.gray_sublist.subset
  exact List.mem_map.mpr ⟨frame, hframe, rfl⟩

/-- Every local precondition of the extracted body follows from the invariant.
    This proves a single iteration cannot fail; preservation and decrease of a
    termination measure are additional obligations. -/
theorem invariant_step_total (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) : dfs_body graph s ⦃ _ => True ⦄ := by
  have hgray_length : s.gray.length = s.depth.val := by
    simp [DfsState.gray, Nat.min_eq_left h.work_bound]
  have hactive_length : s.active.length = s.stack_len.val := by
    simp [DfsState.active, Nat.min_eq_left h.stack_bound]
  have hdepth_stack : s.depth.val ≤ s.stack_len.val := by
    have := h.gray_sublist.length_le
    omega
  have hnext_bound : s.next_index.val ≤ s.state.length := by
    rw [h.discovery_count]
    exact List.length_filter_le _ _
  have hmachine : s.state.length ≤ Usize.max := s.state.property
  have hcounts := h.component_count
  have hstate_size := h.state_size
  have hstack_size := h.stack_size
  have hwork_size := h.work_size
  by_cases hpositive : 0 < s.depth.val
  · have htop_bound : s.depth.val - 1 < s.work.val.length := by
      have := h.work_bound
      change s.depth.val ≤ s.work.val.length at this
      omega
    let frame := s.work.val[s.depth.val - 1]'htop_bound
    have hframe : s.work.val[s.depth.val - 1]? = some frame := by simp [frame]
    have hframe_mem := top_frame_member s frame hpositive hframe
    obtain ⟨successors, hedges, _⟩ := h.frame_bounds frame hframe_mem
    obtain ⟨source, index, hsource, hindex⟩ := frame_discovered graph s h frame hframe_mem
    by_cases hcursor : frame.cursor.val < successors.length
    · let target := successors.val[frame.cursor.val]'hcursor
      have htarget : successors.val[frame.cursor.val]? = some target := by simp [target]
      have htarget_bound : target.val < s.state.val.length := by
        change target.val < s.state.length
        rw [h.state_size]
        exact h.graph_valid frame.node.val successors hedges target
          (List.mem_iff_getElem?.mpr ⟨frame.cursor.val, htarget⟩)
      let entry := s.state.val[target.val]'htarget_bound
      have hentry : s.state.val[target.val]? = some entry := by simp [entry]
      cases hseen : entry.index with
      | none =>
        have hnext_strict : s.next_index.val < s.state.length := by
          rw [h.discovery_count]
          apply List.length_filter_lt_length_iff_exists.mpr
          refine ⟨entry, List.mem_iff_getElem?.mpr ⟨target.val, hentry⟩, ?_⟩
          simp [hseen]
        exact WP.spec_mono (dfs_discover_step graph s frame successors target entry
          hpositive hframe hedges htarget hentry hseen (by omega) (by omega) (by omega))
          (fun _ _ => True.intro)
      | some discovered =>
        exact WP.spec_mono (dfs_seen_step graph s frame successors target discovered entry source
          hpositive hframe hedges htarget hentry hseen hsource) (fun _ _ => True.intro)
    · have hfinished : successors.length ≤ frame.cursor.val := by omega
      have hparent_exists : ∃ parent parent_entry,
          (1 < s.depth.val → s.work.val[s.depth.val - 2]? = some parent) ∧
          (1 < s.depth.val → s.state.val[parent.node.val]? = some parent_entry) := by
        by_cases hdepth : 1 < s.depth.val
        · have hparent_bound : s.depth.val - 2 < s.work.val.length := by omega
          let parent := s.work.val[s.depth.val - 2]'hparent_bound
          have hparent : s.work.val[s.depth.val - 2]? = some parent := by simp [parent]
          have hparent_mem : parent ∈ s.frames := by
            apply List.mem_iff_getElem?.mpr
            refine ⟨s.depth.val - 2, ?_⟩
            simpa [DfsState.frames, List.getElem?_take_of_lt (by omega : s.depth.val - 2 < s.depth.val)]
              using hparent
          obtain ⟨parent_entry, _, hentry, _⟩ := frame_discovered graph s h parent hparent_mem
          exact ⟨parent, parent_entry, fun _ => hparent, fun _ => hentry⟩
        · exact ⟨frame, source, fun h => False.elim (hdepth h), fun h => False.elim (hdepth h)⟩
      obtain ⟨parent, parent_entry, hparent, hparent_entry⟩ := hparent_exists
      by_cases hroot : index = source.lowlink
      · have hroot_index : source.index = some source.lowlink := hindex.trans (congrArg some hroot)
        obtain ⟨ready⟩ := invariant_root_ready graph s h frame successors source
          hpositive hframe hedges hfinished hsource hroot_index
        exact WP.spec_mono (dfs_finish_root graph s frame parent successors source parent_entry
          hpositive hframe hedges hfinished hsource hroot_index ready (by omega) hparent hparent_entry)
          (fun _ _ => True.intro)
      · exact WP.spec_mono (dfs_finish_nonroot graph s frame parent successors index source parent_entry
          hpositive hframe hedges hfinished hsource hindex hroot hparent hparent_entry)
          (fun _ _ => True.intro)
  · have hzero : s.depth = 0#usize := by scalar_tac
    rw [dfs_done graph s hzero]
    simp

theorem invariant_empty_dfs (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (hempty : s.depth = 0#usize) :
    s.stack_len = 0#usize ∧ ∀ vertex, Discovered s.state vertex ↔ s.finished vertex := by
  have hgray : s.gray = [] := by simp [DfsState.gray, hempty]
  have hactive : s.active = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro vertex hvertex
    obtain ⟨ancestor, hancestor, _, _⟩ := h.returns_to_gray vertex hvertex
    simp [hgray] at hancestor
  constructor
  · have hlength : s.active.length = s.stack_len.val := by
      simp [DfsState.active, Nat.min_eq_left h.stack_bound]
    have hzero : s.stack_len.val = 0 := by simpa [hactive] using hlength.symm
    exact UScalar.eq_of_val_eq hzero
  · intro vertex
    simpa [hactive] using h.colors vertex

private def replaceLowlink (node value : Usize) (position : Nat) (entry : NodeState) : NodeState :=
  { entry with lowlink := if position = node.val then value else entry.lowlink }

private theorem lowlink_set_lookup (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source) (position : Nat) :
    (state.set node { source with lowlink := value }).val[position]? =
      (state.val[position]?).map (replaceLowlink node value position) := by
  simp only [alloc.vec.Vec.set_val_eq]
  by_cases heq : node.val = position
  · subst position
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hsource).1, hsource]
    simp [replaceLowlink]
  · rw [List.getElem?_set_ne heq]
    cases state.val[position]? <;> simp [replaceLowlink, Ne.symm heq]

private theorem lowlink_set_entry (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source)
    (vertex : Usize) (entry : NodeState)
    (hentry : (state.set node { source with lowlink := value }).val[vertex.val]? = some entry) :
    ∃ old, state.val[vertex.val]? = some old ∧ entry = replaceLowlink node value vertex.val old := by
  have h := lowlink_set_lookup state node value source hsource vertex.val
  rw [hentry] at h
  cases hold : state.val[vertex.val]? with
  | none => simp [hold] at h
  | some old => exact ⟨old, rfl, by simpa [hold] using h⟩

private theorem lowlink_set_rank (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source) (vertex : Usize) :
    rank (state.set node { source with lowlink := value }) vertex = rank state vertex := by
  simp only [rank, lowlink_set_lookup state node value source hsource]
  cases state.val[vertex.val]? <;> simp [replaceLowlink]

private theorem lowlink_set_value (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source) (vertex : Usize) :
    lowlink (state.set node { source with lowlink := value }) vertex =
      if vertex = node then value.val else lowlink state vertex := by
  by_cases heq : vertex = node
  · subst vertex
    simp only [lowlink, lowlink_set_lookup state node value source hsource, hsource]
    simp [replaceLowlink]
  · have hne : vertex.val ≠ node.val := fun equal => heq (UScalar.eq_of_val_eq equal)
    simp only [lowlink, lowlink_set_lookup state node value source hsource, heq, ↓reduceIte]
    cases state.val[vertex.val]? <;> simp [replaceLowlink, hne]

private theorem lowlink_set_discovered (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source) (vertex : Usize) :
    Discovered (state.set node { source with lowlink := value }) vertex ↔ Discovered state vertex := by
  constructor
  · rintro ⟨entry, index, hentry, hindex⟩
    obtain ⟨old, hold, heq⟩ := lowlink_set_entry state node value source hsource vertex entry hentry
    exact ⟨old, index, hold, by simpa [heq, replaceLowlink] using hindex⟩
  · rintro ⟨old, index, hold, hindex⟩
    refine ⟨replaceLowlink node value vertex.val old, index, ?_, ?_⟩
    · rw [lowlink_set_lookup state node value source hsource, hold]
      rfl
    · simpa [replaceLowlink] using hindex

private theorem lowlink_set_count (state : alloc.vec.Vec NodeState) (node value : Usize)
    (source : NodeState) (hsource : state.val[node.val]? = some source) :
    ((state.set node { source with lowlink := value }).val.filter
      (fun entry => entry.index.isSome)).length =
      (state.val.filter (fun entry => entry.index.isSome)).length := by
  have hmap : (state.set node { source with lowlink := value }).val.map NodeState.index =
      state.val.map NodeState.index := by
    apply List.ext_getElem?
    intro position
    simp only [List.getElem?_map, lowlink_set_lookup state node value source hsource]
    cases state.val[position]? <;> rfl
  have hcount := congrArg (fun values : List (Option Usize) => values.countP Option.isSome) hmap
  simp only [List.countP_map] at hcount
  simpa only [Function.comp_def, List.countP_eq_length_filter] using hcount

private theorem cursor_set_gray (s : DfsState) (top cursor : Usize) (frame : Frame)
    (htop : top.val < s.depth.val) (hframe : s.work.val[top.val]? = some frame) :
    (((s.work.set top { frame with cursor := cursor }).val.take s.depth.val).map
      (fun frame => frame.node)) = s.gray := by
  simp only [alloc.vec.Vec.set_val_eq, List.take_set, List.map_set]
  have hlookup : ((s.work.val.take s.depth.val).map (fun frame => frame.node))[top.val]? =
      some frame.node := by
    simp only [List.getElem?_map]
    rw [List.getElem?_take_of_lt htop, hframe]
    rfl
  have hbound := (List.getElem?_eq_some_iff.mp hlookup).1
  have hvalue := (List.getElem?_eq_some_iff.mp hlookup).2
  rw [← hvalue, List.set_getElem_self hbound]
  rfl

def advanceState (s : DfsState) (top cursor : Usize) (frame : Frame)
    (source : NodeState) (value : Usize) : DfsState := { s with
  state := s.state.set frame.node { source with lowlink := value }
  work := s.work.set top { frame with cursor := cursor } }

private theorem advance_invariant (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (top cursor value : Usize) (frame : Frame)
    (source : NodeState) (successors : alloc.vec.Vec Usize) (target : Usize)
    (htop : top.val + 1 = s.depth.val)
    (hframe : s.work.val[top.val]? = some frame)
    (hsource : s.state.val[frame.node.val]? = some source)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hcursor : cursor.val = frame.cursor.val + 1)
    (hlower : value.val ≤ source.lowlink.val)
    (hwitness : ∃ vertex ∈ s.active, value.val = rank s.state vertex ∧ Reach graph frame.node vertex)
    (hknown : target ∈ s.active ∨ s.finished target)
    (htarget_bound : target ∈ s.active → value.val ≤ rank s.state target) :
    DfsInvariant graph (advanceState s top cursor frame source value) := by
  let updated := advanceState s top cursor frame source value
  change DfsInvariant graph updated
  have hactive : updated.active = s.active := rfl
  have hgray : updated.gray = s.gray := cursor_set_gray s top cursor frame (by omega) hframe
  have hfinished : updated.finished = s.finished := rfl
  have hframes : updated.frames = s.frames.set top.val { frame with cursor := cursor } := by
    simp [updated, advanceState, DfsState.frames, List.take_set]
  have hframe_mem : frame ∈ s.frames := by
    apply List.mem_iff_getElem?.mpr
    refine ⟨top.val, ?_⟩
    simpa [DfsState.frames, List.getElem?_take_of_lt (by omega : top.val < s.depth.val)] using hframe
  have hrank : ∀ vertex, rank updated.state vertex = rank s.state vertex :=
    lowlink_set_rank s.state frame.node value source hsource
  have hlowlink : ∀ vertex, lowlink updated.state vertex =
      if vertex = frame.node then value.val else lowlink s.state vertex :=
    lowlink_set_value s.state frame.node value source hsource
  have hdecrease : ∀ vertex, lowlink updated.state vertex ≤ lowlink s.state vertex := by
    intro vertex
    rw [hlowlink]
    split
    · next heq => simpa [heq, lowlink, hsource] using hlower
    · exact Nat.le_refl _
  have howns : ∀ owner vertex, Owns updated owner vertex ↔ Owns s owner vertex := by
    intro owner vertex
    simp only [Owns, hactive, hgray, hrank]
  have hold_processed : ∀ current ∈ s.frames, ∀ vertex, Owns updated current.node vertex →
      ∀ neighbor, ProcessedEdge graph current vertex neighbor →
        (neighbor ∈ updated.active ∨ updated.finished neighbor) ∧
        (neighbor ∈ updated.active → lowlink updated.state current.node ≤ rank updated.state neighbor) := by
    intro current hcurrent vertex howner neighbor hedge
    have hold := h.processed current hcurrent vertex ((howns _ _).mp howner) neighbor hedge
    refine ⟨by simpa only [hactive, hfinished] using hold.1, ?_⟩
    intro hneighbor
    rw [hrank]
    exact (hdecrease current.node).trans (hold.2 (by simpa only [hactive] using hneighbor))
  refine {
    graph_valid := h.graph_valid
    state_size := by simpa [updated, advanceState] using h.state_size
    stack_size := h.stack_size
    work_size := by simpa [updated, advanceState] using h.work_size
    stack_bound := h.stack_bound
    work_bound := by simpa [updated, advanceState] using h.work_bound
    component_count := h.component_count
    discovery_count := ?_
    indices_bounded := ?_
    indices_unique := ?_
    lowlinks_bounded := ?_
    flags := ?_
    ordered := by simpa only [hactive, hrank] using h.ordered
    gray_sublist := by simpa only [hgray, hactive] using h.gray_sublist
    frame_bounds := ?_
    colors := ?_
    disjoint := h.disjoint
    components_unique := h.components_unique
    components_correct := h.components_correct
    finished_closed := h.finished_closed
    reaches_later := by simpa only [hgray, hactive, hrank] using h.reaches_later
    returns_to_gray := by simpa only [hgray, hactive, hrank] using h.returns_to_gray
    lowlink_witness := ?_
    processed := ?_ }
  · change s.next_index.val = ((s.state.set frame.node { source with lowlink := value }).val.filter
      (fun entry => entry.index.isSome)).length
    rw [lowlink_set_count s.state frame.node value source hsource]
    exact h.discovery_count
  · intro vertex entry index hentry hindex
    obtain ⟨old, hold, heq⟩ := lowlink_set_entry s.state frame.node value source hsource vertex entry hentry
    exact h.indices_bounded vertex old index hold (by simpa [heq, replaceLowlink] using hindex)
  · intro left right le re index hleft hright hle hre
    obtain ⟨lo, hlo, heql⟩ := lowlink_set_entry s.state frame.node value source hsource left le hleft
    obtain ⟨ro, hro, heqr⟩ := lowlink_set_entry s.state frame.node value source hsource right re hright
    exact h.indices_unique left right lo ro index hlo hro
      (by simpa [heql, replaceLowlink] using hle) (by simpa [heqr, replaceLowlink] using hre)
  · intro vertex entry index hentry hindex
    obtain ⟨old, hold, heq⟩ := lowlink_set_entry s.state frame.node value source hsource vertex entry hentry
    have hbound := h.lowlinks_bounded vertex old index hold (by simpa [heq, replaceLowlink] using hindex)
    have hchange := hdecrease vertex
    have hless : entry.lowlink.val ≤ old.lowlink.val := by
      simpa [lowlink, hentry, hold] using hchange
    omega
  · intro vertex entry hentry
    obtain ⟨old, hold, heq⟩ := lowlink_set_entry s.state frame.node value source hsource vertex entry hentry
    simpa [heq, replaceLowlink, hactive] using h.flags vertex old hold
  · intro current hcurrent
    rw [hframes] at hcurrent
    rcases List.mem_or_eq_of_mem_set hcurrent with hold | rfl
    · exact h.frame_bounds current hold
    · refine ⟨successors, hedges, ?_⟩
      have hbound : frame.cursor.val < successors.length := (List.getElem?_eq_some_iff.mp htarget).1
      change cursor.val ≤ successors.length
      omega
  · intro vertex
    change Discovered (s.state.set frame.node { source with lowlink := value }) vertex ↔
      vertex ∈ s.active ∨ s.finished vertex
    rw [lowlink_set_discovered s.state frame.node value source hsource]
    exact h.colors vertex
  · intro current hcurrent
    by_cases heq : current.node = frame.node
    · obtain ⟨vertex, hvertex, hvalue, hreach⟩ := hwitness
      refine ⟨vertex, hvertex, ?_, ?_⟩
      · simpa [hlowlink, hrank, heq] using hvalue
      · simpa [heq] using hreach
    · have hold : current ∈ s.frames := by
        rw [hframes] at hcurrent
        rcases List.mem_or_eq_of_mem_set hcurrent with hold | rfl
        · exact hold
        · exact False.elim (heq rfl)
      obtain ⟨vertex, hvertex, hvalue, hreach⟩ := h.lowlink_witness current hold
      exact ⟨vertex, hvertex, by simpa [hlowlink, hrank, heq] using hvalue, hreach⟩
  · intro current hcurrent vertex howner neighbor hedge
    rw [hframes] at hcurrent
    rcases List.mem_or_eq_of_mem_set hcurrent with hold | rfl
    · exact hold_processed current hold vertex howner neighbor hedge
    · by_cases heq : vertex = frame.node
      · subst vertex
        obtain ⟨neighbors, hneighbors, hneighbor⟩ := hedge.2.resolve_left (by simp)
        have heq : neighbors = successors := Option.some.inj (hneighbors.symm.trans hedges)
        subst neighbors
        have hbound := (List.getElem?_eq_some_iff.mp htarget).1
        have hsplit : neighbor ∈ successors.val.take frame.cursor.val ∨ neighbor = target := by
          simpa [hcursor, List.take_succ_eq_append_getElem hbound,
            (List.getElem?_eq_some_iff.mp htarget).2] using hneighbor
        rcases hsplit with hold | rfl
        · exact hold_processed frame hframe_mem frame.node howner neighbor
            ⟨hedge.1, Or.inr ⟨successors, hedges, hold⟩⟩
        · refine ⟨hknown, ?_⟩
          intro hmember
          simpa [hlowlink, hrank] using htarget_bound hmember
      · exact hold_processed frame hframe_mem vertex howner neighbor ⟨hedge.1, Or.inl heq⟩

theorem invariant_seen_preserved (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (frame : Frame) (successors : alloc.vec.Vec Usize)
    (target index : Usize) (entry source : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hentry : s.state.val[target.val]? = some entry) (hseen : entry.index = some index)
    (hsource : s.state.val[frame.node.val]? = some source) :
    dfs_body graph s ⦃ result => ∃ updated, DfsInvariant graph updated ∧ result = .cont updated.pack ⦄ := by
  let value := if entry.on_stack then min source.lowlink index else source.lowlink
  have hknown : target ∈ s.active ∨ s.finished target :=
    (h.colors target).mp ⟨entry, index, hentry, hseen⟩
  have hrank_target : rank s.state target = index.val := by simp [rank, hentry, hseen]
  have hlower : value.val ≤ source.lowlink.val := by
    have hle : value ≤ source.lowlink := by
      dsimp only [value]
      split
      · exact min_le_left _ _
      · exact le_refl _
    scalar_tac
  have hwitness : ∃ vertex ∈ s.active,
      value.val = rank s.state vertex ∧ Reach graph frame.node vertex := by
    have hold := h.lowlink_witness frame (top_frame_member s frame hpositive hframe)
    by_cases hflag : entry.on_stack = true
    · by_cases hle : source.lowlink ≤ index
      · simpa [value, hflag, min_eq_left hle, lowlink, hsource] using hold
      · have hright : index ≤ source.lowlink := le_of_lt (lt_of_not_ge hle)
        refine ⟨target, (h.flags target entry hentry).mp hflag, ?_, ?_⟩
        · simp [value, hflag, min_eq_right hright, hrank_target]
        · exact Relation.ReflTransGen.single
            ⟨successors, hedges, List.mem_iff_getElem?.mpr ⟨frame.cursor.val, htarget⟩⟩
    · simpa [value, hflag, lowlink, hsource] using hold
  have htarget_bound : target ∈ s.active → value.val ≤ rank s.state target := by
    intro hactive
    have hflag := (h.flags target entry hentry).mpr hactive
    have hle : value ≤ index := by simp [value, hflag]
    rw [hrank_target]
    scalar_tac
  have hsource_self : s.state.set frame.node source = s.state := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.set_val_eq]
    rw [← (List.getElem?_eq_some_iff.mp hsource).2,
      List.set_getElem_self (List.getElem?_eq_some_iff.mp hsource).1]
  have heffect : (if entry.on_stack then
        s.state.set frame.node { source with lowlink := min source.lowlink index } else s.state) =
      s.state.set frame.node { source with lowlink := value } := by
    by_cases hflag : entry.on_stack = true
    · simp [value, hflag]
    · simp [value, hflag, hsource_self]
  apply WP.spec_mono (dfs_seen_step graph s frame successors target index entry source
    hpositive hframe hedges htarget hentry hseen hsource)
  rintro result ⟨top, cursor, htop, hcursor, hresult⟩
  have htop_eq : top.val = s.depth.val - 1 := by omega
  refine ⟨advanceState s top cursor frame source value, ?_, ?_⟩
  · exact advance_invariant graph s h top cursor value frame source successors target htop
      (by simpa [htop_eq] using hframe) hsource hedges htarget hcursor
      hlower hwitness hknown htarget_bound
  · simpa only [heffect, advanceState] using hresult

end NibliSelfCheck.Scc
