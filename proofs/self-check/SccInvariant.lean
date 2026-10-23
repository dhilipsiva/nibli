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

private theorem take_set_push {α : Type} (values : List α) (position : Nat) (value : α)
    (h : position < values.length) :
    (values.set position value).take (position + 1) = values.take position ++ [value] := by
  rw [List.take_succ_eq_append_getElem (by simpa using h), List.take_set_of_le (by omega)]
  simp

/-- Names the native discovery branch's writes without introducing a traversal. -/
def discoverState (s : DfsState) (top cursor next stack_len depth : Usize)
    (frame : Frame) (target : Usize) : DfsState := { s with
  state := s.state.set target
    { index := some s.next_index, lowlink := s.next_index, on_stack := true }
  stack := s.stack.set s.stack_len target
  stack_len := stack_len
  work := (s.work.set top { frame with cursor := cursor }).set s.depth
    { node := target, cursor := 0#usize }
  depth := depth
  next_index := next }

private theorem active_discovered (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (vertex : Usize) (hvertex : vertex ∈ s.active) :
    Discovered s.state vertex := (h.colors vertex).mpr (Or.inl hvertex)

private theorem discovered_rank_bound (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (vertex : Usize) (hvertex : Discovered s.state vertex) :
    rank s.state vertex < s.next_index.val := by
  obtain ⟨entry, index, hentry, hindex⟩ := hvertex
  simpa [rank, hentry, hindex] using h.indices_bounded vertex entry index hentry hindex

private theorem discover_invariant (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (top cursor next stack_len depth : Usize)
    (frame : Frame) (successors : alloc.vec.Vec Usize) (target : Usize) (entry : NodeState)
    (htop : top.val + 1 = s.depth.val)
    (hframe : s.work.val[top.val]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hentry : s.state.val[target.val]? = some entry) (hnew : entry.index = none)
    (hcursor : cursor.val = frame.cursor.val + 1)
    (hnext : next.val = s.next_index.val + 1)
    (hstack_len : stack_len.val = s.stack_len.val + 1)
    (hdepth : depth.val = s.depth.val + 1)
    (hstack : s.stack_len.val < s.stack.length)
    (hwork : s.depth.val < s.work.length) :
    DfsInvariant graph (discoverState s top cursor next stack_len depth frame target) := by
  let updated := discoverState s top cursor next stack_len depth frame target
  let fresh : NodeState :=
    { index := some s.next_index, lowlink := s.next_index, on_stack := true }
  change DfsInvariant graph updated
  have htarget_size := (List.getElem?_eq_some_iff.mp hentry).1
  have hnot_seen : ¬ Discovered s.state target := by
    rintro ⟨old, index, hold, hindex⟩
    have heq : old = entry := Option.some.inj (hold.symm.trans hentry)
    simp [heq, hnew] at hindex
  have hold_ne : ∀ vertex, Discovered s.state vertex → vertex ≠ target := by
    intro vertex hvertex heq
    exact hnot_seen (heq ▸ hvertex)
  have hlookup : ∀ (vertex : Usize), updated.state.val[vertex.val]? =
      if vertex = target then some fresh else s.state.val[vertex.val]? := by
    intro vertex
    change (s.state.set target fresh).val[vertex.val]? = _
    rw [alloc.vec.Vec.set_val_eq]
    by_cases heq : vertex = target
    · subst vertex
      simp [htarget_size]
    · have hne : target.val ≠ vertex.val := fun equal => heq (UScalar.eq_of_val_eq equal.symm)
      simp [heq, List.getElem?_set_ne hne]
  have hdiscovered : ∀ vertex, Discovered updated.state vertex ↔
      vertex = target ∨ Discovered s.state vertex := by
    intro vertex
    by_cases heq : vertex = target
    · subst vertex
      simp [Discovered, hlookup, fresh]
    · simp [Discovered, hlookup, heq]
  have hrank : ∀ vertex, rank updated.state vertex =
      if vertex = target then s.next_index.val else rank s.state vertex := by
    intro vertex
    by_cases heq : vertex = target <;> simp [rank, hlookup, heq, fresh]
  have hrank_old : ∀ vertex, Discovered s.state vertex →
      rank updated.state vertex = rank s.state vertex := by
    intro vertex hvertex
    simp [hrank, hold_ne vertex hvertex]
  have hlowlink : ∀ vertex, lowlink updated.state vertex =
      if vertex = target then s.next_index.val else lowlink s.state vertex := by
    intro vertex
    by_cases heq : vertex = target <;> simp [lowlink, hlookup, heq, fresh]
  have hlowlink_old : ∀ vertex, Discovered s.state vertex →
      lowlink updated.state vertex = lowlink s.state vertex := by
    intro vertex hvertex
    simp [hlowlink, hold_ne vertex hvertex]
  have hactive : updated.active = s.active ++ [target] := by
    change (s.stack.set s.stack_len target).val.take stack_len.val = _
    rw [hstack_len, alloc.vec.Vec.set_val_eq, take_set_push _ _ _ hstack]
    rfl
  have hframes : updated.frames =
      s.frames.set top.val { frame with cursor := cursor } ++ [{ node := target, cursor := 0#usize }] := by
    change (((s.work.set top { frame with cursor := cursor }).set s.depth
      { node := target, cursor := 0#usize }).val.take depth.val) = _
    rw [hdepth, alloc.vec.Vec.set_val_eq, take_set_push _ _ _ (by simpa using hwork)]
    simp [alloc.vec.Vec.set_val_eq, List.take_set, DfsState.frames]
  have hgray : updated.gray = s.gray ++ [target] := by
    change updated.frames.map (fun frame => frame.node) = _
    rw [hframes, List.map_append]
    have hcursor_gray := cursor_set_gray s top cursor frame (by omega) hframe
    simpa [alloc.vec.Vec.set_val_eq, List.take_set, DfsState.frames] using
      congrArg (fun vertices => vertices ++ [target]) hcursor_gray
  have hframe_mem : frame ∈ s.frames := by
    apply top_frame_member s frame (by omega)
    simpa [show top.val = s.depth.val - 1 by omega] using hframe
  have hframe_gray : frame.node ∈ s.gray := List.mem_map.mpr ⟨frame, hframe_mem, rfl⟩
  have hframe_seen := frame_discovered graph s h frame hframe_mem
  have htopmost := topmost_rank graph s h frame (by omega)
    (by simpa [show top.val = s.depth.val - 1 by omega] using hframe)
  have hedge : Edge graph frame.node target :=
    ⟨successors, hedges, List.mem_iff_getElem?.mpr ⟨frame.cursor.val, htarget⟩⟩
  have hfinished : updated.finished = s.finished := rfl
  have hactive_seen := active_discovered graph s h
  have hgray_seen : ∀ vertex ∈ s.gray, Discovered s.state vertex :=
    fun vertex hvertex => hactive_seen vertex (h.gray_sublist.subset hvertex)
  have hrank_bound := discovered_rank_bound graph s h
  have hold_owns : ∀ owner ∈ s.gray, ∀ vertex, Owns updated owner vertex → Owns s owner vertex := by
    intro owner howner vertex ⟨hvertex, hranks, hlater⟩
    have howner_seen := hgray_seen owner howner
    have hvertex_old : vertex ∈ s.active := by
      rw [hactive, List.mem_append, List.mem_singleton] at hvertex
      rcases hvertex with hold | heq
      · exact hold
      · subst vertex
        have himpossible := hlater target (by simp [hgray])
          (by simpa [hrank, hold_ne owner howner_seen] using hrank_bound owner howner_seen)
        omega
    have hvertex_seen := hactive_seen vertex hvertex_old
    refine ⟨hvertex_old, ?_, ?_⟩
    · simpa [hrank_old owner howner_seen, hrank_old vertex hvertex_seen] using hranks
    · intro later hmember hless
      have hlater_seen := hgray_seen later hmember
      have hbound := hlater later (by simp [hgray, hmember])
        (by simpa [hrank_old owner howner_seen, hrank_old later hlater_seen] using hless)
      simpa [hrank_old vertex hvertex_seen, hrank_old later hlater_seen] using hbound
  have hold_processed : ∀ current ∈ s.frames, ∀ vertex, Owns updated current.node vertex →
      ∀ neighbor, ProcessedEdge graph current vertex neighbor →
        (neighbor ∈ updated.active ∨ updated.finished neighbor) ∧
        (neighbor ∈ updated.active → lowlink updated.state current.node ≤ rank updated.state neighbor) := by
    intro current hcurrent vertex howner neighbor hprocessed
    have hcurrent_gray : current.node ∈ s.gray := List.mem_map.mpr ⟨current, hcurrent, rfl⟩
    have hold := h.processed current hcurrent vertex
      (hold_owns current.node hcurrent_gray vertex howner) neighbor hprocessed
    have hneighbor_seen := (h.colors neighbor).mpr hold.1
    refine ⟨hold.1.imp (fun hmem => by simp [hactive, hmem]) id, ?_⟩
    intro hneighbor
    have hneighbor_old : neighbor ∈ s.active := by
      simpa [hactive, hold_ne neighbor hneighbor_seen] using hneighbor
    rw [hlowlink_old current.node (hgray_seen current.node hcurrent_gray),
      hrank_old neighbor hneighbor_seen]
    exact hold.2 hneighbor_old
  refine {
    graph_valid := h.graph_valid
    state_size := by simpa [updated, discoverState] using h.state_size
    stack_size := by simpa [updated, discoverState] using h.stack_size
    work_size := by simpa [updated, discoverState] using h.work_size
    stack_bound := by simpa [updated, discoverState, hstack_len] using hstack
    work_bound := by simpa [updated, discoverState, hdepth] using hwork
    component_count := by
      change s.components.length + stack_len.val ≤ next.val
      have := h.component_count
      omega
    discovery_count := ?_
    indices_bounded := ?_
    indices_unique := ?_
    lowlinks_bounded := ?_
    flags := ?_
    ordered := ?_
    gray_sublist := by rw [hgray, hactive]; exact h.gray_sublist.append_right _
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
  · change next.val = ((s.state.set target fresh).val.filter
      (fun entry => entry.index.isSome)).length
    rw [alloc.vec.Vec.set_val_eq, ← List.countP_eq_length_filter, List.countP_set htarget_size]
    simpa [fresh, (List.getElem?_eq_some_iff.mp hentry).2, hnew,
      List.countP_eq_length_filter, ← h.discovery_count] using hnext
  · intro vertex current index hcurrent hindex
    rw [hlookup] at hcurrent
    by_cases heq : vertex = target
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
    by_cases hl : left = target <;> by_cases hr : right = target
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
    by_cases heq : vertex = target
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hcurrent
      have hi : index = s.next_index := by simpa [← hcurrent, fresh] using hindex.symm
      simp [← hcurrent, fresh, hi]
    · simp only [heq, ↓reduceIte] at hcurrent
      exact h.lowlinks_bounded vertex current index hcurrent hindex
  · intro vertex current hcurrent
    rw [hlookup] at hcurrent
    by_cases heq : vertex = target
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hcurrent
      simp [← hcurrent, fresh, hactive, heq]
    · simp only [heq, ↓reduceIte] at hcurrent
      simpa [hactive, heq] using h.flags vertex current hcurrent
  · rw [hactive, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · apply h.ordered.imp_of_mem
      intro left right hleft hright hless
      simpa [hrank_old left (hactive_seen left hleft), hrank_old right (hactive_seen right hright)]
        using hless
    · intro left hleft right hright
      have heq : right = target := by simpa using hright
      subst right
      simpa [hrank, hold_ne left (hactive_seen left hleft)] using
        hrank_bound left (hactive_seen left hleft)
  · intro current hcurrent
    rw [hframes, List.mem_append, List.mem_singleton] at hcurrent
    rcases hcurrent with hold | rfl
    · rcases List.mem_or_eq_of_mem_set hold with hold | rfl
      · exact h.frame_bounds current hold
      · refine ⟨successors, hedges, ?_⟩
        have : frame.cursor.val < successors.length := (List.getElem?_eq_some_iff.mp htarget).1
        change cursor.val ≤ successors.length
        omega
    · have hvalid := h.graph_valid frame.node.val successors hedges target
        (List.mem_iff_getElem?.mpr ⟨frame.cursor.val, htarget⟩)
      exact ⟨graph.val[target.val]'hvalid, by simp, by simp⟩
  · intro vertex
    rw [hdiscovered, hactive, hfinished, h.colors]
    simp only [List.mem_append, List.mem_singleton]
    tauto
  · intro vertex hvertex hdone
    rw [hactive, List.mem_append, List.mem_singleton] at hvertex
    rcases hvertex with hold | heq
    · exact h.disjoint vertex hold hdone
    · subst vertex
      exact hnot_seen ((h.colors target).mpr (Or.inr hdone))
  · intro ancestor hancestor vertex hvertex hless
    rw [hgray, List.mem_append, List.mem_singleton] at hancestor
    rw [hactive, List.mem_append, List.mem_singleton] at hvertex
    rcases hancestor with ha | rfl <;> rcases hvertex with hv | rfl
    · apply h.reaches_later ancestor ha vertex hv
      simpa [hrank_old ancestor (hgray_seen ancestor ha), hrank_old vertex (hactive_seen vertex hv)]
        using hless
    · exact (h.reaches_later ancestor ha frame.node (h.gray_sublist.subset hframe_gray)
        (htopmost ancestor ha)).tail hedge
    · have hbound := hrank_bound vertex (hactive_seen vertex hv)
      rw [hrank_old vertex (hactive_seen vertex hv), hrank] at hless
      simp only [↓reduceIte] at hless
      omega
    · exact Relation.ReflTransGen.refl
  · intro vertex hvertex
    rw [hactive, List.mem_append, List.mem_singleton] at hvertex
    rcases hvertex with hold | heq
    · obtain ⟨ancestor, ha, hle, hreach⟩ := h.returns_to_gray vertex hold
      refine ⟨ancestor, by simp [hgray, ha], ?_, hreach⟩
      simpa [hrank_old ancestor (hgray_seen ancestor ha), hrank_old vertex (hactive_seen vertex hold)]
        using hle
    · subst vertex
      exact ⟨target, by simp [hgray], Nat.le_refl _, Relation.ReflTransGen.refl⟩
  · intro current hcurrent
    rw [hframes, List.mem_append, List.mem_singleton] at hcurrent
    rcases hcurrent with hold | rfl
    · have hnode : ∃ old ∈ s.frames, current.node = old.node := by
        rcases List.mem_or_eq_of_mem_set hold with hold | rfl
        · exact ⟨current, hold, rfl⟩
        · exact ⟨frame, hframe_mem, rfl⟩
      obtain ⟨old, hold, hnode⟩ := hnode
      obtain ⟨vertex, hvertex, hvalue, hreach⟩ := h.lowlink_witness old hold
      refine ⟨vertex, by simp [hactive, hvertex], ?_, by simpa [hnode] using hreach⟩
      simpa [hnode, hlowlink_old old.node (frame_discovered graph s h old hold),
        hrank_old vertex (hactive_seen vertex hvertex)] using hvalue
    · exact ⟨target, by simp [hactive], by simp [hlowlink, hrank], Relation.ReflTransGen.refl⟩
  · intro current hcurrent vertex howner neighbor hprocessed
    rw [hframes, List.mem_append, List.mem_singleton] at hcurrent
    rcases hcurrent with hold | rfl
    · rcases List.mem_or_eq_of_mem_set hold with hold | rfl
      · exact hold_processed current hold vertex howner neighbor hprocessed
      · by_cases heq : vertex = frame.node
        · subst vertex
          obtain ⟨neighbors, hneighbors, hneighbor⟩ := hprocessed.2.resolve_left (by simp)
          have heq : neighbors = successors := Option.some.inj (hneighbors.symm.trans hedges)
          subst neighbors
          have hbound := (List.getElem?_eq_some_iff.mp htarget).1
          have hsplit : neighbor ∈ successors.val.take frame.cursor.val ∨ neighbor = target := by
            simpa [hcursor, List.take_succ_eq_append_getElem hbound,
              (List.getElem?_eq_some_iff.mp htarget).2] using hneighbor
          rcases hsplit with hold | rfl
          · exact hold_processed frame hframe_mem frame.node howner neighbor
              ⟨hprocessed.1, Or.inr ⟨successors, hedges, hold⟩⟩
          · refine ⟨Or.inl (by simp [hactive]), ?_⟩
            intro _
            obtain ⟨source, index, hsource, hindex⟩ := hframe_seen
            have hle := h.lowlinks_bounded frame.node source index hsource hindex
            have hlt := h.indices_bounded frame.node source index hsource hindex
            simp only [hlowlink_old frame.node ⟨source, index, hsource, hindex⟩, hrank,
              ↓reduceIte]
            simpa [lowlink, hsource] using Nat.le_trans hle (Nat.le_of_lt hlt)
        · exact hold_processed frame hframe_mem vertex howner neighbor ⟨hprocessed.1, Or.inl heq⟩
    · have hvertex : vertex = target := by
        have hmember := howner.1
        rw [hactive, List.mem_append, List.mem_singleton] at hmember
        rcases hmember with hold | heq
        · have hbound := hrank_bound vertex (hactive_seen vertex hold)
          have hless := howner.2.1
          rw [hrank_old vertex (hactive_seen vertex hold), hrank] at hless
          simp only [↓reduceIte] at hless
          omega
        · exact heq
      subst vertex
      obtain ⟨_, _, himpossible⟩ := hprocessed.2.resolve_left (by simp)
      simp at himpossible

theorem invariant_discover_preserved (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (frame : Frame) (successors : alloc.vec.Vec Usize)
    (target : Usize) (entry : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hentry : s.state.val[target.val]? = some entry) (hnew : entry.index = none) :
    dfs_body graph s ⦃ result => ∃ updated, DfsInvariant graph updated ∧ result = .cont updated.pack ⦄ := by
  have hnext_bound : s.next_index.val < s.state.length := by
    rw [h.discovery_count]
    apply List.length_filter_lt_length_iff_exists.mpr
    refine ⟨entry, List.mem_iff_getElem?.mpr ⟨target.val, hentry⟩, ?_⟩
    simp [hnew]
  have hgray_length : s.gray.length = s.depth.val := by
    simp [DfsState.gray, Nat.min_eq_left h.work_bound]
  have hactive_length : s.active.length = s.stack_len.val := by
    simp [DfsState.active, Nat.min_eq_left h.stack_bound]
  have hdepth_stack : s.depth.val ≤ s.stack_len.val := by
    have := h.gray_sublist.length_le
    omega
  have hcounts := h.component_count
  have hstate_size := h.state_size
  have hstack_size := h.stack_size
  have hwork_size := h.work_size
  have hmachine : s.state.length ≤ Usize.max := s.state.property
  have hstack : s.stack_len.val < s.stack.length := by omega
  have hwork : s.depth.val < s.work.length := by omega
  apply WP.spec_mono (dfs_discover_step graph s frame successors target entry
    hpositive hframe hedges htarget hentry hnew (by omega) hstack hwork)
  rintro result ⟨top, cursor, next, stack_len, depth, htop, hcursor, hnext,
    hstack_len, hdepth, hresult⟩
  refine ⟨discoverState s top cursor next stack_len depth frame target, ?_, hresult⟩
  exact discover_invariant graph s h top cursor next stack_len depth frame successors target entry
    htop (by simpa [show top.val = s.depth.val - 1 by omega] using hframe)
    hedges htarget hentry hnew hcursor hnext hstack_len hdepth hstack hwork

end NibliSelfCheck.Scc
