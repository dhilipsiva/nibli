import SccInvariant

/- Termination of the extracted inner DFS loop, using its native state buffers. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow
open nibli_reason.dependency_graph

def unpackState (tuple : DfsTuple) : DfsState := {
  state := tuple.1, stack := tuple.2.1, stack_len := tuple.2.2.1,
  work := tuple.2.2.2.1, depth := tuple.2.2.2.2.1,
  components := tuple.2.2.2.2.2.1, next_index := tuple.2.2.2.2.2.2 }

private theorem unpack_pack (s : DfsState) : unpackState s.pack = s := rfl

def cursorSum (work : alloc.vec.Vec Frame) : Nat :=
  (work.val.map (fun frame => frame.cursor.val)).sum

def dfsMeasure (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState) : Nat × Nat × Nat :=
  (graph.length - s.next_index.val, graph.length * Usize.max - cursorSum s.work, s.depth.val)

private theorem cursor_sum_bound (work : alloc.vec.Vec Frame) :
    cursorSum work ≤ work.length * Usize.max := by
  change (work.val.map (fun frame => frame.cursor.val)).sum ≤ work.val.length * Usize.max
  generalize work.val = frames
  induction frames with
  | nil => simp
  | cons frame rest ih =>
    have hmax : frame.cursor.val ≤ Usize.max := by scalar_tac
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem cursor_sum_advance (frames : List Frame) (position : Nat) (frame : Frame) (cursor : Usize)
    (hframe : frames[position]? = some frame) (hcursor : cursor.val = frame.cursor.val + 1) :
    ((frames.set position { frame with cursor := cursor }).map (fun frame => frame.cursor.val)).sum =
      (frames.map (fun frame => frame.cursor.val)).sum + 1 := by
  induction frames generalizing position with
  | nil => simp at hframe
  | cons current rest ih =>
    cases position with
    | zero =>
      have heq : current = frame := by simpa using hframe
      simp [heq, hcursor, Nat.add_assoc, Nat.add_comm]
    | succ position =>
      have htail : rest[position]? = some frame := by simpa using hframe
      simpa [Nat.add_assoc] using congrArg (fun total => current.cursor.val + total) (ih position htail)

private theorem seen_decreases (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) (top cursor : Usize) (frame : Frame)
    (state : alloc.vec.Vec NodeState)
    (hframe : s.work.val[top.val]? = some frame) (hcursor : cursor.val = frame.cursor.val + 1) :
    WellFoundedRelation.rel (dfsMeasure graph { s with
      state := state, work := s.work.set top { frame with cursor := cursor } }) (dfsMeasure graph s) := by
  have hsum : cursorSum (s.work.set top { frame with cursor := cursor }) = cursorSum s.work + 1 := by
    simpa [cursorSum, alloc.vec.Vec.set_val_eq] using cursor_sum_advance s.work.val top.val frame cursor hframe hcursor
  have hbound := cursor_sum_bound (s.work.set top { frame with cursor := cursor })
  have hbudget : cursorSum (s.work.set top { frame with cursor := cursor }) ≤ graph.length * Usize.max := by
    simpa [h.work_size] using hbound
  apply Prod.Lex.right
  apply Prod.Lex.left
  change graph.length * Usize.max - cursorSum (s.work.set top { frame with cursor := cursor }) <
    graph.length * Usize.max - cursorSum s.work
  omega

private theorem discovery_decreases (graph : Slice (alloc.vec.Vec Usize)) (s updated : DfsState)
    (h : DfsInvariant graph updated) (hnext : updated.next_index.val = s.next_index.val + 1) :
    WellFoundedRelation.rel (dfsMeasure graph updated) (dfsMeasure graph s) := by
  have hbound : updated.next_index.val ≤ graph.length := by
    rw [h.discovery_count, ← h.state_size]
    exact List.length_filter_le _ _
  apply Prod.Lex.left
  change graph.length - updated.next_index.val < graph.length - s.next_index.val
  omega

private theorem completion_decreases (graph : Slice (alloc.vec.Vec Usize)) (s updated : DfsState)
    (hnext : updated.next_index = s.next_index) (hwork : updated.work = s.work)
    (hdepth : updated.depth.val + 1 = s.depth.val) :
    WellFoundedRelation.rel (dfsMeasure graph updated) (dfsMeasure graph s) := by
  simp only [dfsMeasure, hnext, hwork]
  apply Prod.Lex.right
  apply Prod.Lex.right
  change updated.depth.val < s.depth.val
  omega

private theorem invariant_result (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) :
    dfs_body graph s ⦃ result => match result with
      | .cont tuple => DfsInvariant graph (unpackState tuple)
      | .done tuple => DfsInvariant graph (unpackState tuple) ∧ (unpackState tuple).depth = 0#usize ⦄ := by
  apply WP.spec_mono (invariant_step_preserved graph s h)
  rintro result ⟨updated, hinvariant, hresult⟩
  rcases hresult with rfl | ⟨rfl, hdepth⟩
  · exact hinvariant
  · exact ⟨hinvariant, hdepth⟩

theorem dfs_step_decreases (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) :
    dfs_body graph s ⦃ result => match result with
      | .done _ => True
      | .cont tuple => WellFoundedRelation.rel (dfsMeasure graph (unpackState tuple)) (dfsMeasure graph s) ⦄ := by
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
      have hbound : s.depth.val ≤ s.work.val.length := h.work_bound
      omega
    let frame := s.work.val[s.depth.val - 1]'htop_bound
    have hframe : s.work.val[s.depth.val - 1]? = some frame := by simp [frame]
    have hframe_mem : frame ∈ s.frames := by
      apply List.mem_iff_getElem?.mpr
      refine ⟨s.depth.val - 1, ?_⟩
      simpa [DfsState.frames, List.getElem?_take_of_lt (by omega : s.depth.val - 1 < s.depth.val)] using hframe
    have hframe_gray : frame.node ∈ s.gray := List.mem_map.mpr ⟨frame, hframe_mem, rfl⟩
    obtain ⟨source, index, hsource, hindex⟩ :=
      (h.colors frame.node).mpr (Or.inl (h.gray_sublist.subset hframe_gray))
    obtain ⟨successors, hedges, _⟩ := h.frame_bounds frame hframe_mem
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
        apply WP.spec_mono (WP.spec_and (invariant_result graph s h)
          (dfs_discover_step graph s frame successors target entry hpositive hframe hedges htarget hentry hseen
            (by omega) (by omega) (by omega)))
        rintro result ⟨hinvariant, top, cursor, next, stack_len, depth, htop, hcursor, hnext,
          hstack_len, hdepth, rfl⟩
        exact discovery_decreases graph s _ hinvariant hnext
      | some discovered =>
        apply WP.spec_mono (dfs_seen_step graph s frame successors target discovered entry source
          hpositive hframe hedges htarget hentry hseen hsource)
        rintro result ⟨top, cursor, htop, hcursor, rfl⟩
        exact seen_decreases graph s h top cursor frame _
          (by simpa [show top.val = s.depth.val - 1 by omega] using hframe) hcursor
    · have hcomplete : successors.length ≤ frame.cursor.val := by omega
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
          have hparent_gray : parent.node ∈ s.gray := List.mem_map.mpr ⟨parent, hparent_mem, rfl⟩
          obtain ⟨parent_entry, _, hentry, _⟩ :=
            (h.colors parent.node).mpr (Or.inl (h.gray_sublist.subset hparent_gray))
          exact ⟨parent, parent_entry, fun _ => hparent, fun _ => hentry⟩
        · exact ⟨frame, source, fun h => False.elim (hdepth h), fun h => False.elim (hdepth h)⟩
      obtain ⟨parent, parent_entry, hparent, hparent_entry⟩ := hparent_exists
      by_cases hroot : index = source.lowlink
      · have hroot_index : source.index = some source.lowlink := hindex.trans (congrArg some hroot)
        obtain ⟨ready⟩ := invariant_root_ready graph s h frame successors source
          hpositive hframe hedges hcomplete hsource hroot_index
        apply WP.spec_mono (dfs_finish_root graph s frame parent successors source parent_entry
          hpositive hframe hedges hcomplete hsource hroot_index ready (by omega) hparent hparent_entry)
        rintro result ⟨top, cleared, remaining, output, components, htop, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
        exact completion_decreases graph s _ rfl rfl htop
      · apply WP.spec_mono (dfs_finish_nonroot graph s frame parent successors index source parent_entry
          hpositive hframe hedges hcomplete hsource hindex hroot hparent hparent_entry)
        rintro result ⟨top, htop, rfl⟩
        exact completion_decreases graph s _ rfl rfl htop
  · have hzero : s.depth = 0#usize := by scalar_tac
    rw [dfs_done graph s hzero]
    simp

/-- The complete production inner loop terminates from an invariant state and
    returns with both logical stacks empty. The outer traversal is separate. -/
theorem dfs_total (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (h : DfsInvariant graph s) :
    compute_sccs_loop0_loop0 graph s.state s.stack s.stack_len s.work s.depth s.components s.next_index
      ⦃ tuple => DfsInvariant graph (unpackState tuple) ∧ (unpackState tuple).depth = 0#usize ∧
        (unpackState tuple).stack_len = 0#usize ⦄ := by
  unfold compute_sccs_loop0_loop0
  apply loop.spec (γ := Nat × Nat × Nat) (measure := fun tuple => dfsMeasure graph (unpackState tuple))
    (inv := fun tuple => DfsInvariant graph (unpackState tuple))
  · intro tuple hinvariant
    rcases tuple with ⟨state, stack, stack_len, work, depth, components, next_index⟩
    let current : DfsState := ⟨state, stack, stack_len, work, depth, components, next_index⟩
    apply WP.spec_mono (WP.spec_and (invariant_result graph current hinvariant)
      (dfs_step_decreases graph current hinvariant))
    intro result hresult
    cases result with
    | done tuple =>
      obtain ⟨hinvariant, hdepth⟩ := hresult.1
      exact ⟨hinvariant, hdepth, (invariant_empty_dfs graph (unpackState tuple) hinvariant hdepth).1⟩
    | cont tuple => exact hresult
  · exact h

end NibliSelfCheck.Scc
