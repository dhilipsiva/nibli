import SccGraph

/- Proofs about the extracted production traversal. These local obligations
   are building blocks for SCC correctness, not a proof of the complete
   traversal or the predicate-name adapter. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow
open nibli_reason.dependency_graph

/-- The only state change licensed by emitting a component. -/
def clearEntry (removed : List Usize) (index : Nat) (entry : NodeState) : NodeState :=
  { entry with on_stack :=
      if removed.any (fun member => member.val == index) then false else entry.on_stack }

/-- Pointwise equality includes untouched entries and out-of-bounds lookups. -/
def Clears (before after : alloc.vec.Vec NodeState) (removed : List Usize) : Prop :=
  ∀ index, after.val[index]? = (before.val[index]?).map (clearEntry removed index)

/-- The flags in Rust state agree with membership of the logical stack. -/
def StackFlags (state : alloc.vec.Vec NodeState) (active : List Usize) : Prop :=
  ∀ vertex entry, state.val[vertex.val]? = some entry →
    (entry.on_stack = true ↔ vertex ∈ active)

private theorem any_index (removed : List Usize) (vertex : Usize) :
    removed.any (fun member => member.val == vertex.val) = decide (vertex ∈ removed) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨member, hmember, heq⟩
    exact UScalar.eq_of_val_eq heq ▸ hmember
  · intro hmember
    exact ⟨vertex, hmember, rfl⟩

private theorem clears_flags (before after : alloc.vec.Vec NodeState)
    (active removed : List Usize) (hclear : Clears before after removed)
    (hflags : StackFlags before active) :
    StackFlags after (active.filter (fun vertex => decide (vertex ∉ removed))) := by
  intro vertex entry hentry
  have hlookup := hclear vertex.val
  rw [hentry] at hlookup
  cases hold : before.val[vertex.val]? with
  | none => simp [hold] at hlookup
  | some original =>
    have heq : entry = clearEntry removed vertex.val original := by
      simpa [hold] using hlookup
    rw [heq]
    simp only [clearEntry, any_index]
    by_cases hremoved : vertex ∈ removed
    · simp [hremoved]
    · simpa [hremoved] using hflags vertex original hold

private theorem clears_rank (before after : alloc.vec.Vec NodeState)
    (removed : List Usize) (hclear : Clears before after removed) (vertex : Usize) :
    rank after vertex = rank before vertex := by
  simp only [rank, hclear vertex.val]
  cases before.val[vertex.val]? <;> simp [clearEntry]

private theorem clears_lowlink (before after : alloc.vec.Vec NodeState)
    (removed : List Usize) (hclear : Clears before after removed) (vertex : Usize) :
    lowlink after vertex = lowlink before vertex := by
  simp only [lowlink, hclear vertex.val]
  cases before.val[vertex.val]? <;> simp [clearEntry]

private theorem clears_empty (state : alloc.vec.Vec NodeState) : Clears state state [] := by
  intro index
  cases h : state.val[index]? with
  | none => simp
  | some entry => simp [clearEntry]

private theorem clears_step (before after : alloc.vec.Vec NodeState)
    (removed : List Usize) (member : Usize) (entry : NodeState)
    (hclear : Clears before after removed)
    (hentry : after.val[member.val]? = some entry) :
    Clears before (after.set member { entry with on_stack := false }) (removed ++ [member]) := by
  intro index
  simp only [alloc.vec.Vec.set_val_eq]
  by_cases heq : member.val = index
  · subst index
    have hbound := (List.getElem?_eq_some_iff.mp hentry).1
    rw [List.getElem?_set_self hbound]
    have hbefore := hclear member.val
    rw [hentry] at hbefore
    cases hold : before.val[member.val]? with
    | none => simp [hold] at hbefore
    | some original =>
      have he : entry = clearEntry removed member.val original := by
        simpa [hold] using hbefore
      simp [he, clearEntry]
  · rw [List.getElem?_set_ne heq, hclear index]
    cases hold : before.val[index]? with
    | none => simp
    | some original => simp [clearEntry, heq]

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
      output.val = ((stack.val.take length.val).drop position).reverse ∧
      Clears state updated output.val ⦄ := by
  let inv := fun (current : alloc.vec.Vec NodeState × Usize × alloc.vec.Vec Usize × Bool) =>
    match current with
    | (updated, remaining, output, complete) =>
      updated.length = state.length ∧ position ≤ remaining.val ∧
      remaining.val ≤ length.val ∧ output.length + remaining.val = length.val ∧
      (complete = true ↔ remaining.val = position) ∧
      output.val = ((stack.val.take length.val).drop remaining.val).reverse ∧
      Clears state updated output.val
  unfold pop_component pop_component_loop
  apply loop.spec_decr_nat (measure := fun (_, remaining, _, _) => remaining.val)
    (inv := inv)
  · rintro ⟨updated, remaining, output, complete⟩ hinv
    rcases hinv with ⟨hsize, hlow, hhigh, hcount, hcomplete, horder, hflags⟩
    dsimp only
    cases complete with
    | true =>
      rw [pop_done]
      simp only [WP.spec_ok]
      have heq := hcomplete.mp rfl
      exact ⟨hsize, heq, by omega, by simpa [heq] using horder, hflags⟩
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
        refine ⟨?_, by omega, by omega, by omega, ?_, hnew_order, ?_⟩
        · simpa using hsize
        · simpa using heq
        · rw [happended]
          exact clears_step state updated output.val member entry hflags hentry
      · omega
  · dsimp only [inv]
    refine ⟨rfl, Nat.le_of_lt hposition, Nat.le_refl _, ?_, ?_, ?_, ?_⟩
    · simp [alloc.vec.Vec.new]
    · simp only [Bool.false_eq_true, false_iff]
      omega
    · simp [alloc.vec.Vec.new]
    · exact clears_empty state

/-- The actual extracted removal emits a maximal SCC when the DFS root
    invariants hold. Establishing those invariants for every traversal branch
    remains a separate obligation. -/
theorem pop_component_scc (graph : Slice (alloc.vec.Vec Usize))
    (state : alloc.vec.Vec NodeState) (stack : Slice Usize)
    (length root : Usize) (position : Nat) (gray : List Usize) (finished : Usize → Prop)
    (hposition : position < length.val)
    (hlength : length.val ≤ stack.length)
    (hroot : stack.val[position]? = some root)
    (htargets : ∀ i, i < length.val → ∀ member,
      stack.val[i]? = some member → member.val < state.length)
    (hflags : StackFlags state (stack.val.take length.val))
    (horder : (stack.val.take length.val).Pairwise
      (fun left right => rank state left < rank state right))
    (hfrontier : RootFrontier graph state (stack.val.take length.val) gray finished root) :
    pop_component state stack length root ⦃ updated remaining output =>
      updated.length = state.length ∧ remaining.val = position ∧
      output.length + position = length.val ∧
      output.val = ((stack.val.take length.val).drop position).reverse ∧
      Clears state updated output.val ∧ output.val.Nodup ∧ IsScc graph output.val ∧
      Closed graph (fun vertex => vertex ∈ output.val ∨ finished vertex) ∧
      (∀ vertex, rank updated vertex = rank state vertex ∧
        lowlink updated vertex = lowlink state vertex) ∧
      StackFlags updated (stack.val.take remaining.val) ∧
      (stack.val.take remaining.val).Pairwise
        (fun left right => rank updated left < rank updated right) ⦄ := by
  let active := stack.val.take length.val
  have hactive_root : active[position]? = some root := by
    dsimp only [active]
    rw [List.getElem?_take_of_lt hposition]
    exact hroot
  have hlast : ∀ i, position < i → i < length.val → stack.val[i]? ≠ some root := by
    intro index habove hbelow heq
    have hindex : active[index]? = some root := by
      dsimp only [active]
      rw [List.getElem?_take_of_lt hbelow]
      exact heq
    have hlt := horder.rel_getElem_of_lt
      ((List.getElem?_eq_some_iff.mp hactive_root).1)
      ((List.getElem?_eq_some_iff.mp hindex).1) habove
    rw [(List.getElem?_eq_some_iff.mp hactive_root).2,
      (List.getElem?_eq_some_iff.mp hindex).2] at hlt
    omega
  apply WP.spec_mono (pop_component_total state stack length root position
    hposition hlength hroot hlast htargets)
  rintro ⟨updated, remaining, output⟩ ⟨hsize, hremaining, hcount, hsuffix, hclear⟩
  refine ⟨hsize, hremaining, hcount, hsuffix, hclear, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hnodup : active.Nodup := by
      apply List.Pairwise.imp _ horder
      intro left right hlt heq
      subst right
      omega
    rw [hsuffix]
    exact List.nodup_reverse.mpr (hnodup.drop)
  · apply scc_of_same_members graph _ output.val _
      (root_frontier_scc graph state active gray finished root hfrontier)
    intro vertex
    simp only [List.mem_filter, decide_eq_true_eq, hsuffix, List.mem_reverse]
    exact (rank_suffix_membership state active position root hactive_root horder vertex).symm
  · have hclosed := root_frontier_closed graph state active gray finished root hfrontier
    have hmembers : ∀ vertex, vertex ∈ output.val ↔
        vertex ∈ active.filter (fun vertex => decide (rank state root ≤ rank state vertex)) := by
      intro vertex
      simp only [List.mem_filter, decide_eq_true_eq, hsuffix, List.mem_reverse]
      exact rank_suffix_membership state active position root hactive_root horder vertex
    intro source target hsource hedge
    have hsource' : source ∈ active.filter
        (fun vertex => decide (rank state root ≤ rank state vertex)) ∨ finished source :=
      hsource.imp (hmembers source).mp id
    exact (hclosed source target hsource' hedge).imp (hmembers target).mpr id
  · intro vertex
    exact ⟨clears_rank state updated output.val hclear vertex,
      clears_lowlink state updated output.val hclear vertex⟩
  · have hnew_flags := clears_flags state updated active output.val hclear hflags
    intro vertex entry hentry
    rw [hnew_flags vertex entry hentry, hremaining]
    simp only [List.mem_filter, decide_eq_true_eq, hsuffix, List.mem_reverse]
    have hprefix := rank_prefix_membership state active position horder vertex
    have htake : active.take position = stack.val.take position := by
      simp [active, List.take_take, Nat.min_eq_left (Nat.le_of_lt hposition)]
    simpa [htake] using hprefix.symm
  · have hprefix : (stack.val.take position).Pairwise
        (fun left right => rank state left < rank state right) := by
      have h := horder.take (i := position)
      simpa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hposition)] using h
    simpa [hremaining, clears_rank state updated output.val hclear] using hprefix

/-- Names for the extracted loop's tuple fields; this introduces no traversal. -/
structure DfsState where
  state : alloc.vec.Vec NodeState
  stack : alloc.vec.Vec Usize
  stack_len : Usize
  work : alloc.vec.Vec Frame
  depth : Usize
  components : alloc.vec.Vec (alloc.vec.Vec Usize)
  next_index : Usize

abbrev DfsTuple := alloc.vec.Vec NodeState × alloc.vec.Vec Usize × Usize ×
  alloc.vec.Vec Frame × Usize × alloc.vec.Vec (alloc.vec.Vec Usize) × Usize

def DfsState.pack (s : DfsState) : DfsTuple :=
  (s.state, s.stack, s.stack_len, s.work, s.depth, s.components, s.next_index)

def dfs_body (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState) :
    Result (ControlFlow DfsTuple DfsTuple) :=
  compute_sccs_loop0_loop0.body graph s.state s.stack s.stack_len s.work s.depth
    s.components s.next_index

private theorem usize_min_eq (left right : Usize) :
    core.cmp.impls.OrdUsize.min left right = min left right := by
  by_cases h : right < left
  · simp only [core.cmp.impls.OrdUsize.min, h, ↓reduceIte]
    exact (min_eq_right (le_of_lt h)).symm
  · simp only [core.cmp.impls.OrdUsize.min, h, ↓reduceIte]
    exact (min_eq_left (le_of_not_gt h)).symm

theorem dfs_done (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (hempty : s.depth = 0#usize) : dfs_body graph s = .ok (.done s.pack) := by
  simp [dfs_body, compute_sccs_loop0_loop0.body, hempty, DfsState.pack]

theorem dfs_discover_step (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (frame : Frame) (successors : alloc.vec.Vec Usize) (target : Usize) (entry : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hentry : s.state.val[target.val]? = some entry) (hnew : entry.index = none)
    (hindex : s.next_index.val < Usize.max)
    (hstack : s.stack_len.val < s.stack.length)
    (hwork : s.depth.val < s.work.length) :
    dfs_body graph s ⦃ result => ∃ top cursor next stack_len depth,
      top.val + 1 = s.depth.val ∧ cursor.val = frame.cursor.val + 1 ∧
      next.val = s.next_index.val + 1 ∧ stack_len.val = s.stack_len.val + 1 ∧
      depth.val = s.depth.val + 1 ∧
      result = .cont (DfsState.pack { s with
        state := s.state.set target
          { index := some s.next_index, lowlink := s.next_index, on_stack := true },
        stack := s.stack.set s.stack_len target,
        stack_len := stack_len,
        work := (s.work.set top { frame with cursor := cursor }).set s.depth
          { node := target, cursor := 0#usize },
        depth := depth, next_index := next }) ⦄ := by
  have htop_bound : s.depth.val - 1 < s.work.length :=
    (List.getElem?_eq_some_iff.mp hframe).1
  have hnode_bound : frame.node.val < graph.length :=
    (List.getElem?_eq_some_iff.mp hedges).1
  have hcursor_bound : frame.cursor.val < successors.length :=
    (List.getElem?_eq_some_iff.mp htarget).1
  have htarget_bound : target.val < s.state.length :=
    (List.getElem?_eq_some_iff.mp hentry).1
  have hdepth_test : s.depth > 0#usize := by scalar_tac
  have hcursor_test : frame.cursor < alloc.vec.Vec.len successors := by scalar_tac
  unfold dfs_body compute_sccs_loop0_loop0.body
  simp only [hdepth_test, ↓reduceIte]
  step as ⟨top, htop⟩
  have htop_eq : top.val = s.depth.val - 1 := by omega
  step as ⟨actual_frame, hactual_frame⟩
  have hframe_eq : actual_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hactual_frame
  subst actual_frame
  simp only [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2]
  step as ⟨actual_edges, hactual_edges⟩
  have hedges_eq : actual_edges = successors := by
    simpa [(List.getElem?_eq_some_iff.mp hedges).2] using hactual_edges
  subst actual_edges
  simp only [(List.getElem?_eq_some_iff.mp hedges).2, hcursor_test, ↓reduceIte]
  step as ⟨actual_target, hactual_target⟩
  have htarget_eq : actual_target = target := by
    simpa [(List.getElem?_eq_some_iff.mp htarget).2] using hactual_target
  subst actual_target
  simp only [(List.getElem?_eq_some_iff.mp htarget).2]
  step as ⟨old_frame, frame_back, hold_frame, hframe_back⟩
  have hold_frame_eq : old_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hold_frame
  subst old_frame
  step as ⟨cursor, hcursor⟩
  step as ⟨actual_entry, hactual_entry⟩
  have hentry_eq : actual_entry = entry := by
    simpa [(List.getElem?_eq_some_iff.mp hentry).2] using hactual_entry
  subst actual_entry
  simp only [(List.getElem?_eq_some_iff.mp hentry).2, hnew]
  step as ⟨old_entry, state_back, hold_entry, hstate_back⟩
  step as ⟨next, hnext⟩
  step as ⟨old_stack, stack_back, hold_stack, hstack_back⟩
  step as ⟨stack_len, hstack_len⟩
  simp only [hframe_back]
  step as ⟨old_work, work_back, hold_work, hwork_back⟩
  step as ⟨depth, hdepth⟩
  refine ⟨top, cursor, next, stack_len, depth, by omega, ?_, hnext, hstack_len, hdepth, ?_⟩
  · simpa [hold_frame_eq] using hcursor
  · simp [DfsState.pack, hstate_back, hstack_back, hwork_back, hold_frame_eq]

theorem dfs_seen_step (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (frame : Frame) (successors : alloc.vec.Vec Usize) (target index : Usize)
    (entry source : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (htarget : successors.val[frame.cursor.val]? = some target)
    (hentry : s.state.val[target.val]? = some entry) (hseen : entry.index = some index)
    (hsource : s.state.val[frame.node.val]? = some source) :
    dfs_body graph s ⦃ result => ∃ top cursor,
      top.val + 1 = s.depth.val ∧ cursor.val = frame.cursor.val + 1 ∧
      result = .cont (DfsState.pack { s with
        state := if entry.on_stack then
          s.state.set frame.node { source with lowlink := min source.lowlink index }
          else s.state,
        work := s.work.set top { frame with cursor := cursor } }) ⦄ := by
  have htop_bound : s.depth.val - 1 < s.work.length :=
    (List.getElem?_eq_some_iff.mp hframe).1
  have hnode_bound : frame.node.val < graph.length :=
    (List.getElem?_eq_some_iff.mp hedges).1
  have hcursor_bound : frame.cursor.val < successors.length :=
    (List.getElem?_eq_some_iff.mp htarget).1
  have htarget_bound : target.val < s.state.length :=
    (List.getElem?_eq_some_iff.mp hentry).1
  have hsource_bound : frame.node.val < s.state.length :=
    (List.getElem?_eq_some_iff.mp hsource).1
  have hdepth_test : s.depth > 0#usize := by scalar_tac
  have hcursor_test : frame.cursor < alloc.vec.Vec.len successors := by scalar_tac
  unfold dfs_body compute_sccs_loop0_loop0.body
  simp only [hdepth_test, ↓reduceIte]
  step as ⟨top, htop⟩
  have htop_eq : top.val = s.depth.val - 1 := by omega
  step as ⟨actual_frame, hactual_frame⟩
  have hframe_eq : actual_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hactual_frame
  subst actual_frame
  simp only [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2]
  step as ⟨actual_edges, hactual_edges⟩
  have hedges_eq : actual_edges = successors := by
    simpa [(List.getElem?_eq_some_iff.mp hedges).2] using hactual_edges
  subst actual_edges
  simp only [(List.getElem?_eq_some_iff.mp hedges).2, hcursor_test, ↓reduceIte]
  step as ⟨actual_target, hactual_target⟩
  have htarget_eq : actual_target = target := by
    simpa [(List.getElem?_eq_some_iff.mp htarget).2] using hactual_target
  subst actual_target
  simp only [(List.getElem?_eq_some_iff.mp htarget).2]
  step as ⟨old_frame, frame_back, hold_frame, hframe_back⟩
  have hold_frame_eq : old_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hold_frame
  subst old_frame
  step as ⟨cursor, hcursor⟩
  step as ⟨actual_entry, hactual_entry⟩
  have hentry_eq : actual_entry = entry := by
    simpa [(List.getElem?_eq_some_iff.mp hentry).2] using hactual_entry
  subst actual_entry
  simp only [(List.getElem?_eq_some_iff.mp hentry).2, hseen]
  cases hflag : entry.on_stack with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨top, cursor, by omega, ?_, ?_⟩
    · simpa [hold_frame_eq] using hcursor
    · simp [DfsState.pack, hframe_back, hold_frame_eq]
  | true =>
    simp only [↓reduceIte]
    step as ⟨actual_source, hactual_source⟩
    have hsource_eq : actual_source = source := by
      simpa [(List.getElem?_eq_some_iff.mp hsource).2] using hactual_source
    subst actual_source
    step as ⟨minimum, hminimum⟩
    step as ⟨old_source, source_back, hold_source, hsource_back⟩
    refine ⟨top, cursor, by omega, ?_, ?_⟩
    · simpa [hold_frame_eq] using hcursor
    · simp [DfsState.pack, hframe_back, hsource_back, hold_frame_eq, hold_source, hminimum,
        (List.getElem?_eq_some_iff.mp hsource).2, usize_min_eq]

theorem dfs_finish_nonroot (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (frame parent : Frame) (successors : alloc.vec.Vec Usize) (index : Usize)
    (source parent_entry : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (hfinished : successors.length ≤ frame.cursor.val)
    (hsource : s.state.val[frame.node.val]? = some source)
    (hseen : source.index = some index) (hnonroot : index ≠ source.lowlink)
    (hparent : 1 < s.depth.val → s.work.val[s.depth.val - 2]? = some parent)
    (hparent_entry : 1 < s.depth.val → s.state.val[parent.node.val]? = some parent_entry) :
    dfs_body graph s ⦃ result => ∃ top,
      top.val + 1 = s.depth.val ∧
      result = .cont (DfsState.pack { s with
        depth := top,
        state := if 0 < top.val then
          s.state.set parent.node
            { parent_entry with lowlink := min parent_entry.lowlink source.lowlink }
          else s.state }) ⦄ := by
  have htop_bound : s.depth.val - 1 < s.work.length :=
    (List.getElem?_eq_some_iff.mp hframe).1
  have hnode_bound : frame.node.val < graph.length :=
    (List.getElem?_eq_some_iff.mp hedges).1
  have hsource_bound : frame.node.val < s.state.length :=
    (List.getElem?_eq_some_iff.mp hsource).1
  have hdepth_test : s.depth > 0#usize := by scalar_tac
  have hcursor_test : ¬ frame.cursor < alloc.vec.Vec.len successors := by scalar_tac
  unfold dfs_body compute_sccs_loop0_loop0.body
  simp only [hdepth_test, ↓reduceIte]
  step as ⟨top, htop⟩
  have htop_eq : top.val = s.depth.val - 1 := by omega
  step as ⟨actual_frame, hactual_frame⟩
  have hframe_eq : actual_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hactual_frame
  subst actual_frame
  simp only [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2]
  step as ⟨actual_edges, hactual_edges⟩
  have hedges_eq : actual_edges = successors := by
    simpa [(List.getElem?_eq_some_iff.mp hedges).2] using hactual_edges
  subst actual_edges
  simp only [(List.getElem?_eq_some_iff.mp hedges).2, hcursor_test, ↓reduceIte]
  step as ⟨actual_source, hactual_source⟩
  have hsource_eq : actual_source = source := by
    simpa [(List.getElem?_eq_some_iff.mp hsource).2] using hactual_source
  subst actual_source
  simp [(List.getElem?_eq_some_iff.mp hsource).2, hseen, hnonroot]
  by_cases habove : 0 < top.val
  · have hdepth : 1 < s.depth.val := by omega
    have hparent_lookup := hparent hdepth
    have hparent_source := hparent_entry hdepth
    have hparent_bound : s.depth.val - 2 < s.work.length :=
      (List.getElem?_eq_some_iff.mp hparent_lookup).1
    have hparent_state_bound : parent.node.val < s.state.length :=
      (List.getElem?_eq_some_iff.mp hparent_source).1
    simp only [habove, ↓reduceIte]
    step as ⟨parent_position, hparent_position⟩
    have hparent_position_eq : parent_position.val = s.depth.val - 2 := by omega
    step as ⟨actual_parent, hactual_parent⟩
    have hparent_eq : actual_parent = parent := by
      simpa [hparent_position_eq, (List.getElem?_eq_some_iff.mp hparent_lookup).2]
        using hactual_parent
    subst actual_parent
    simp only [hparent_position_eq, (List.getElem?_eq_some_iff.mp hparent_lookup).2]
    step as ⟨old_parent, hold_parent⟩
    step as ⟨old_source, hold_source⟩
    step as ⟨minimum, hminimum⟩
    step as ⟨parent_value, parent_back, hparent_value, hparent_back⟩
    refine ⟨top, by omega, ?_⟩
    simp [DfsState.pack, habove, hparent_back, hparent_value, hminimum, hold_parent,
      hold_source, (List.getElem?_eq_some_iff.mp hparent_source).2,
      (List.getElem?_eq_some_iff.mp hsource).2, usize_min_eq]
  · simp only [habove, ↓reduceIte, WP.spec_ok]
    exact ⟨top, by omega, by simp [DfsState.pack, habove]⟩

def DfsState.active (s : DfsState) : List Usize := s.stack.val.take s.stack_len.val

def DfsState.gray (s : DfsState) : List Usize :=
  (s.work.val.take s.depth.val).map (fun frame => frame.node)

def DfsState.finished (s : DfsState) (vertex : Usize) : Prop :=
  ∃ component ∈ s.components.val, vertex ∈ component.val

/-- Obligations that the full DFS invariant must supply at its root branch.
    Gray and completed vertices come from the actual extracted loop buffers. -/
structure EmissionReady (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (root : Usize) where
  position : Nat
  position_bound : position < s.stack_len.val
  stack_bound : s.stack_len.val ≤ s.stack.length
  root_position : s.stack.val[position]? = some root
  target_bounds : ∀ i, i < s.stack_len.val → ∀ member,
    s.stack.val[i]? = some member → member.val < s.state.length
  flags : StackFlags s.state s.active
  ordered : s.active.Pairwise (fun left right => rank s.state left < rank s.state right)
  frontier : RootFrontier graph s.state s.active s.gray s.finished root

theorem dfs_finish_root (graph : Slice (alloc.vec.Vec Usize)) (s : DfsState)
    (frame parent : Frame) (successors : alloc.vec.Vec Usize) (source parent_entry : NodeState)
    (hpositive : 0 < s.depth.val)
    (hframe : s.work.val[s.depth.val - 1]? = some frame)
    (hedges : graph.val[frame.node.val]? = some successors)
    (hfinished : successors.length ≤ frame.cursor.val)
    (hsource : s.state.val[frame.node.val]? = some source)
    (hroot : source.index = some source.lowlink)
    (ready : EmissionReady graph s frame.node)
    (hcapacity : s.components.length < Usize.max)
    (hparent : 1 < s.depth.val → s.work.val[s.depth.val - 2]? = some parent)
    (hparent_entry : 1 < s.depth.val → s.state.val[parent.node.val]? = some parent_entry) :
    dfs_body graph s ⦃ result => ∃ top updated remaining output components,
      top.val + 1 = s.depth.val ∧ remaining.val = ready.position ∧
      output.val = (s.active.drop ready.position).reverse ∧
      Clears s.state updated output.val ∧ output.val.Nodup ∧ IsScc graph output.val ∧
      Closed graph (fun vertex => vertex ∈ output.val ∨ s.finished vertex) ∧
      components.val = s.components.val ++ [output] ∧
      result = .cont (DfsState.pack { s with
        depth := top, stack_len := remaining, components := components,
        state := if 0 < top.val then updated.set parent.node
          { clearEntry output.val parent.node.val parent_entry with
            lowlink := min parent_entry.lowlink source.lowlink }
          else updated }) ⦄ := by
  have htop_bound : s.depth.val - 1 < s.work.length :=
    (List.getElem?_eq_some_iff.mp hframe).1
  have hnode_bound : frame.node.val < graph.length :=
    (List.getElem?_eq_some_iff.mp hedges).1
  have hsource_bound : frame.node.val < s.state.length :=
    (List.getElem?_eq_some_iff.mp hsource).1
  have hdepth_test : s.depth > 0#usize := by scalar_tac
  have hcursor_test : ¬ frame.cursor < alloc.vec.Vec.len successors := by scalar_tac
  have hderef : s.stack.deref = s.stack.slice := by
    simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
  have hpop := pop_component_scc graph s.state s.stack.slice s.stack_len frame.node
    ready.position s.gray s.finished ready.position_bound ready.stack_bound ready.root_position
    ready.target_bounds ready.flags ready.ordered ready.frontier
  unfold dfs_body compute_sccs_loop0_loop0.body
  simp only [hdepth_test, ↓reduceIte]
  step as ⟨top, htop⟩
  have htop_eq : top.val = s.depth.val - 1 := by omega
  step as ⟨actual_frame, hactual_frame⟩
  have hframe_eq : actual_frame = frame := by
    simpa [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2] using hactual_frame
  subst actual_frame
  simp only [htop_eq, (List.getElem?_eq_some_iff.mp hframe).2]
  step as ⟨actual_edges, hactual_edges⟩
  have hedges_eq : actual_edges = successors := by
    simpa [(List.getElem?_eq_some_iff.mp hedges).2] using hactual_edges
  subst actual_edges
  simp only [(List.getElem?_eq_some_iff.mp hedges).2, hcursor_test, ↓reduceIte]
  step as ⟨actual_source, hactual_source⟩
  have hsource_eq : actual_source = source := by
    simpa [(List.getElem?_eq_some_iff.mp hsource).2] using hactual_source
  subst actual_source
  simp [(List.getElem?_eq_some_iff.mp hsource).2, hroot, hderef]
  step with hpop as ⟨popped, hsize, hremaining, hcount, hsuffix,
    hclear, hnodup, hscc, hclosed, hmetadata, hflags, horder⟩
  rcases popped with ⟨updated, remaining, output⟩
  dsimp only at hsize hremaining hcount hsuffix hclear hnodup hscc hclosed hmetadata hflags horder ⊢
  step as ⟨components, hcomponents⟩
  by_cases habove : 0 < top.val
  · have hdepth : 1 < s.depth.val := by omega
    have hparent_lookup := hparent hdepth
    have hparent_source := hparent_entry hdepth
    have hparent_bound : s.depth.val - 2 < s.work.length :=
      (List.getElem?_eq_some_iff.mp hparent_lookup).1
    have hparent_state_bound : parent.node.val < updated.length := by
      rw [hsize]
      exact (List.getElem?_eq_some_iff.mp hparent_source).1
    have hsource_updated_bound : frame.node.val < updated.length := by omega
    have hparent_updated : updated.val[parent.node.val]? =
        some (clearEntry output.val parent.node.val parent_entry) := by
      rw [hclear, hparent_source]
      rfl
    have hsource_updated : updated.val[frame.node.val]? =
        some (clearEntry output.val frame.node.val source) := by
      rw [hclear, hsource]
      rfl
    simp only [habove, ↓reduceIte]
    step as ⟨parent_position, hparent_position⟩
    have hparent_position_eq : parent_position.val = s.depth.val - 2 := by omega
    step as ⟨actual_parent, hactual_parent⟩
    have hparent_eq : actual_parent = parent := by
      simpa [hparent_position_eq, (List.getElem?_eq_some_iff.mp hparent_lookup).2]
        using hactual_parent
    subst actual_parent
    simp only [hparent_position_eq, (List.getElem?_eq_some_iff.mp hparent_lookup).2]
    step as ⟨old_parent, hold_parent⟩
    step as ⟨old_source, hold_source⟩
    step as ⟨minimum, hminimum⟩
    step as ⟨parent_value, parent_back, hparent_value, hparent_back⟩
    refine ⟨top, by omega, updated, remaining, hremaining, output,
      hsuffix, hclear, hnodup, hscc, hclosed, components, hcomponents, ?_⟩
    simp [DfsState.pack, habove, hparent_back, hparent_value, hminimum, hold_parent,
      hold_source, (List.getElem?_eq_some_iff.mp hparent_updated).2,
      (List.getElem?_eq_some_iff.mp hsource_updated).2, clearEntry, usize_min_eq]
  · simp only [habove, ↓reduceIte, WP.spec_ok]
    exact ⟨top, by omega, updated, remaining, hremaining, output,
      hsuffix, hclear, hnodup, hscc, hclosed, components, hcomponents,
      by simp [DfsState.pack, habove]⟩

end NibliSelfCheck.Scc
