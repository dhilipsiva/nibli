import SccTraversal

/- The positive closure rules used by nibli_checker.nibli's stratification
   criterion. These inductive relations specify the least closure of those
   rules; they do not assume that the production evaluator computes it.
   The result below connects this criterion to the actual indexed SCC kernel.
   Predicate-name encoding and evaluator refinement remain separate. -/
namespace NibliSelfCheck.Scc

open Aeneas Aeneas.Std
open nibli_reason.dependency_graph

/-- The two dep_path clauses: a direct edge, or a path followed by an edge. -/
inductive DepPath {α : Type} (edge : α → α → Prop) : α → α → Prop
  | direct {source target} : edge source target → DepPath edge source target
  | extend {source middle target} :
      DepPath edge source middle → edge middle target → DepPath edge source target

/-- The three neg_dep_path clauses. A negative edge anywhere in a path is
    sufficient; negative-edge parity is deliberately irrelevant. -/
inductive NegDepPath {α : Type} (edge negative : α → α → Prop) : α → α → Prop
  | direct {source target} : negative source target → NegDepPath edge negative source target
  | prepend {source middle target} :
      DepPath edge source middle → negative middle target → NegDepPath edge negative source target
  | extend {source middle target} :
      NegDepPath edge negative source middle → edge middle target → NegDepPath edge negative source target

theorem dep_path_reaches {α : Type} {edge : α → α → Prop} {source target : α}
    (h : DepPath edge source target) : Relation.ReflTransGen edge source target := by
  induction h with
  | direct hedge => exact .single hedge
  | extend _ hedge ih => exact .tail ih hedge

theorem reach_eq_or_dep_path {α : Type} {edge : α → α → Prop} {source target : α}
    (h : Relation.ReflTransGen edge source target) : source = target ∨ DepPath edge source target := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hedge ih =>
    apply Or.inr
    rcases ih with rfl | hpath
    · exact .direct hedge
    · exact .extend hpath hedge

theorem neg_path_append {α : Type} {edge negative : α → α → Prop} {source middle target : α}
    (hnegative : NegDepPath edge negative source middle)
    (hpath : Relation.ReflTransGen edge middle target) : NegDepPath edge negative source target := by
  induction hpath with
  | refl => exact hnegative
  | tail _ hedge ih => exact .extend ih hedge

/-- Exactly one marked negative edge separates an arbitrary prefix and suffix;
    either of those paths may itself contain additional negative edges. -/
theorem neg_path_iff_marked_edge {α : Type} {edge negative : α → α → Prop} {source target : α} :
    NegDepPath edge negative source target ↔ ∃ left right,
      Relation.ReflTransGen edge source left ∧ negative left right ∧
        Relation.ReflTransGen edge right target := by
  constructor
  · intro h
    induction h with
    | direct hnegative => exact ⟨_, _, .refl, hnegative, .refl⟩
    | prepend hpath hnegative => exact ⟨_, _, dep_path_reaches hpath, hnegative, .refl⟩
    | extend _ hedge ih =>
      obtain ⟨left, right, hprefix, hnegative, hsuffix⟩ := ih
      exact ⟨left, right, hprefix, hnegative, .tail hsuffix hedge⟩
  · rintro ⟨left, right, hprefix, hnegative, hsuffix⟩
    apply neg_path_append (middle := right) _ hsuffix
    rcases reach_eq_or_dep_path hprefix with rfl | hprefix
    · exact .direct hnegative
    · exact .prepend hprefix hnegative

/-- The checker's self-path query is exactly a negative edge with a return path. -/
theorem negative_cycle_iff_return_path {α : Type} (edge negative : α → α → Prop) :
    (∃ vertex, NegDepPath edge negative vertex vertex) ↔
      ∃ source target, negative source target ∧ Relation.ReflTransGen edge target source := by
  constructor
  · rintro ⟨vertex, hcycle⟩
    obtain ⟨source, target, hprefix, hnegative, hsuffix⟩ := neg_path_iff_marked_edge.mp hcycle
    exact ⟨source, target, hnegative, hsuffix.trans hprefix⟩
  · rintro ⟨source, target, hnegative, hreturn⟩
    exact ⟨source, neg_path_append (.direct hnegative) hreturn⟩

/-- The condition tested by an SCC-based negative-edge scan. This definition
    specifies that decision; it does not replace or assume correctness of the
    production scan through names, maps and sets. -/
def InternalNegative (components : alloc.vec.Vec (alloc.vec.Vec Usize))
    (negative : Usize → Usize → Prop) : Prop :=
  ∃ component ∈ components.val, ∃ source ∈ component.val, ∃ target ∈ component.val,
    negative source target

theorem partition_negative_cycle_iff (graph : Slice (alloc.vec.Vec Usize))
    (components : alloc.vec.Vec (alloc.vec.Vec Usize)) (hpartition : IsSccPartition graph components)
    (negative : Usize → Usize → Prop) (hnegative : ∀ source target, negative source target → Edge graph source target) :
    InternalNegative components negative ↔ ∃ vertex, NegDepPath (Edge graph) negative vertex vertex := by
  rw [negative_cycle_iff_return_path]
  constructor
  · rintro ⟨component, hcomponent, source, hsource, target, htarget, hedge⟩
    have hscc := hpartition.2.1 component hcomponent
    exact ⟨source, target, hedge, ((hscc.2.2 source hsource target).mp htarget).2⟩
  · rintro ⟨source, target, hedge, hreturn⟩
    obtain ⟨successors, hsuccessors, htarget⟩ := hnegative source target hedge
    have hsource : source.val < graph.length := (List.getElem?_eq_some_iff.mp hsuccessors).1
    obtain ⟨component, hcomponent, hmember⟩ := (hpartition.2.2 source).mp hsource
    have hscc := hpartition.2.1 component hcomponent
    refine ⟨component, hcomponent, source, hmember, target, ?_, hedge⟩
    exact (hscc.2.2 source hmember target).mpr ⟨.single ⟨successors, hsuccessors, htarget⟩, hreturn⟩

/-- The actual production kernel returns a partition whose internal-negative-
    edge criterion agrees with the checker's positive Horn closure criterion. -/
theorem compute_sccs_negative_cycle_criterion (graph : Slice (alloc.vec.Vec Usize))
    (hgraph : ValidGraph graph) (negative : Usize → Usize → Prop)
    (hnegative : ∀ source target, negative source target → Edge graph source target) :
    compute_sccs graph ⦃ components => IsSccPartition graph components ∧
      (InternalNegative components negative ↔ ∃ vertex, NegDepPath (Edge graph) negative vertex vertex) ⦄ := by
  apply WP.spec_mono (compute_sccs_correct graph hgraph)
  intro components hpartition
  exact ⟨hpartition, partition_negative_cycle_iff graph components hpartition negative hnegative⟩

end NibliSelfCheck.Scc
