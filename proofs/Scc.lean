/-
  Mechanized proof of nibli's SCC DECOMPOSITION (Track B, phase 3).

  The engine permits negation-as-failure only in stratified programs, enforced by
  `check_stratification` (`logji/src/rules.rs` :741), which groups the predicate dependency graph
  into strongly-connected components via Tarjan's algorithm (`compute_sccs` :647) and rejects a
  negative edge whose endpoints lie in one SCC.

  `Stratification.lean` proved the reachability CRITERION ("no negative edge whose target reaches
  its source") is equivalent to stratifiability. This file closes the remaining gap for the
  SCC-based check the engine actually runs:

    1. SCCs are the mutual-reachability equivalence classes — a well-defined partition. `SameSCC`
       is reflexive, symmetric, and transitive, so "the SCC decomposition" is unique: any two
       correct decompositions induce the same partition (`decomp_unique`), and a correct one always
       exists (`canonicalComp_correct`). This is the specification Tarjan must compute; verifying
       the imperative traversal (lowlink/stack) directly is out of scope — the real `compute_sccs`
       output is tied to this mutual-reachability spec by the corpus conformance test
       `compute_sccs_matches_scc_spec` in `logji/src/rules.rs`.

    2. The SCC-membership check equals the proven criterion: `SccRejects` (a negative edge with both
       endpoints in one SCC — exactly `check_stratification`) is EQUIVALENT to `RejectsByCriterion`
       (`sccRejects_iff_criterion`). Composed with `Stratification.lean`'s
       `RejectsByCriterion ↔ ¬Stratifiable`, this shows the SCC-based check rejects exactly the
       unstratifiable programs.

  Checked by `lean proofs/Scc.lean` (`just verify-proofs`). No mathlib — `funext`, `propext`, `cast`
  and the `Classical` namespace are Lean core. Self-contained: the graph/reachability model is
  duplicated from `Stratification.lean` (each proof file stands alone and offline).
-/

set_option linter.unusedSimpArgs false

namespace Nibli.SCC

open Classical

variable {n : Nat}

/-- A dependency edge (duplicated from `Stratification.lean`): conclusion `src` depends on condition
    `tgt`; `neg` is true iff the dependency is under negation-as-failure. -/
structure Edge (n : Nat) where
  src : Fin n
  tgt : Fin n
  neg : Bool

/-- The predicate dependency graph as an edge list. -/
abbrev Graph (n : Nat) := List (Edge n)

/-- A direct dependency edge `a → b` (ignoring sign). -/
def HasEdge (g : Graph n) (a b : Fin n) : Prop :=
  ∃ e ∈ g, e.src = a ∧ e.tgt = b

/-- Reachability: the reflexive-transitive closure of `HasEdge`. -/
inductive Reach (g : Graph n) : Fin n → Fin n → Prop
  | refl (a : Fin n) : Reach g a a
  | tail {a b c : Fin n} : Reach g a b → HasEdge g b c → Reach g a c

theorem Reach.of_edge {g : Graph n} {a b : Fin n} (h : HasEdge g a b) : Reach g a b :=
  Reach.tail (Reach.refl a) h

theorem Reach.trans {g : Graph n} {a b c : Fin n}
    (h1 : Reach g a b) (h2 : Reach g b c) : Reach g a c := by
  induction h2 with
  | refl => exact h1
  | tail _ e ih => exact Reach.tail ih e

/-- The check's reject condition (duplicated from `Stratification.lean`): a negative edge whose
    target reaches back to its source. -/
def RejectsByCriterion (g : Graph n) : Prop :=
  ∃ e ∈ g, e.neg ∧ Reach g e.tgt e.src

/- ── SCCs as mutual-reachability classes ─────────────────────────────────────────────────── -/

/-- Two nodes are in the same strongly-connected component iff each reaches the other. -/
def SameSCC (g : Graph n) (a b : Fin n) : Prop :=
  Reach g a b ∧ Reach g b a

theorem sameSCC_refl (g : Graph n) (a : Fin n) : SameSCC g a a :=
  ⟨Reach.refl a, Reach.refl a⟩

theorem sameSCC_symm {g : Graph n} {a b : Fin n} (h : SameSCC g a b) : SameSCC g b a :=
  ⟨h.2, h.1⟩

theorem sameSCC_trans {g : Graph n} {a b c : Fin n}
    (hab : SameSCC g a b) (hbc : SameSCC g b c) : SameSCC g a c :=
  ⟨Reach.trans hab.1 hbc.1, Reach.trans hbc.2 hab.2⟩

/-- For an edge in the graph, its endpoints are in one SCC iff the target reaches back to the
    source — the forward direction `Reach src tgt` is free from the edge itself. -/
theorem sameSCC_edge {g : Graph n} {e : Edge n} (he : e ∈ g) :
    SameSCC g e.src e.tgt ↔ Reach g e.tgt e.src := by
  constructor
  · intro h
    exact h.2
  · intro hback
    exact ⟨Reach.of_edge ⟨e, he, rfl, rfl⟩, hback⟩

/- ── The SCC-based stratification check equals the reachability criterion ─────────────────── -/

/-- The model of `check_stratification`: reject iff some negative edge has both endpoints in one
    SCC. -/
def SccRejects (g : Graph n) : Prop :=
  ∃ e ∈ g, e.neg ∧ SameSCC g e.src e.tgt

/-- The SCC-membership check the engine actually runs rejects EXACTLY when the reachability
    criterion does. Composed with `Stratification.lean`'s `RejectsByCriterion ↔ ¬Stratifiable`,
    the SCC-based check rejects exactly the unstratifiable programs. -/
theorem sccRejects_iff_criterion (g : Graph n) : SccRejects g ↔ RejectsByCriterion g := by
  constructor
  · intro h
    obtain ⟨e, he, hneg, hscc⟩ := h
    exact ⟨e, he, hneg, (sameSCC_edge he).mp hscc⟩
  · intro h
    obtain ⟨e, he, hneg, hback⟩ := h
    exact ⟨e, he, hneg, (sameSCC_edge he).mpr hback⟩

/- ── SCC decomposition: correctness, uniqueness, existence ────────────────────────────────── -/

/-- A decomposition labels each node with a component id. It is CORRECT iff two nodes share a label
    exactly when they lie in one SCC. `compute_sccs` returns such a labeling (its blocks). -/
def CorrectDecomp {κ : Type} (g : Graph n) (comp : Fin n → κ) : Prop :=
  ∀ a b, comp a = comp b ↔ SameSCC g a b

/-- A correct decomposition is exactly a sound (same label ⇒ same SCC) and complete (same SCC ⇒
    same label) one. -/
theorem correct_iff_sound_complete {κ : Type} (g : Graph n) (comp : Fin n → κ) :
    CorrectDecomp g comp ↔
      ((∀ a b, comp a = comp b → SameSCC g a b) ∧ (∀ a b, SameSCC g a b → comp a = comp b)) := by
  constructor
  · intro h
    exact ⟨fun a b => (h a b).mp, fun a b => (h a b).mpr⟩
  · intro h
    obtain ⟨hs, hc⟩ := h
    intro a b
    exact ⟨hs a b, hc a b⟩

/-- UNIQUENESS: any two correct decompositions induce the SAME partition — for all `a b` they agree
    on whether `a` and `b` share a component. So "the SCC partition" is well-defined and Tarjan's
    output is unique up to relabeling; the conformance test may compare `compute_sccs` to any one
    correct reference (mutual reachability). -/
theorem decomp_unique {κ₁ κ₂ : Type} (g : Graph n) (c1 : Fin n → κ₁) (c2 : Fin n → κ₂)
    (h1 : CorrectDecomp g c1) (h2 : CorrectDecomp g c2) :
    ∀ a b, (c1 a = c1 b ↔ c2 a = c2 b) := by
  intro a b
  rw [h1 a b, h2 a b]

/-- The canonical labeling: each node maps to its SCC, represented as the predicate `SameSCC g a`
    (its equivalence class). -/
def canonicalComp (g : Graph n) : Fin n → (Fin n → Prop) :=
  fun a => SameSCC g a

/-- EXISTENCE: the canonical labeling is a correct decomposition — so a correct SCC partition always
    exists (the spec is satisfiable, not vacuous). -/
theorem canonicalComp_correct (g : Graph n) : CorrectDecomp g (canonicalComp g) := by
  intro a b
  constructor
  · intro h
    -- `h : SameSCC g a = SameSCC g b`; apply at `a` and use reflexivity.
    have heq : SameSCC g a a = SameSCC g b a := congrFun h a
    have hba : SameSCC g b a := cast heq (sameSCC_refl g a)
    exact sameSCC_symm hba
  · intro hab
    funext x
    apply propext
    constructor
    · intro hax
      exact sameSCC_trans (sameSCC_symm hab) hax
    · intro hbx
      exact sameSCC_trans hab hbx

end Nibli.SCC
