/-
  Mechanized proof of nibli's NAF STRATIFICATION CRITERION (Track B, phase 2).

  The engine permits negation-as-failure only in *stratified* programs and enforces this at
  rule-registration time: it builds a predicate dependency graph and rejects any rule that would
  put a negation edge on a cycle (`logji/src/rules.rs` `check_stratification` :741 / `compute_sccs`
  :647). This is soundness-critical — NAF over a recursive cycle is unsound.

  This file proves the CRITERION is correct: over the dependency graph, "no negative edge has its
  target reaching back to its source" (≡ no negative edge with both endpoints in one SCC, which is
  exactly what the Rust check rejects on) is EQUIVALENT to "a valid stratification (level function)
  exists." That gives both the soundness direction (the check accepts ⇒ the program is genuinely
  stratifiable) and completeness (it never rejects a stratifiable program).

  Correspondence (`logji/src/rules.rs`): an edge is conclusion `H` → condition `B` with `neg=true`
  iff the dependency is negated (graph built at :542); `check_stratification` (:741) rejects iff
  some SCC contains a negative edge whose both endpoints lie in it. The real Tarjan-based check is
  tied to this criterion by the corpus conformance test `mod stratification_conformance` in
  `logji/src/rules.rs`.

  Checked by `lean proofs/Stratification.lean` (`just verify-proofs`). No mathlib — `Classical`,
  `List.finRange`, and `List.countP` are Lean core. The combiner gave a complete (finite-domain)
  guarantee; here graphs are unbounded, so the Rust bridge is a corpus test, not exhaustive.
-/

set_option linter.unusedSimpArgs false

namespace Nibli.Strat

open Classical

variable {n : Nat}

/-- A dependency edge: conclusion `src` (= `H`) depends on condition `tgt` (= `B`); `neg` is true
    iff the dependency is under negation-as-failure. -/
structure Edge (n : Nat) where
  src : Fin n
  tgt : Fin n
  neg : Bool

/-- The predicate dependency graph as an edge list (mirrors `HashMap<String, Vec<(String,bool)>>`,
    flattened). -/
abbrev Graph (n : Nat) := List (Edge n)

/-- There is a direct dependency edge `a → b` (ignoring sign). -/
def HasEdge (g : Graph n) (a b : Fin n) : Prop :=
  ∃ e ∈ g, e.src = a ∧ e.tgt = b

/-- Reachability: the reflexive-transitive closure of `HasEdge` (sign-ignoring). -/
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

/-- A valid stratification: a level (stratum) for each predicate such that a negated dependency
    drops the stratum strictly and a positive dependency does not raise it. (Edge `src → tgt`, so
    the dependent `src` sits strictly above a negated dependency `tgt`, weakly above a positive
    one.) -/
def Stratifiable (g : Graph n) : Prop :=
  ∃ lvl : Fin n → Nat, ∀ e ∈ g,
    if e.neg then lvl e.src > lvl e.tgt else lvl e.src ≥ lvl e.tgt

/-- The graph criterion the check tests, stated as the *good* case: no negative edge whose target
    reaches back to its source. Since the edge already gives `Reach g e.src e.tgt`, "tgt reaches
    src" ⇔ src and tgt are in one SCC, so this is exactly the negation of the Rust reject
    condition. -/
def NoNegCycle (g : Graph n) : Prop :=
  ∀ e ∈ g, e.neg → ¬ Reach g e.tgt e.src

/-- The check's reject condition: a negative edge with both endpoints in one SCC. -/
def RejectsByCriterion (g : Graph n) : Prop :=
  ∃ e ∈ g, e.neg ∧ Reach g e.tgt e.src

/- ── Two short `List.countP` lemmas (proved locally; no mathlib). ── -/

theorem countP_mono {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) → l.countP p ≤ l.countP q := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    have hsub : ∀ x ∈ t, p x = true → q x = true := fun x hx => h x (List.mem_cons_of_mem a hx)
    have ht := ih hsub
    rw [List.countP_cons, List.countP_cons]
    by_cases hpa : p a = true
    · have hqa : q a = true := h a List.mem_cons_self hpa
      simp [hpa, hqa]; omega
    · simp only [Bool.not_eq_true] at hpa
      simp [hpa]
      by_cases hqa : q a = true <;> simp [hqa] <;> omega

theorem countP_lt {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      ∀ {x : α}, x ∈ l → p x = false → q x = true → l.countP p < l.countP q := by
  intro l
  induction l with
  | nil => intro _ x hx _ _; simp at hx
  | cons a t ih =>
    intro hmono x hx hpx hqx
    have hsub : ∀ y ∈ t, p y = true → q y = true := fun y hy => hmono y (List.mem_cons_of_mem a hy)
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · -- x = a: p a = false (hpx), q a = true (hqx).
      have ht := countP_mono (l := t) hsub
      simp [hpx, hqx]; omega
    · -- x ∈ t: strict on the tail; the head only adds q ≥ p.
      have hlt := ih hsub hxt hpx hqx
      by_cases hpa : p a = true
      · have hqa : q a = true := hmono a List.mem_cons_self hpa
        simp [hpa, hqa]; omega
      · simp only [Bool.not_eq_true] at hpa
        simp [hpa]
        by_cases hqa : q a = true <;> simp [hqa] <;> omega

/- ── The level function: how many nodes a node can reach. ── -/

/-- `level g a` = the number of nodes reachable from `a` (including `a`). Noncomputable: it counts
    a classically-decidable predicate, which is fine for a proof (we prove a level function
    *exists*; we do not run it). -/
noncomputable def level (g : Graph n) (a : Fin n) : Nat :=
  (List.finRange n).countP (fun b => decide (Reach g a b))

/-- Reachability shrinks (weakly) the reachable-set size: if `a` reaches `b`, every node `b`
    reaches `a` reaches too, so `level b ≤ level a`. -/
theorem reach_level_le {g : Graph n} {a b : Fin n} (h : Reach g a b) :
    level g b ≤ level g a := by
  apply countP_mono
  intro c _ hc
  have hbc : Reach g b c := by simpa using hc
  simp [Reach.trans h hbc]

/- ── The criterion is correct (both directions). ── -/

/-- SOUNDNESS: if the graph has no negative edge on a cycle, a stratification exists. Witness:
    `level`. A positive edge weakly drops the level (reachability); a negative edge `src → tgt`
    drops it STRICTLY because (no neg cycle ⇒) `tgt` cannot reach `src`, so `src` is in `src`'s
    reachable-set but not `tgt`'s. -/
theorem noNegCycle_imp_stratifiable {g : Graph n} (h : NoNegCycle g) : Stratifiable g := by
  refine ⟨level g, ?_⟩
  intro e he
  have hedge : HasEdge g e.src e.tgt := ⟨e, he, rfl, rfl⟩
  have hreach : Reach g e.src e.tgt := Reach.of_edge hedge
  by_cases hneg : e.neg
  · simp only [hneg, if_true]
    -- level e.tgt < level e.src
    refine countP_lt ?_ (List.mem_finRange e.src) ?_ ?_
    · intro c _ hc
      have htc : Reach g e.tgt c := by simpa using hc
      simp [Reach.trans hreach htc]
    · -- decide (Reach g e.tgt e.src) = false, since tgt cannot reach src
      have hnr : ¬ Reach g e.tgt e.src := h e he hneg
      simp [hnr]
    · -- decide (Reach g e.src e.src) = true (reflexivity)
      simp [Reach.refl e.src]
  · simp only [hneg, if_false]
    exact reach_level_le hreach

/-- A level function is (weakly) non-increasing along any reachability path. -/
theorem stratifiable_level_mono {g : Graph n} {lvl : Fin n → Nat}
    (hstrat : ∀ e ∈ g, if e.neg then lvl e.src > lvl e.tgt else lvl e.src ≥ lvl e.tgt)
    {a b : Fin n} (h : Reach g a b) : lvl a ≥ lvl b := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hedge ih =>
    obtain ⟨ed, hmem, hsrc, htgt⟩ := hedge
    have hc := hstrat ed hmem
    have hbc : lvl ed.src ≥ lvl ed.tgt := by
      by_cases hneg : ed.neg
      · simp only [hneg, if_true] at hc; omega
      · simp only [hneg, if_false] at hc; exact hc
    rw [hsrc, htgt] at hbc
    omega

/-- COMPLETENESS: a stratifiable program has no negative edge on a cycle. -/
theorem stratifiable_imp_noNegCycle {g : Graph n} (h : Stratifiable g) : NoNegCycle g := by
  rcases h with ⟨lvl, hstrat⟩
  intro e he hneg hcycle
  have hgt := hstrat e he
  simp only [hneg, if_true] at hgt
  have hle := stratifiable_level_mono hstrat hcycle
  omega

/-- The criterion decides stratifiability exactly. -/
theorem criterion_iff {g : Graph n} : NoNegCycle g ↔ Stratifiable g :=
  ⟨noNegCycle_imp_stratifiable, stratifiable_imp_noNegCycle⟩

/-- The check's REJECT condition holds iff the program is genuinely unstratifiable. -/
theorem rejects_iff_unstratifiable {g : Graph n} :
    RejectsByCriterion g ↔ ¬ Stratifiable g := by
  constructor
  · rintro ⟨e, he, hneg, hcycle⟩ hstrat
    exact stratifiable_imp_noNegCycle hstrat e he hneg hcycle
  · intro h
    apply Classical.byContradiction
    intro hno
    apply h
    apply noNegCycle_imp_stratifiable
    intro e he hneg hcycle
    exact hno ⟨e, he, hneg, hcycle⟩

end Nibli.Strat
