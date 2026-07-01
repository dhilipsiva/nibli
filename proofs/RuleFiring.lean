/-
  Mechanized proof of nibli's RULE FIRING (Track B, phase 5).

  Backward chaining derives a goal by FIRING a universal rule (`logji/src/reasoning.rs`
  `process_phase` / `emit_derived`, `UniversalRuleRecord` at `kb.rs:474`): it unifies a rule's
  conclusion template against the goal (producing σ), discharges each condition under σ (positive
  conditions must hold; `negated_condition_indices` must FAIL, by negation-as-failure), and
  concludes the σ-instantiated head. This file proves one firing step is a sound
  universal-instantiation + modus-ponens step — it never fabricates.

  The load-bearing composition is `unify_sound` (proved at the term level in `Unify.lean`): a
  successful head match instantiates the conclusion template to EXACTLY the goal. Here it is lifted
  to atoms (relation + argument list) via `unifyArgs_sound` — the arg-wise fold that mirrors the
  argument loop in the real `unify_facts` (`kb.rs:315`) — and then to the firing step
  (`firing_sound`): if the rule holds in the model M (the perfect/least model is closed under every
  registered rule; the NAF conditions are well-defined because the program is stratified — proved
  in `Stratification.lean` + `Scc.lean`), the head matches the goal via σ, and σ discharges the
  conditions, then the goal is in M. The contrapositive (`firing_no_fabrication`) is the
  no-fabrication guarantee.

  Bridged to the real engine by the `rule_firing_conformance` test in `logji/src/tests.rs`. Checked
  by `lean proofs/RuleFiring.lean` (`just verify-proofs`). No mathlib — prelude only. Self-contained:
  the term-level unifier (`GTerm`/`subst`/`unify`/`unify_sound` + its two lemmas) is duplicated from
  `Unify.lean` (each proof file stands alone).
-/

set_option linter.unusedSimpArgs false

namespace Nibli.RuleFiring

/- ── Term-level unifier, duplicated verbatim from `Unify.lean` (self-contained) ───────────── -/

/-- A ground term, mirroring `logji`'s `GroundTerm` (`logji/src/kb.rs:130`). -/
inductive GTerm where
  | const : String → GTerm
  | num : Nat → GTerm
  | descr : String → GTerm
  | unspec : GTerm
  | skolem : String → GTerm → GTerm
  | depPair : GTerm → GTerm → GTerm
  | pvar : String → GTerm
deriving DecidableEq, Repr

abbrev Subst := List (String × GTerm)

def lookup : Subst → String → Option GTerm
  | [], _ => none
  | (k, v) :: rest, name => if k = name then some v else lookup rest name

def NoVar : GTerm → Prop
  | .const _ => True
  | .num _ => True
  | .descr _ => True
  | .unspec => True
  | .pvar _ => False
  | .skolem _ d => NoVar d
  | .depPair a b => NoVar a ∧ NoVar b

def subst (σ : Subst) : GTerm → GTerm
  | .const a => .const a
  | .num a => .num a
  | .descr a => .descr a
  | .unspec => .unspec
  | .pvar name => match lookup σ name with
    | some t => t
    | none => .pvar name
  | .skolem n d => .skolem n (subst σ d)
  | .depPair a b => .depPair (subst σ a) (subst σ b)

def unify : GTerm → GTerm → Subst → Option Subst
  | .pvar name, c, σ =>
    match lookup σ name with
    | some t' => if t' = c then some σ else none
    | none => some ((name, c) :: σ)
  | .const a, c, σ => match c with
    | .const b => if a = b then some σ else none
    | _ => none
  | .num a, c, σ => match c with
    | .num b => if a = b then some σ else none
    | _ => none
  | .descr a, c, σ => match c with
    | .descr b => if a = b then some σ else none
    | _ => none
  | .unspec, c, σ => match c with
    | .unspec => some σ
    | _ => none
  | .skolem na da, c, σ => match c with
    | .skolem nb db => if na = nb then unify da db σ else none
    | _ => none
  | .depPair a1 a2, c, σ => match c with
    | .depPair b1 b2 => match unify a1 b1 σ with
      | some σ' => unify a2 b2 σ'
      | none => none
    | _ => none

theorem lookup_cons_self (name : String) (c : GTerm) (σ : Subst) :
    lookup ((name, c) :: σ) name = some c := by
  simp [lookup]

theorem unify_extends (t : GTerm) :
    ∀ (c : GTerm) (σ σ' : Subst),
      unify t c σ = some σ' → ∀ k v, lookup σ k = some v → lookup σ' k = some v := by
  induction t with
  | const a =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact hkv
    · contradiction
  | num a =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact hkv
    · contradiction
  | descr a =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact hkv
    · contradiction
  | unspec =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    injection h with h; subst h; exact hkv
  | pvar name =>
    intro c σ σ' h k v hkv
    cases hl : lookup σ name with
    | some t' =>
      simp only [unify, hl] at h
      by_cases hc : t' = c
      · rw [if_pos hc] at h; injection h with h; subst h; exact hkv
      · rw [if_neg hc] at h; contradiction
    | none =>
      simp only [unify, hl] at h; injection h with h; subst h
      by_cases hk : name = k
      · rw [← hk] at hkv; rw [hl] at hkv; contradiction
      · simp only [lookup, if_neg hk]; exact hkv
  | skolem na da ih =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i nb db
    by_cases hn : na = nb
    · rw [if_pos hn] at h; exact ih db σ σ' h k v hkv
    · rw [if_neg hn] at h; contradiction
  | depPair a1 a2 ih1 ih2 =>
    intro c σ σ' h k v hkv
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i b1 b2
    cases hh : unify a1 b1 σ with
    | none => rw [hh] at h; contradiction
    | some σ1 =>
      rw [hh] at h
      have h1 := ih1 b1 σ σ1 hh k v hkv
      exact ih2 b2 σ1 σ' h k v h1

theorem subst_stable (t : GTerm) :
    ∀ (σ σ' : Subst),
      (∀ k v, lookup σ k = some v → lookup σ' k = some v) →
      NoVar (subst σ t) → subst σ' t = subst σ t := by
  induction t with
  | const a => intro _ _ _ _; rfl
  | num a => intro _ _ _ _; rfl
  | descr a => intro _ _ _ _; rfl
  | unspec => intro _ _ _ _; rfl
  | pvar name =>
    intro σ σ' hext hg
    cases hl : lookup σ name with
    | none => simp only [subst, hl, NoVar] at hg
    | some w =>
      have hl' : lookup σ' name = some w := hext name w hl
      simp only [subst, hl, hl']
  | skolem n d ih =>
    intro σ σ' hext hg
    simp only [subst] at hg ⊢
    rw [ih σ σ' hext hg]
  | depPair a b iha ihb =>
    intro σ σ' hext hg
    simp only [subst] at hg ⊢
    obtain ⟨hga, hgb⟩ := hg
    rw [iha σ σ' hext hga, ihb σ σ' hext hgb]

theorem unify_sound (t : GTerm) :
    ∀ (c : GTerm) (σ σ' : Subst),
      NoVar c → unify t c σ = some σ' → subst σ' t = c := by
  induction t with
  | const a =>
    intro c σ σ' _ h
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · next hab => injection h with h; subst h; simp only [subst]; rw [hab]
    · contradiction
  | num a =>
    intro c σ σ' _ h
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · next hab => injection h with h; subst h; simp only [subst]; rw [hab]
    · contradiction
  | descr a =>
    intro c σ σ' _ h
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · next hab => injection h with h; subst h; simp only [subst]; rw [hab]
    · contradiction
  | unspec =>
    intro c σ σ' _ h
    cases c <;> simp only [unify] at h <;> try contradiction
    injection h with h; subst h; rfl
  | pvar name =>
    intro c σ σ' _ h
    cases hl : lookup σ name with
    | some t' =>
      simp only [unify, hl] at h
      by_cases hc : t' = c
      · rw [if_pos hc] at h; injection h with h; subst h
        simp only [subst, hl]; exact hc
      · rw [if_neg hc] at h; contradiction
    | none =>
      simp only [unify, hl] at h; injection h with h; subst h
      simp only [subst, lookup_cons_self]
  | skolem na da ih =>
    intro c σ σ' hc h
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i nb db
    by_cases hn : na = nb
    · rw [if_pos hn] at h
      have hcd : NoVar db := hc
      have hrec := ih db σ σ' hcd h
      simp only [subst]; rw [hrec, hn]
    · rw [if_neg hn] at h; contradiction
  | depPair a1 a2 ih1 ih2 =>
    intro c σ σ' hc h
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i b1 b2
    obtain ⟨hb1, hb2⟩ := hc
    cases hh : unify a1 b1 σ with
    | none => rw [hh] at h; contradiction
    | some σ1 =>
      rw [hh] at h
      have e2 := ih2 b2 σ1 σ' hb2 h
      have e1σ1 := ih1 b1 σ σ1 hb1 hh
      have hext := unify_extends a2 b2 σ1 σ' h
      have e1 : subst σ' a1 = subst σ1 a1 :=
        subst_stable a1 σ1 σ' hext (by rw [e1σ1]; exact hb1)
      simp only [subst]; rw [e1, e1σ1, e2]

/- ── Atom-level unifier: the arg-wise fold that mirrors `unify_facts` ─────────────────────── -/

/-- An atom: a relation name and an argument list (mirrors a `GroundFact`). -/
structure Atom where
  rel : String
  args : List GTerm
deriving DecidableEq, Repr

/-- Apply a substitution to an atom (mirrors `substitute_fact`, `kb.rs:364`). -/
def substAtom (σ : Subst) (a : Atom) : Atom :=
  { rel := a.rel, args := a.args.map (subst σ) }

/-- A ground atom (the concrete/goal side is always ground). -/
def AtomNoVar (a : Atom) : Prop := ∀ t ∈ a.args, NoVar t

/-- Unify two argument lists, threading the accumulator (mirrors the `zip` loop in `unify_facts`,
    `kb.rs:315` — same-length lists after the arity check; mismatched lengths fail). -/
def unifyArgs : List GTerm → List GTerm → Subst → Option Subst
  | [], [], σ => some σ
  | t :: ts, c :: cs, σ => match unify t c σ with
    | some σ' => unifyArgs ts cs σ'
    | none => none
  | _, _, _ => none

/-- Unify two atoms: relation names and arities must match, then fold over the arguments. -/
def unifyAtom (t c : Atom) (σ : Subst) : Option Subst :=
  if t.rel = c.rel then unifyArgs t.args c.args σ else none

theorem unifyArgs_extends :
    ∀ (ts cs : List GTerm) (σ σ' : Subst),
      unifyArgs ts cs σ = some σ' → ∀ k v, lookup σ k = some v → lookup σ' k = some v := by
  intro ts
  induction ts with
  | nil =>
    intro cs σ σ' h k v hkv
    cases cs with
    | nil => simp only [unifyArgs] at h; injection h with h; subst h; exact hkv
    | cons c cs' => simp only [unifyArgs] at h; contradiction
  | cons t ts ih =>
    intro cs σ σ' h k v hkv
    cases cs with
    | nil => simp only [unifyArgs] at h; contradiction
    | cons c cs' =>
      simp only [unifyArgs] at h
      cases hh : unify t c σ with
      | none => rw [hh] at h; contradiction
      | some σ1 =>
        rw [hh] at h
        have h1 := unify_extends t c σ σ1 hh k v hkv
        exact ih cs' σ1 σ' h k v h1

theorem unifyArgs_sound :
    ∀ (ts cs : List GTerm) (σ σ' : Subst),
      (∀ c ∈ cs, NoVar c) → unifyArgs ts cs σ = some σ' → ts.map (subst σ') = cs := by
  intro ts
  induction ts with
  | nil =>
    intro cs σ σ' _ h
    cases cs with
    | nil => simp
    | cons c cs' => simp only [unifyArgs] at h; contradiction
  | cons t ts ih =>
    intro cs σ σ' hg h
    cases cs with
    | nil => simp only [unifyArgs] at h; contradiction
    | cons c cs' =>
      simp only [unifyArgs] at h
      cases hh : unify t c σ with
      | none => rw [hh] at h; contradiction
      | some σ1 =>
        rw [hh] at h
        have hc : NoVar c := hg c List.mem_cons_self
        have hcs : ∀ x ∈ cs', NoVar x := fun x hx => hg x (List.mem_cons_of_mem c hx)
        have e_t_σ1 : subst σ1 t = c := unify_sound t c σ σ1 hc hh
        have hext := unifyArgs_extends ts cs' σ1 σ' h
        have e_t : subst σ' t = subst σ1 t :=
          subst_stable t σ1 σ' hext (by rw [e_t_σ1]; exact hc)
        have e_tail := ih cs' σ1 σ' hcs h
        simp only [List.map_cons]
        rw [e_t, e_t_σ1, e_tail]

/-- The atom-level analogue of `unify_sound`: a successful head match instantiates the template
    atom to exactly the (ground) concrete atom. This is what `unify_facts` guarantees. -/
theorem unifyAtom_sound (t c : Atom) (σ σ' : Subst)
    (hg : AtomNoVar c) (h : unifyAtom t c σ = some σ') : substAtom σ' t = c := by
  simp only [unifyAtom] at h
  by_cases hrel : t.rel = c.rel
  · rw [if_pos hrel] at h
    have hargs := unifyArgs_sound t.args c.args σ σ' hg h
    simp only [substAtom]; rw [hrel, hargs]
  · rw [if_neg hrel] at h; contradiction

/- ── Rule firing: one firing step is sound universal instantiation + modus ponens ────────── -/

/-- A universal rule: a conclusion atom and a list of `(isNegated, condition atom)` — mirrors a
    `UniversalRuleRecord`'s `typed_conclusions` (the matched one) + `typed_conditions` with the
    `negated_condition_indices` folded in as the `Bool`. -/
structure Rule where
  concl : Atom
  conds : List (Bool × Atom)

/-- A rule's conditions are DISCHARGED at σ w.r.t. the model M iff each positive condition's
    instance is in M and each negated condition's instance is NOT in M (negation-as-failure). -/
def CondsDischarged (M : Atom → Prop) (σ : Subst) (r : Rule) : Prop :=
  ∀ b a, (b, a) ∈ r.conds → (if b then ¬ M (substAtom σ a) else M (substAtom σ a))

/-- The rule HOLDS in the model M iff, for every substitution, discharging its conditions forces
    its conclusion instance. The perfect/least model is closed under every registered rule, so this
    premise holds by construction; stratification (`Stratification.lean` + `Scc.lean`) is what makes
    the NAF conditions well-defined so that "M" is a unique model. -/
def RuleHolds (M : Atom → Prop) (r : Rule) : Prop :=
  ∀ σ, CondsDischarged M σ r → M (substAtom σ r.concl)

/-- FIRING SOUNDNESS: one firing step is a sound universal-instantiation + modus-ponens step. If
    the rule holds in M, the head unifies with the (ground) goal via σ, and σ discharges the
    conditions, then the goal is in M. Composes `unifyAtom_sound` (hence `unify_sound`): the
    instantiated head IS the goal, so discharging the σ-instance directly yields the goal. -/
theorem firing_sound (M : Atom → Prop) (r : Rule) (goal : Atom) (σ₀ σ : Subst)
    (hrule : RuleHolds M r)
    (hmatch : unifyAtom r.concl goal σ₀ = some σ)
    (hgoal : AtomNoVar goal)
    (hconds : CondsDischarged M σ r) :
    M goal := by
  have hinst : substAtom σ r.concl = goal := unifyAtom_sound r.concl goal σ₀ σ hgoal hmatch
  have hhead := hrule σ hconds
  rw [hinst] at hhead
  exact hhead

/-- NO FABRICATION (the contrapositive): if the goal is NOT in the model, then no firing of a
    model-sound rule whose head matches the goal can succeed — some condition must be undischarged
    (a positive one missing, or a negated one's witness present). Firing never concludes something
    outside the model. -/
theorem firing_no_fabrication (M : Atom → Prop) (r : Rule) (goal : Atom) (σ₀ σ : Subst)
    (hrule : RuleHolds M r)
    (hmatch : unifyAtom r.concl goal σ₀ = some σ)
    (hgoal : AtomNoVar goal)
    (hnot : ¬ M goal) :
    ¬ CondsDischarged M σ r :=
  fun hconds => hnot (firing_sound M r goal σ₀ σ hrule hmatch hgoal hconds)

end Nibli.RuleFiring
