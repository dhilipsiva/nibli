/-
  Mechanized proof of nibli's ONE-DIRECTIONAL UNIFIER (Track B, phase 4).

  Backward chaining matches a rule's conclusion TEMPLATE (which carries pattern variables) against
  a ground goal fact, producing a substitution σ, then instantiates the rule with σ. That match
  must be SOUND: a successful unification instantiates the template to exactly the goal. Nothing
  above the unifier (rule firing, the proof-trace ⇒ model theorem) is sound if this isn't.

  The real code (`logji/src/kb.rs`): `unify_terms(template, concrete, &mut bindings) -> bool`
  (:326) delegated per-argument by `unify_facts` (:290); `substitute_term` (:389) applies a
  substitution. Only the template carries `PatternVar`s — the concrete side is always GROUND (facts
  in the store are ground). This file models the term-level recursion (where all the subtlety
  lives: consistency of repeated variables, and threading the accumulator through `DepPair` /
  `SkolemFn`) and proves:

      unify t c σ₀ = some σ  →  subst σ t = c        (for ground `c`)

  Bridged to the real `unify_facts` / `substitute_fact` by the `unify_conformance` corpus test in
  `logji/src/tests.rs` (the fact-level property is the arg-wise fold of this term-level one).

  Checked by `lean proofs/Unify.lean` (`just verify-proofs`). No mathlib — prelude only.
  Self-contained (each proof file stands alone). The `Number` payload is abstracted to `Nat`: only
  decidable equality matters for match soundness, not f64 bit-semantics.
-/

set_option linter.unusedSimpArgs false

namespace Nibli.Unify

/-- A ground term, mirroring `logji`'s `GroundTerm` (`logji/src/kb.rs:130`). Only `pvar` (a
    template pattern variable) is ever bound; the concrete side is always `NoVar` (ground). -/
inductive GTerm where
  | const : String → GTerm
  | num : Nat → GTerm
  | descr : String → GTerm
  | unspec : GTerm
  | skolem : String → GTerm → GTerm
  | depPair : GTerm → GTerm → GTerm
  | pvar : String → GTerm
deriving DecidableEq, Repr

/-- A substitution: an association list from pattern-variable names to terms. `unify` inserts a key
    only when it is ABSENT, so keys stay unique and `lookup` (first match) is the binding. -/
abbrev Subst := List (String × GTerm)

def lookup : Subst → String → Option GTerm
  | [], _ => none
  | (k, v) :: rest, name => if k = name then some v else lookup rest name

/-- No pattern variable anywhere — the ground-concrete invariant. -/
def NoVar : GTerm → Prop
  | .const _ => True
  | .num _ => True
  | .descr _ => True
  | .unspec => True
  | .pvar _ => False
  | .skolem _ d => NoVar d
  | .depPair a b => NoVar a ∧ NoVar b

/-- Apply a substitution (mirrors `substitute_term`, `logji/src/kb.rs:389`). -/
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

/-- The one-directional unifier (mirrors `unify_terms`, `logji/src/kb.rs:326`): match `t`
    (template, may contain `pvar`s) against `c` (concrete), threading the accumulator `σ`. A bound
    variable must re-match consistently; an unbound one binds; non-variables match structurally. -/
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

/-- `lookup` of an absent key freshly bound: it resolves to the new value. -/
theorem lookup_cons_self (name : String) (c : GTerm) (σ : Subst) :
    lookup ((name, c) :: σ) name = some c := by
  simp [lookup]

/-- EXTENSION MONOTONICITY: a successful `unify` only ADDS bindings — every prior binding is
    preserved. This lets the second component of a `depPair` be unified without disturbing the
    first component's bindings. -/
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

/-- SUBST STABILITY: if `subst σ t` is fully ground, extending `σ` to `σ'` does not change the
    result — every variable of `t` is already resolved by `σ`. -/
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

/-- SOUNDNESS: a successful one-directional unification instantiates the template to exactly the
    (ground) concrete term. The property the Rust `unify_conformance` test checks on the real
    `unify_facts` / `substitute_fact`. -/
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

/-- Whether a pattern variable `name` occurs in a term. -/
def occurs (name : String) : GTerm → Prop
  | .pvar m => m = name
  | .skolem _ d => occurs name d
  | .depPair a b => occurs name a ∨ occurs name b
  | _ => False

/-- MINIMAL BINDINGS: `unify` never binds a variable absent from the template — any key resolvable
    in the result but not in `σ₀` occurs in `t`. -/
theorem unify_minimal (t : GTerm) :
    ∀ (c : GTerm) (σ σ' : Subst),
      unify t c σ = some σ' →
        ∀ k, (lookup σ' k).isSome → (lookup σ k).isSome ∨ occurs k t := by
  induction t with
  | const a =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact Or.inl hk
    · contradiction
  | num a =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact Or.inl hk
    · contradiction
  | descr a =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    split at h
    · injection h with h; subst h; exact Or.inl hk
    · contradiction
  | unspec =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    injection h with h; subst h; exact Or.inl hk
  | pvar name =>
    intro c σ σ' h k hk
    cases hl : lookup σ name with
    | some t' =>
      simp only [unify, hl] at h
      by_cases hc : t' = c
      · rw [if_pos hc] at h; injection h with h; subst h; exact Or.inl hk
      · rw [if_neg hc] at h; contradiction
    | none =>
      simp only [unify, hl] at h; injection h with h; subst h
      by_cases hk2 : name = k
      · exact Or.inr hk2
      · left; simp only [lookup, if_neg hk2] at hk; exact hk
  | skolem na da ih =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i nb db
    by_cases hn : na = nb
    · rw [if_pos hn] at h; exact ih db σ σ' h k hk
    · rw [if_neg hn] at h; contradiction
  | depPair a1 a2 ih1 ih2 =>
    intro c σ σ' h k hk
    cases c <;> simp only [unify] at h <;> try contradiction
    rename_i b1 b2
    cases hh : unify a1 b1 σ with
    | none => rw [hh] at h; contradiction
    | some σ1 =>
      rw [hh] at h
      rcases ih2 b2 σ1 σ' h k hk with hσ1 | hocc2
      · rcases ih1 b1 σ σ1 hh k hσ1 with hσ | hocc1
        · exact Or.inl hσ
        · exact Or.inr (Or.inl hocc1)
      · exact Or.inr (Or.inr hocc2)

end Nibli.Unify
