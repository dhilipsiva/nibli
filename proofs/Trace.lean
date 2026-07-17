/-
  Mechanized proof of nibli's HEADLINE SOUNDNESS THEOREM (Track B, phase 6 — the capstone):
  a recorded proof trace ⇒ the conclusion holds in the stratified/perfect model.

  This closes Track B. The five earlier proofs verified individual layers (the four-valued combiner,
  the stratification criterion, the SCC decomposition, the unifier, and rule firing). This file ties
  them together at the top: a recorded proof trace, read as a PROOF CERTIFICATE, is sound w.r.t. the
  perfect model — if the engine records a TRUE derivation the conclusion holds, and if it records a
  closed-world FALSE the conclusion does NOT hold (no fabrication).

  Design (mathlib-free, self-contained):

  * The trace deals in GROUND atoms (unify already happened — a `Derived{fact}` step carries the
    already-instantiated conclusion), so this file works over an abstract `Atom : Type` and models a
    fired rule as a ground `Firing` (head + positive premises + NAF-negative premises). Firing
    soundness is NOT re-derived; it enters as the `ruleClosed` axiom, which is exactly
    `RuleFiring.firing_sound`'s conclusion at the ground instance.

  * A `PerfectModel` bundles the model `M`, the facts `KB`, the (finite) candidate rules per atom,
    and four axioms characterizing the perfect model of a stratified program: `factAx` (facts hold),
    `ruleClosed` (= `firing_sound`), `candOk` (a candidate for `a` concludes `a`), and `supported`
    (every true atom is a fact or the head of a fireable candidate — least-model minimality). These
    are HYPOTHESES here (the model is characterized, not constructed as a fixpoint) — but each is
    BRIDGED to the real engine by the `trace_soundness_conformance` validator, so the theorem is
    load-bearing rather than proof-conditional: `factAx` ↔ every `Asserted` leaf is a stored KB fact;
    `candOk`/`ruleClosed` ↔ every `Derived` step maps to a registered rule (and `firing_sound` is
    itself proved + separately bridged by `rule_firing_conformance`); `supported` ↔ every closed-world
    FALSE (`PredicateNotFound`) records a genuine non-fact whose blocked candidates are all real rules
    (the `notFound`/`Neg` certificate the engine emits). `supported`'s well-definedness is further
    justified by `Stratification.lean` (a stratified program has a unique, minimal perfect model).

  * Certificates are DEPTH-INDEXED (`Pos`/`Neg : Nat → Atom → Prop`, mutual `def` on a fuel `Nat`) —
    a mutual `inductive` would be rejected by the positivity checker (the negative certificate's
    "every candidate is blocked" premise is non-strictly-positive). Depth-indexing is honest: the
    engine's backward chaining is depth-bounded, so a depth-`d` trace yields a depth-`d` certificate,
    and `∃ d, …` recovers the un-indexed statement. The negative certificate ranges over the FINITE
    candidate list, so it is constructible from a real (finite) trace.

  Bridged to the real recorded traces by the `trace_soundness_conformance` validator in
  `nibli-reason/src/tests.rs` (every recorded trace is a valid certificate ⇒, with this theorem, its
  conclusion holds in the model). Checked by `lean proofs/Trace.lean` (`just verify-proofs`). No
  mathlib — prelude only.
-/

set_option linter.unusedSimpArgs false

namespace Nibli.Trace

variable {Atom : Type}

/-- A ground rule instance as recorded when a rule fires: the concluded atom, the positive premises,
    and the NAF-negative premises. (Unify has already run; these are ground.) -/
structure Firing (Atom : Type) where
  concl : Atom
  pos : List Atom
  neg : List Atom

/-- The perfect model of a stratified program, characterized by four axioms. `M` = the true ground
    atoms; `KB` = the asserted facts; `candidates a` = the finite registered rules that can conclude
    `a`. -/
structure PerfectModel (Atom : Type) where
  M : Atom → Prop
  KB : Atom → Prop
  candidates : Atom → List (Firing Atom)
  /-- Asserted facts hold. -/
  factAx : ∀ a, KB a → M a
  /-- A fired candidate whose positive premises hold and whose negative premises fail concludes into
      the model. This IS `RuleFiring.firing_sound` at the ground instance. -/
  ruleClosed :
    ∀ a f, f ∈ candidates a → (∀ p ∈ f.pos, M p) → (∀ n ∈ f.neg, ¬ M n) → M a
  /-- A candidate for `a` really concludes `a`. -/
  candOk : ∀ a f, f ∈ candidates a → f.concl = a
  /-- Least-model minimality: every true atom is a fact or the head of a fireable candidate. Justified
      by `Stratification.lean` (a stratified program has a unique, supported perfect model); assumed,
      not reconstructed. -/
  supported :
    ∀ a, M a → KB a ∨ ∃ f ∈ candidates a, (∀ p ∈ f.pos, M p) ∧ (∀ n ∈ f.neg, ¬ M n)

/- A POSITIVE certificate at fuel `d` (`Pos`): `a` is a fact, or a candidate rule fires with its
   positive premises positively certified and its negative premises refuted.
   A NEGATIVE (closed-world) certificate (`Neg`): `a` is not a fact, and EVERY candidate rule for `a`
   is blocked (a positive premise is refuted, or a negative premise is positively certified). -/
mutual
def Pos (P : PerfectModel Atom) : Nat → Atom → Prop
  | 0, a => P.KB a
  | d + 1, a =>
    P.KB a ∨ ∃ f ∈ P.candidates a, (∀ p ∈ f.pos, Pos P d p) ∧ (∀ n ∈ f.neg, Neg P d n)
def Neg (P : PerfectModel Atom) : Nat → Atom → Prop
  | 0, a => ¬ P.KB a ∧ P.candidates a = []
  | d + 1, a =>
    ¬ P.KB a ∧ ∀ f ∈ P.candidates a, (∃ p ∈ f.pos, Neg P d p) ∨ (∃ n ∈ f.neg, Pos P d n)
end

/-- HEADLINE: at every fuel `d`, a positive certificate is sound (`Pos → M`) and a negative
    certificate is sound (`Neg → ¬ M`). By induction on the fuel: `Pos.fire` composes `ruleClosed`
    (= `firing_sound`) with the IH; `Neg` uses `supported` + the finite-candidate blocking premise +
    the mutual IH to reach a contradiction. -/
theorem cert_sound (P : PerfectModel Atom) :
    ∀ d, (∀ a, Pos P d a → P.M a) ∧ (∀ a, Neg P d a → ¬ P.M a) := by
  intro d
  induction d with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro a h
      simp only [Pos] at h
      exact P.factAx a h
    · intro a h hM
      simp only [Neg] at h
      obtain ⟨hnk, hcand⟩ := h
      rcases P.supported a hM with hk | ⟨f, hf, _⟩
      · exact hnk hk
      · rw [hcand] at hf; simp at hf
  | succ d ih =>
    obtain ⟨ihpos, ihneg⟩ := ih
    refine ⟨?_, ?_⟩
    · intro a h
      simp only [Pos] at h
      rcases h with hk | ⟨f, hf, hpos, hneg⟩
      · exact P.factAx a hk
      · have hposM : ∀ p ∈ f.pos, P.M p := fun p hp => ihpos p (hpos p hp)
        have hnegM : ∀ n ∈ f.neg, ¬ P.M n := fun n hn => ihneg n (hneg n hn)
        exact P.ruleClosed a f hf hposM hnegM
    · intro a h hM
      simp only [Neg] at h
      obtain ⟨hnk, hblock⟩ := h
      rcases P.supported a hM with hk | ⟨f, hf, hposM, hnegM⟩
      · exact hnk hk
      · rcases hblock f hf with ⟨p, hp, hpNeg⟩ | ⟨n, hn, hnPos⟩
        · exact ihneg p hpNeg (hposM p hp)
        · exact hnegM n hn (ihpos n hnPos)

/-- A positive certificate at SOME fuel witnesses model membership. -/
theorem pos_sound (P : PerfectModel Atom) (a : Atom) (h : ∃ d, Pos P d a) : P.M a := by
  obtain ⟨d, hd⟩ := h
  exact (cert_sound P d).1 a hd

/-- A negative (closed-world) certificate at SOME fuel witnesses non-membership — the no-fabrication
    guarantee: the engine never records a closed-world FALSE for an atom that is in the model. -/
theorem neg_sound (P : PerfectModel Atom) (a : Atom) (h : ∃ d, Neg P d a) : ¬ P.M a := by
  obtain ⟨d, hd⟩ := h
  exact (cert_sound P d).2 a hd

/- ── Query layer: compound propositions (mirrors the connectives of `Combiner.lean`) ─────── -/

/-- A query proposition over atoms. -/
inductive QProp (Atom : Type) where
  | atom : Atom → QProp Atom
  | and : QProp Atom → QProp Atom → QProp Atom
  | or : QProp Atom → QProp Atom → QProp Atom
  | not : QProp Atom → QProp Atom

/-- The truth of a query proposition in the model. -/
def qHolds (P : PerfectModel Atom) : QProp Atom → Prop
  | .atom a => P.M a
  | .and l r => qHolds P l ∧ qHolds P r
  | .or l r => qHolds P l ∨ qHolds P r
  | .not q => ¬ qHolds P q

/- A proof that a query is TRUE (`QProof`, built from positive atom certificates); dually `QRefute`
   proves a query FALSE (from negative atom certificates). -/
mutual
def QProof (P : PerfectModel Atom) : QProp Atom → Prop
  | .atom a => ∃ d, Pos P d a
  | .and l r => QProof P l ∧ QProof P r
  | .or l r => QProof P l ∨ QProof P r
  | .not q => QRefute P q
def QRefute (P : PerfectModel Atom) : QProp Atom → Prop
  | .atom a => ∃ d, Neg P d a
  | .and l r => QRefute P l ∨ QRefute P r
  | .or l r => QRefute P l ∧ QRefute P r
  | .not q => QProof P q
end

/-- CAPSTONE: a recorded proof of a (compound) query is sound, and a recorded refutation is sound —
    the full "a recorded trace ⇒ the query's verdict holds in the perfect model," composing the atom
    certificates (`pos_sound`/`neg_sound`) through the connective algebra. -/
theorem qproof_sound (P : PerfectModel Atom) :
    ∀ q, (QProof P q → qHolds P q) ∧ (QRefute P q → ¬ qHolds P q) := by
  intro q
  induction q with
  | atom a =>
    refine ⟨?_, ?_⟩
    · intro h; simp only [QProof] at h; simp only [qHolds]; exact pos_sound P a h
    · intro h; simp only [QRefute] at h; simp only [qHolds]; exact neg_sound P a h
  | and l r ihl ihr =>
    obtain ⟨ihlp, ihln⟩ := ihl
    obtain ⟨ihrp, ihrn⟩ := ihr
    refine ⟨?_, ?_⟩
    · intro h
      simp only [QProof] at h
      obtain ⟨hl, hr⟩ := h
      simp only [qHolds]
      exact ⟨ihlp hl, ihrp hr⟩
    · intro h hqh
      simp only [QRefute] at h
      simp only [qHolds] at hqh
      obtain ⟨hql, hqr⟩ := hqh
      rcases h with hl | hr
      · exact ihln hl hql
      · exact ihrn hr hqr
  | or l r ihl ihr =>
    obtain ⟨ihlp, ihln⟩ := ihl
    obtain ⟨ihrp, ihrn⟩ := ihr
    refine ⟨?_, ?_⟩
    · intro h
      simp only [QProof] at h
      simp only [qHolds]
      rcases h with hl | hr
      · exact Or.inl (ihlp hl)
      · exact Or.inr (ihrp hr)
    · intro h hqh
      simp only [QRefute] at h
      simp only [qHolds] at hqh
      obtain ⟨hl, hr⟩ := h
      rcases hqh with hql | hqr
      · exact ihln hl hql
      · exact ihrn hr hqr
  | not q ih =>
    obtain ⟨ihp, ihn⟩ := ih
    refine ⟨?_, ?_⟩
    · intro h
      simp only [QProof] at h
      simp only [qHolds]
      exact ihn h
    · intro h hqh
      simp only [QRefute] at h
      simp only [qHolds] at hqh
      exact hqh (ihp h)

end Nibli.Trace
