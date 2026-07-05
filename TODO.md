# TODO

Plain bullets, never numbered — work the FIRST remaining bullet; cross-reference items by
name. Delete a bullet entirely when it fully lands; update it if only partially done.
(All three items came out of the 2026-07-05 Lojban Discord #proga thread with korvo —
brismu/zaha/zatske — and feklat.)

- **Predilex cross-validation for smuni-dictionary** — Predilex
  (https://github.com/Ntsekees/Predilex — public-domain CSV thesaurus of language-neutral
  sememes-as-predicates with per-language lemma mappings). A Lojban mapping file EXISTS:
  `conlangs/Lojban.csv`, 459 entries (gismu + lujvo + cmavo), each row carrying a Supertype
  (VT/VI/VD/…), an optional Features arity, and a Sememe cell with an optional slot-reorder
  string (e.g. `behucu 132` — Lojban→sememe place permutation, same atomic move as korvo's
  ontology rows). Spike already run (scratchpad `predilex_arity_check.py`): on the 46 rows
  with a high-confidence arity signal that are also in the lensisku gismu/lujvo set, 37
  agree / 9 disagree — all 9 are Predilex modeling a coarser place-deleted sememe
  (legitimate, not a nibli error). (Was 36/10 before the lujvo component-letter arity fix
  landed in `arity.rs`; the sole remaining undercount then, `flubisli`, is now correct.)
  TODO: wire this into a repeatable offline validation pass (own bin or a `nibli-verify`
  leg) that reports divergences and skips known place-deletion cases.
  200+ Predilex entries also carry formal logic definitions — a possible second oracle later.

- **Ontology-row import (brismu/zatske interchange)** — korvo proposed flat rows
  `[P, Q, mapping]` (selbri subrelation with terbri mapping: identity `["gerku","danlu",
  [1,2]]`; place deletion `["skari","ckaji",[1,2]]` — unmapped source places dropped;
  permutation `["lanzu","cmima",[2,1]]`) as the interchange format between brismu / zaha /
  zatske and downstream consumers; agreed in-thread, korvo confirmed rows are "a good
  compromise". Build an importer beside `nibli-import/src/rdf.rs`/`owl.rs`: each row
  compiles to one monotone Horn rule at the IR level (event decomposition — mapping is a
  role renaming, deletion = roles absent from the head), arity/place validation against
  smuni-dictionary (strict-mode rejection semantics), per-row source/provenance field
  surfaced in proof traces, curated Vampire differential cases for the three row shapes,
  plus mutual-row (equivalence) cases like dugri/tenfa — positive cycles legal, fuel-bounded.
  BLOCKED on korvo pinning the row schema + publishing a baseline export. Spec feedback
  already sent in-thread: the mapping-list direction is ambiguous (a 3-cycle case like
  dugri/tenfa pins it — the [2,1] swap and [1,2] identity examples can't distinguish the
  two readings), and rows want a source field (brismu / zaha / zatske) for provenance.

- **Document the LogicBuffer IR as a consumable format** — three independent parties
  converged on wanting a shared logic representation: korvo from the ontology side, feklat
  from the multi-loglang / LLM-verification side, and Ntsekees, who described the same idea
  unprompted as "Predilog" — a customized logic notation (e.g. `∀c.[Cat(c) ⇒ ∃l. Leg(l,c) ∧
  Four(l)]`) intended as a JSON translation-pivot between languages, and asked whether nibli
  already had one (it does: the IR). (feklat also asked about Toaq / Xextan / Eberban
  front-ends — the answer given: only the parser + dictionary are Lojban-specific; the IR,
  prover, oracle gates, and Lean proofs are language-agnostic, so the IR is the seam.) Write
  a short spec: node types, flat-buffer layout, what is stable vs internal, and the existing
  external entry points (`nibli-wasm` assert/query as the "does this Lojban entail that
  claim" API). Non-goal for now: actually building non-Lojban front-ends.
