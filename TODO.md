# TODO

Plain bullets, never numbered — work the FIRST remaining bullet; cross-reference items by
name. Delete a bullet entirely when it fully lands; update it if only partially done.
(All three items came out of the 2026-07-05 Lojban Discord #proga thread with korvo —
brismu/zaha/zatske — and feklat.)

- **Predilex cross-validation for smuni-dictionary** — feklat pointed at Predilex
  (https://github.com/Ntsekees/Predilex — public-domain CSV thesaurus of language-neutral
  sememes-as-predicates with per-language lemma mappings). Ntsekees confirmed in-thread
  (2026-07-05): arity is a data field; per-language mapping files carry each lemma's
  argument-structure traits plus a slot-reorder string (e.g. English `give V·DO·to 132`:
  "X gives Y to Z" maps to `jubaku X Z Y`); 200+ entries also have formal logic
  definitions. Open question (asked in-thread): whether a LOJBAN mapping file exists —
  the jubaku entry shows Loglan/Eberban lemmas but no Lojban. If yes: add an offline
  validation pass cross-checking smuni-dictionary's extracted arities + place frames
  against it and reporting divergences (catches lensisku prose-extraction errors — the
  `$x_{N}$`-marker scrape in `smuni-dictionary/src/arity.rs` is best-effort on the
  non-curated long tail, and feklat confirmed jbovlaste conventions are inconsistently
  followed). If no: generate a candidate Lojban→Predilex mapping from lensisku + the
  curated arity table and contribute it upstream, then validate against it.

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

- **Document the LogicBuffer IR as a consumable format** — two independent parties
  converged on wanting a shared logic representation: korvo from the ontology side, feklat
  from the multi-loglang / LLM-verification side (feklat also asked about Toaq / Xextan /
  Eberban front-ends — the answer given: only the parser + dictionary are Lojban-specific;
  the IR, prover, oracle gates, and Lean proofs are language-agnostic, so the IR is the
  seam). Write a short spec: node types, flat-buffer layout, what is stable vs internal,
  and the existing external entry points (`nibli-wasm` assert/query as the "does this
  Lojban entail that claim" API). Non-goal for now: actually building non-Lojban
  front-ends.
