# TODO

Plain bullets, never numbered — work the FIRST remaining bullet; cross-reference items by
name. Delete a bullet entirely when it fully lands; update it if only partially done.
(The first three items came out of the 2026-07-05 Lojban Discord #proga thread with korvo —
brismu/zaha/zatske — and feklat; the int19h items from his 2026-07-10 nibli-fanva feedback.)

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

- **gasnu: split bare-`.i` sentences into independent facts (DEFERRED)** — a bare-`.i`
  multi-sentence line now becomes N independent facts (one per root, connectives kept whole)
  via `LogicBuffer::split_roots` in nibli-ui, nibli-engine, and nibli-wasm, but the gasnu REPL
  still asserts such a line as ONE fact. Deferring on purpose: matching gasnu needs a permanent
  WIT-boundary change (`assert-text -> list<fact-id>` + an `assert-text-root-with-id` replay
  func) AND a durable-store schema addition (`StoredAssertion::TextRoot { text, root }`), all to
  survive per-sentence retraction across a REPL restart — a niche workflow that no shipped
  corpus even exercises (gdpr/ddi have zero medial `.i`). No clean half-measure exists (live-only
  splitting silently loses per-sentence retraction on reopen). The principled fix, if it ever
  becomes real, is to realign gasnu persistence to store the FACT (buffer) rather than the source
  TEXT — then splitting falls out for free and it also removes the recompile-on-replay provenance
  hazard. Full, source-verified steps are in the plan file
  (`~/.claude/plans/i-need-to-make-wild-goblet.md`, "Phase 5").

- **nibli-fanva: semantic verification turn (int19h feedback)** — pass/fail gating is
  insufficient: models emit syntactically valid Lojban with wrong semantics (anaphora
  resolution, bridi place overflow, attitudinals-as-commands — `ei` used for "you must").
  After the gates pass, feed the `nibli_render` back-translation (plus place-structure /
  arity info smuni already knows) back to the model as a verification turn — "here is what
  your Lojban actually claims; does it match the source? revise if not" — ideally as a
  FRESH-context validator call (a `Chat` with no history) so the model cannot green-light
  its own past output. Add int19h's Genesis 1:1–8 pair (Gemini's garbage-that-parses vs his
  reference translation, in the 2026-07-10 Discord feedback / memory) as a
  silent-mistranslation eval fixture. Directly feeds the roadmap's non-Lojbanist
  authoring-study frontier (round-trip fidelity + silent-mistranslation rate).

- **fanva-proxy: retire once jbotci CORS lands** — int19h is enabling direct browser→jbotci
  MCP calls on his end ("no reason it shouldn't be allowed from the browser"). When live:
  verify `initialize` + `tools/list` + `tersmu` from nibli-ui WITHOUT the proxy, then default
  the proxy URL to the direct endpoint and deprecate the Cloudflare Worker (keep the
  local-gates degradation path). Longer-term option he offered: jbotci is Rust→WASM and runs
  fully in-browser (jbotci.app; unpublished crate, referenceable from
  github.com/int19h/jbotci) — but swapping the camxes gate for jbotci's parser would desync
  the browser gate from verify-parser's ilmentufa reference (~500/22k intentional
  divergences: SA erasure, ZOI preprocessing), so embedding is dictionary/tersmu-only if ever.

- **verify-parser: GIhA in the random generators + solid `.ije` lexing** — `gi'e`/`gi'a`/
  `gi'o`/`gi'u` now parse (curated seam cases pin the desugar, and a curated GIhA list rides
  the parser-differential gate) but the seeded random case generators never emit bridi-tails,
  so the camxes differential doesn't fuzz them; add a GIhA production. Separately, the solid
  spelling `.ije` does not lex (only `.i je` parses) — corpus text from Lojbanists will use
  the solid form; teach the lexer/preprocessor the `.i`+JA compounds.

- **GIhA quantified/description heads: share the head witness across tails** — currently
  rejected fail-closed (gerna `giha_safe_head`): the repeated-head desugar would re-quantify
  a `da`/`lo`-head per tail, splitting one surface scope into independent ∃s (wrong TRUE on
  disjoint witnesses — adversarial-review finding, 2026-07-10). The real fix is compiling the
  head ONCE (one witness/variable) and distributing only the tails — needs a smuni-level GIhA
  construct instead of the parse-time desugar. Would un-block int19h's Genesis 1:2
  (`lo terdi cu na se tarmi gi'e kunti`), which today needs a name head or `.i je` restate.

- **logji: upgrade the reversed material-conditional arm (`Or(Q, Not P)`)** — a `na` on the
  RIGHT operand of an asserted disjunction (`mi klama .i ja mi na citka`, `… gi'a na citka`)
  registers a conditional whose condition templates carry the assertion's own event-Skolem
  CONSTANTS, so it can never unify with a later assertion's fresh event Skolem — the rule is
  inert (modus ponens never fires; completeness-only, never unsound). The forward arm
  (Not-on-left) was upgraded to `compile_forall_to_rule` (ev__ pattern vars) precisely for
  this; mirror it in the reversed arm (`register_ground_material_conditional`, kb.rs) and add
  the `Q→P + Q ⊢ P` engine test the adversarial review used to confirm the gap.

- **Determinism corpus: add GIhA + negative-conjunct lines** — `determinism-corpus.lojban`
  predates both; add a `gi'e` chain, a `gi'enai` line, and a `P .i je na Q` +
  contradiction-check sequence so all three runtime surfaces pin the new shapes (requires
  re-pinning the corpus verdicts on native + Wasmtime + node).
