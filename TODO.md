# Engine TODO

**Future-facing only.** An entry is here because it is still true and still wants doing —
delete it when it lands rather than marking it done, and put the record in the commit.

Every surviving entry was re-verified against HEAD on 2026-08-16 (HEAD `5777ced`) by a
12-way parallel sweep: every cited file opened at the cited line, behavioural claims
checked against current source, and every negative grep positive-controlled. Five commits
landed after the previous 2026-08-08 sweep (`ef669b8`, `1784c67`, `07734c8`, `5580618`,
`5777ced` — the witness-enumeration fail-closed decision and the corpus-scoped
compute-registration decision). They closed NOTHING below, but they moved many lines in
`nibli-reason/src/lib.rs` (+~40..110), `kb.rs` (+~90..290), `reasoning.rs` (~+100 in the
tracer region), and README — citations below were corrected in the same pass — and
5580618's complete-or-error collection contract joined what the book-sync entries must
carry. One sub-claim died and was deleted (`ProofRule::Asserted` DOES carry fact-id
citations since `d421a6d` / WIT 0.10.0), and the mutants figures were refreshed. Still
check a line before trusting it, and correct it in place when you do.

**Ordered by dependency since 2026-08-16.** Four tiers: constraints of record (no open
work), INDEPENDENT entries (no ordering constraints between them — land any time, any
order), dependency CHAINS (numbered; do them in the stated order, the reason is given in
place), and entries blocked on external repos. Effort is NOT the axis — an independent
entry may be week-sized and a chain step an afternoon.

**Effort tags (added 2026-08-16):** every open entry carries *(effort: …)*, sized
against the code by a 10-agent assess-and-calibrate sweep. **low** = under an hour —
one file or recipe, existing coverage. **medium** = a focused session — a few files
plus targeted tests, no open design decisions. **high** = days — cross-crate work,
new batteries/gates, design within established patterns. **extra** = a week-plus — a
new contract/subsystem, a WIT bump threaded through every surface, or Lean
proof-gate work. **max** = a multi-week program — external professional review on
the critical path. **ultracode** = open-ended program-scale work whose scope is only
discoverable by doing it; currently unused — every entry here has a stated
deliverable and bounded scope. Where an entry documents a cheaper exit, that exit's
tier is noted in the same tag. Constraints of record carry no tag (nothing to
implement).

Release runbook: **`RELEASING.md`**. Docs hosting: **`DEPLOY.md`**. Book manuscript:
separate `book/` repo (`book/TODO.md`). The docs + release tracker `DOCS_TODO.md` was
RETIRED 2026-08-03.

---

## Constraints of record — nothing to do; rules a future change must respect

**Authorization (A0–A5 SHIPPED in full):** `nibli-auth` + `nibli-auth-py`, `authorizer`
on `nibli:engine@0.6.0` (package now @0.11.0 — `wit/world.wit`:14; the export survives at
:531/:580), `policy/auth-0.1.0.nibli`, Rust and Python adapters, both examples, the
mdBook chapter, and a dedicated `auth` job in CI (`just test-auth && just
check-auth-axum`). The phase-by-phase record is in git history; these outlive it:

- **Forbidden names for auth heads:** `can`, `field`, `principal` — all three collide
  with corpus entries (`lante` tin/can, `foldi` agricultural field, `ralju`). The KR
  heads are `authorized(agent, action, resource)` and
  `visible_attr(agent, resource, attr)`; the host-language method names stay
  `can` / `allowed_fields` / `explain`.
- **Do not overload `permits`/`permitted` as HTTP auth.** They are the deontic corpus
  pair and mean something else.
- **UNKNOWN on the hot path DENIES.** Only an engine TRUE allows; proofs stay opt-in
  via `explain`.
- **One warm `Authorizer` per process** — never per-request, and never `reset()`
  between requests (it drops the policy).
- **Still non-goals:** Extism as primary runtime; per-request engine spawn; weakening
  CWA/CDA; inventing vocabulary outside the fail-closed corpus; framework-specific
  policy languages.

(The one open item this section used to carry — Python-bridge CI coverage — LANDED
2026-08-16: the `auth-py` CI job runs `just test-auth-py` through the default Nix
devshell, so both halves of the adapter surface are gated.)

**Pin runner — `:accept-scoped` cannot scope a one-way declaration, by design.**
`derived_only`/`admits` are deliberately absent from `rebuild_inner`'s clear list, so
they survive the replay a retraction performs; the runner refuses to scope them rather
than silently no-op (`nibli/src/bin/pin.rs`:321-332, the refusal at :945-957). If a KB
ever needs a *scoped* vocabulary control, the engine would have to gain an explicit
un-declare — which was rejected once already, because a vocabulary that can be re-opened
at runtime gives back exactly the capability the declaration removes. Revisit only with
a concrete need.

---

## The mutants re-cut

(C3 CLOSED 2026-08-16, in four steps: the semi-naive join indexed on statically
bound positions (`LevelIndex`; transitive closure 1.19 s -> 72 ms at |R|=100);
a refused assertion no longer dropping the saturation (`rollback_inner`;
254 ms -> 7.9 ms); an insert outside the dependency cone no longer dropping it
(`invalidate_materialization_for_insert`; 87.6 ms -> 0.54 ms); and finally the
IN-CONE DELTA RESUME (`resume_with_delta`; 84.3 ms -> 5.5 ms), which folds new
stored tuples into the existing extensions by re-entering the semi-naive
fixpoint from a delta instead of recomputing it. The resume refuses -- falling
back to a full recompute -- on equality classes, any relation read under
NEGATION (growth through a negated condition shrinks the model, so it is not
monotone), a relation that can no longer be seeded, an arity disagreement, or a
budget overflow. In debug builds it verifies itself against a full recompute on
every fold, which makes the whole test suite and the interleaved ON/OFF
differential gates on the incremental path.

One residual, recorded rather than left implicit: a refused assertion still
REPLAYS every surviving record to restore a state it never changed (the 7.9 ms
above). Skipping that replay needs a trustworthy "nothing was mutated" signal,
which the saturation's survival alone does not provide -- insert-only domain
state (`known_entities`/`known_numbers`, the member caches) is mutated by paths
that do not all invalidate, the 2026-08-01 lingering-member class. Either extend
the at-the-mutation-point discipline to one logical-state epoch every mutation
bumps, or leave the replay alone.)

**One more confirming `just mutants` run owed** *(effort: low — one ~4 h run, no triage
expected)*. The baseline was re-cut 2026-08-17 from ONE COMPLETE run (1592 mutants in
4 h: 1104 caught, 49 timeouts, 142 unviable, 297 missed = 241 normalized survivors), and
the recipe's own diff against it is exactly clean — 0 survivors unlisted, 0 stale entries.
Since that run the tree gained ONE test (`the_converted_duty_alias_compiles_and_reasons_in_every_corpus_shape`),
which can only kill more, never fewer. Run it once to confirm and delete this entry.

**Why a full run rather than a stitched one, learned the hard way:** the first attempt at
this re-cut built the baseline from an interrupted sweep UNIONED with a scoped follow-up
that closed its 103-mutant gap. That union recorded 13 mutants as CAUGHT which the
confirming run found MISSED; re-testing them by hand showed they survive at both the pre-
and post-change commits, so the union — not the tree — was wrong. A baseline is a claim
about a whole sweep and has to come from one. **Gotcha for whoever runs it:**
`cargo mutants -f <path>` does NOT scope the sweep when `examine_globs` is set (the config
wins); edit `examine_globs` temporarily instead, and check the "Found N mutants to test"
line before walking away. **Second gotcha:** when reproducing a survivor by hand, match the
COLUMN — several of these functions carry two mutable faces on one line, and mutating the
wrong one proves nothing (it cost two wrong conclusions during this re-cut).

---

## Chain — case-study corpora (1 and 2 independent)

The `obliged`-rendering entry that used to head this chain LANDED 2026-08-17, together
with the corpus migration it turned out to require, so the GDPR redesign below no longer
waits on anything. What was fixed, and what a future change must not undo: the obligated
party is **x1** in every spelling (`obliged`'s corpus places are `[bound, duty, standard]`),
the renderer reads that place rather than compensating for a corpus, and the shipped
corpora now write duties with the PLAIN `obliged` spelling so the party lands where the
places put it. The converted `obligated_by` alias still exists, still inverts, and is
still pinned (`pins/converse-alias.nibli`) — it is simply no longer what the corpora use.

1. **Replace person-level GDPR proxies with operation-scoped legal facts.** *(effort: max)*
  `gdpr.nibli`:46-78 derives a generic `permitted(person)` from
  `approves/promise/obliged` (the three rules at :48/:50/:52) and uses absence of
  `approves` under NAF as the erasure trigger (rationale at :64-78; the erasure rule
  statement itself, `obligated_by(every person where ~approves, event { removes() }).`,
  sits at :101). It does not identify the processing operation, controller, data,
  purpose, consent scope/withdrawal time, alternative lawful bases, Article 17
  exceptions, or jurisdiction/effective text; NAF absence is not a legal finding.
  Design an operation-scoped schema and corpus with legal review, explicit coverage
  assumptions, exceptions, and dated primary sources. **Exit:**
  multi-controller/multi-purpose/withdrawal/alternative-basis/exception
  counterexamples are pinned; missing evidence yields an honest
  non-compliance-neutral result rather than a legal conclusion; engine/UI fixtures and
  Chapter 19 consume the same live artifact.

2. **Redesign `drug-interactions.nibli` around a patient-local exposure event.** *(effort: max)* The
  concentration rules at :71-72 derive drug-level risk from global
  inhibition/metabolism, and the alert rule at :94 checks only that Adam uses the
  risky substrate. Retracting `uses(Adam, Flukonazol)` therefore does not withdraw the
  warfarin alert; a second patient taking warfarin alone can inherit risk from an
  inhibitor nobody in that regimen takes. Model co-administration explicitly and
  decide/document the dosage, route, timing, phenotype, evidence-quality, and
  uncertainty boundary with a pharmacology reviewer. **Exit:** patient-isolation and
  inhibitor-retraction negatives, dose/route/time boundary tests, and clinically
  reviewed scenario fixtures pass in `nibli-engine`, `nibli-ui`, and the pin/seam
  gates; Chapter 20 is recaptured from the live corpus and is labeled a synthetic
  teaching model until that review exists.

---

## Chain — Editor / Linguist / LSP (syntax tooling)

Policy: book and gates keep fence tags **`nibli` / `nibli-kr`** (never a foreign
language alias). Seed grammar lives in `grammars/` (`nibli.tmLanguage.json` +
injection sketch + `grammars/README.md`). Runtime lexer remains
`nibli-kr/src/highlight.rs` (REPL / UI) — keep token classes aligned when anything
here changes. Keywords must stay equal to `nibli_lexicon::RESERVED_WORDS`.
(Whole section re-verified 2026-08-16: no artifacts have appeared — still no
`editors/`, no `nibli-lsp`, no tree-sitter grammar, no `tower-lsp`/`lsp-server` in
`Cargo.lock`; `grammars/` is read by exactly one thing, the keyword ratchet.)

Independent starters (any order):

- **VS Code / Cursor extension (local):** *(effort: medium)* package `grammars/nibli.tmLanguage.json`
  as language id `nibli` for `*.nibli`, plus markdown fence injection for
  `nibli` and `nibli-kr` via `grammars/nibli-markdown-injection.json`. Ship as
  `editors/vscode/` (or a small sibling repo) with `language-configuration.json`
  (`#` line / `/* */` block). Optional: publish to Open VSX / Marketplace.
  → Unblocks the editor docs page below.
- **GitHub Linguist PR:** *(effort: medium — the submission work; merge is
  externally gated on Linguist's usage threshold)* submit `source.nibli` + samples from shipped corpora
  (`gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli`, …); language name
  **Nibli**, extensions `.nibli`, aliases `nibli-kr` / `nibli kr`. Until merge,
  github.com fences stay uncolored — do not retag book fences to `prolog` etc.
- **Tree-sitter grammar (`tree-sitter-nibli`):** *(effort: high)* new crate/repo tracking
  `nibli-kr.pest` by discipline (not codegen). Queries: `highlights.scm`,
  `locals.scm`, `injections.scm` for Markdown. Consumers: nvim-treesitter,
  Helix, Zed. Does **not** replace Linguist/TextMate for github.com.
  → Unblocks the tree-sitter keyword ratchet below.
- **`nibli-lsp` (thin LSP):** *(effort: high; diagnostics-only first cut: medium)* workspace
  bin on `tower-lsp` (or `lsp-server`) using
  `nibli_kr::parse_checked` diagnostics, lexicon hover/completion (gloss,
  places, templates), optional format via `nibli_kr::render`, optional semantic
  tokens from `nibli_kr::highlight::lex`. Single-file first; multi-file KB
  projects later. → Also unblocks the editor docs page below.

Blocked followers:

- **Conformance guard — TextMate half LANDED** *(effort of the still-owed tree-sitter half: low)*
  (`just verify-grammar-parity`, in
  `ci`: set, order and the `\b` anchors vs `RESERVED_WORDS`). Still owed: the same
  ratchet for the Tree-sitter keyword list — blocked on the tree-sitter grammar
  existing.
- **Editor/LSP docs (mdBook)** *(effort: low, once unblocked)* — blocked,
  precondition UNMET, and the last docs
  item that outlived `DOCS_TODO.md`. Everything above is design + seed artifacts:
  `grammars/` holds a TextMate grammar and an injection sketch that **no build or
  CI job consumes** (only the keyword ratchet reads it), and there is no
  `editors/` dir, no `nibli-lsp` crate, no tree-sitter grammar, and no `tower-lsp`
  anywhere — `Cargo.lock` included. Writing the page now would present aspiration
  as shipped, which the docs' own epistemic rule forbids. Revisit when
  `editors/vscode/` or `nibli-lsp` actually exists.
- **Book fence rename (optional, coordinated):** *(effort: medium)* if/when fences go plain
  `nibli` only, retarget `verify_book.py` + capture harness + injection regex in
  one PR; keep `nibli-kr` as Linguist/VS Code alias forever.

---

## Blocked on external repos — nothing in this repo is missing

- **Synchronize the manuscript with the resolved existential-import algebra (engine
  decision complete 2026-08-05; book-repo work only).** *(effort: high)* The engine now uses clean-core
  as the high-assurance default: a description universal mints no entity, so `some`,
  `??`/`query_find`, `count_witnesses`, and `exactly 0/1` all range over the same
  ordinary domain. Explicit legacy import remains available
  (`set_existential_import(true)`, `NIBLI_EXISTENTIAL_IMPORT=1`,
  `:existential-import on`); when enabled, every imported witness participates in
  ∃/∀/find/count/aggregate-derived enumeration rather than being selectively hidden.
  `WitnessBinding.origin`, `ExistsWitness.origin`, and
  `CountResult.existential_imported` expose that contribution; a profile toggle
  transactionally rebuilds the loaded KB, and the host/browser surfaces report the
  active profile. Engine evidence: `nibli-engine/tests/integration.rs` pins the ON/OFF
  `some`/forall/find/exact-0/exact-1/count/aggregate/retraction matrix and live toggles
  (:1710, :1831, :1906, :1927 as of HEAD `5777ced`); `smoke-host-existential-import`
  pins the component path; the independent oracle engines explicitly select clean-core.
  **Remaining work:** in the separate `book/` repository, update Chapters 5, 8, and 12
  plus Appendices A, B, E, and K to describe this exact algebra, the default/opt-in
  controls, structural witness origin, the 0.9.0-introduced witness-origin proof
  surfaces (current package is `nibli:engine@0.11.0` — cite the live version, not
  0.9.0), the fact that ON→OFF/OFF→ON applies immediately to already-loaded rules, AND
  — since `5580618` (2026-08-12) — the complete-or-error collection contract: `find`/
  `count_witnesses`/`aggregate` now refuse ("witness enumeration incomplete") whenever
  any final evaluated candidate leaf is non-definitive, under either polarity, instead
  of undercounting (GUARANTEES "Collections are complete or error"). Chapter 12's
  consent capture currently depends on the historical import profile (the engine's
  `ch12_consent_case_study_traced_query_completes` watchdog —
  `nibli-engine/tests/known_failures.rs`:333 — now selects it explicitly), so either
  mark that profile in the capture or recast the example for clean-core. Run the book
  validator, reference checker, capture checker, and two byte-idempotence passes before
  removing this residual with the `book-todo` workflow.

- **Synchronize the manuscript with query-only exact-count semantics (engine
  decision complete 2026-08-05; book-repo work only).** *(effort: medium)* The engine no longer
  generates witnesses for an asserted `CountNode`: every assertion, assumption,
  and preassigned/replay ingress rejects `exactly N`/`no` in asserted position before
  allocating an id or mutating state. Counts remain valid queries over the current
  closed domain, collapse equality classes, include explicitly enabled legacy-import
  witnesses with structured `CountResult` provenance, and may change after facts,
  equality links, import-profile changes, or retractions. `exactly 0` is a query,
  never a stored prohibition. Counts inside opaque abstractions are quoted content,
  not outer-KB constraints. Legacy persisted count-assertion rows fail replay
  non-destructively. Root specs/docs and Formalize's assertion-authoring guard are
  synchronized; do not reintroduce the retired generative reading. (The separate
  exact-`CountNode` evaluator was explicitly PRESERVED through `5580618`'s
  witness-enumeration change — both CHANGELOG and GUARANTEES say so — so this entry's
  semantics are unaffected by that commit.) Update Chapters 4 and 8 plus Appendices
  A/B/E and any renderer/capture exposition to present exact counts only on query
  surfaces; rewrite examples that currently load them as KB statements. Run the book
  validator, reference checker, capture checker, and two byte-idempotence passes
  before removing this residual with the `book-todo` workflow.

- **Synchronize the manuscript with the fail-closed aggregate outcome (engine done
  2026-08-16; book-repo work only).** *(effort: low)* `KnowledgeBase::aggregate` /
  `aggregate_text` now return the typed `AggregateOutcome` — `Empty` for a complete
  zero-witness enumeration, `Value { value, witnesses }` with contributing-witness
  provenance — and REFUSE (distinct reasoning errors) a binding set missing the
  variable, a non-numeric value, a non-finite operand, and an overflowed result;
  the 5580618 incomplete-enumeration refusal is unchanged, and no WIT surface
  exposes aggregation. Update Chapter 20 and Appendices B/E to present this
  contract (and drop any "silently skips non-numeric witnesses" phrasing). Run the
  book validator, reference checker, capture checker, and two byte-idempotence
  passes before removing this residual with the `book-todo` workflow.

- **Synchronize Chapter 11 with the one-path retraction model and the renamed
  benchmark (engine done 2026-08-16; book-repo work only).** *(effort: low)* The
  engine repo no longer contains any live two-path retraction claim: the public
  `retract_fact` doc, the benchmark (now ONE criterion group, `retraction`, with
  `text_event_decomposed` / `flat_direct_inject` fixture VARIANTS of the same
  rebuild path, verdict-asserted fixtures, and a methodology header), the
  write-only `rule_source_map` (removed outright), and the stale test
  names/comments are all reconciled. Chapter 11 still describes and measures the
  retired incremental path and quotes the old `retraction_rebuild` /
  `retraction_incremental` group names — re-derive its table from the new bench
  (`cargo bench -p nibli-engine --bench engine_bench -- retraction`) on
  documented hardware and rewrite the prose to the one-path story. Run the book
  validator, reference checker, capture checker, and two byte-idempotence passes
  before removing this residual with the `book-todo` workflow.

- **Synchronize Chapters 16/21 with the real N-Triples export (engine done
  2026-08-16; book-repo work only).** *(effort: low)* `nibli-import --export` now
  emits valid, independently-parsed N-Triples for the representable fragment
  (arity-2 surface tuples over IRI-safe constants/finite numbers, re-projected
  from the store's event decomposition under the minted `http://nibli.dev/kb#`
  base) and REFUSES everything else with per-fact reasons on stderr — the old
  `# fact:<id> <label>` comment-line dump and its stale Lojban wording are gone.
  Update Chapter 21's Turtle import/export exposition (and Chapter 16 if it
  quotes the old dump) to the fragment-plus-refusals contract; re-capture any
  transcripts. Run the book validator, reference checker, capture checker, and
  two byte-idempotence passes before removing this residual with the
  `book-todo` workflow.

- **Recapture Chapter 17 from the new verdict-class `[Why]` renderer (engine done
  2026-08-16; book-repo work only).** *(effort: low)* `[Why]` is now verdict-driven:
  a computed FALSE prints "Decided by computation: … (computed locally / by the
  trusted backend)" instead of the closed-world sentence, UNKNOWN prints a
  per-reason "No verdict: …" line (backend-unavailable, non-finite), and
  RESOURCE_EXCEEDED prints the budget-cutoff sentence. Chapter 17's transcripts
  quote the old fallback under these verdicts — recapture from real bytes. Run the
  book validator, reference checker, capture checker, and two byte-idempotence
  passes before removing this residual with the `book-todo` workflow.

- **Document the proof envelope on the book/docs surfaces (engine done
  2026-08-16; book-repo work only).** *(effort: low)* `ProofEnvelope` binds
  verdict + trace + session profile + the lockstep engine version into one
  schema-versioned, independently-validatable certificate (`validate_envelope`,
  KB-free); surfaces: `certify_text` (engine/session), wasm `certify` (JSON),
  nibli-host `:certify` (document on stdout, validator verdict on stderr — no
  WIT change). Chapter 17/Appendix C exposition should present it as THE
  durable proof artifact (a bare trace cannot prove which non-TRUE verdict it
  accompanied). Run the book validator, reference checker, capture checker, and
  two byte-idempotence passes before removing this residual with the
  `book-todo` workflow.

- **Wire `dhilipsiva.dev/docs/nibli/`** *(effort: low)* in the external `dhilipsiva/dhilipsiva.dev`
  repo, on the `nibli-updated` dispatch this repo already fires: checkout nibli →
  `just docs` (default `site-url=/docs/nibli/`) → copy `mdbook/book/` →
  `public/docs/nibli/`. Recipe and requirements are `DEPLOY.md` §2b. **Do not call
  the primary URL live until it returns HTTP 200** — until then the canonical
  public docs URL is the GitHub Pages mirror, `dhilipsiva.github.io/nibli/`, which
  `docs-pages.yml` already deploys. Blocked here only in the sense that the work
  is in another repo; nothing in this one is missing. (Search needs no attention
  under either base path: every mdBook asset, the searcher and the index included,
  is referenced through `path_to_root`, verified in the built output.)

---

## Pointers

| Tracker / doc | Scope |
|---------|--------|
| **This file** | Engine runtime, editors/tooling, docs hosting, open semantics decisions — the ONE repo tracker since `DOCS_TODO.md` retired |
| **`RELEASING.md`** | Release decisions of record (tiers, lockstep, tags) + the operator runbook |
| **`DEPLOY.md`** | Hosting: playground, wasm demo, mdBook primary + Pages mirror |
| **`book/TODO.md`** | Manuscript only (private checkout; Orange AVA) |

## Lucy D

- **Engine performance finding (2026-09-15, reproducer below).** On a KB holding Lucy's
  constitution (`lucy-cli/constitution/lucy.nibli`: `derived_only` heads, `exist -> person`,
  `leave -> person`, three `entitled(every person, event { P() })` floor lines, two
  `~leave` NAF rules with 2 variables, one 3-variable `grant -> permitted` rule) plus N
  unrelated ground facts `human(PersonI).`, the query `person(Lucy).` costs, in a debug
  build: N=5 0.3 s, 10 0.6 s, 20 1.8 s, 40 8.1 s, 80 ≈47 s — roughly quadratic in facts
  the query never touches. Bisect at N=20: dropping the three `entitled` lines halves it
  (0.9 s); dropping the `~leave` rules 1.5 s; dropping Article 2 no change; with only
  Article 1 + `derived_only` 0.1 s. `NIBLI_MATERIALIZE=0` is not read by nibli-engine;
  `LUCY_MATERIALIZE=0` (→ `set_materialization(false)`) makes no difference (8.6 s vs
  8.2 s at N=40), so materialization is not the cause.
  Reproducer: `LUCY_HOME=$(mktemp -d)/l; lucy init; for i in $(seq 1 40); do echo
  "human(P$i)." >> $LUCY_HOME/memory.nibli; done; time lucy ask 'person(Lucy).'`.
  Lucy's capsule sidesteps it (standing lines computed before the memory loads); user
  `ask`s still pay it. Hypothesis to check first: universal rules with abstraction heads
  and body variables unbound by any indexed fact enumerate the whole domain per query.
- **Deferred, wanted later:** code-browsing tools for LLMs in `lucy` (`code tree | outline
  <file> | find <symbol> | grep <pattern>`, deterministic and token-cheap) plus her own
  summaries of code as tagged memories; the browser page (`lucy-wasm`: two editors over
  nibli-wasm, import/export of the same files); `lucy` in the release binary matrix for
  Linux, macOS and Windows; an optional `Stop` hook that records Lucy's reply itself.
