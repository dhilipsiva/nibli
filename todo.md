# Nibli — Backlog (ordered)

This backlog records the still-open gaps from the book-vs-code audit + the 2026-06-10 deep
code-review panel, ordered top-down by what to tackle next. Overall fidelity is high: parser,
semantic compiler, reasoning core, WASM/WIT surface, and the Transparency Triad do what the book
describes; the deterministic firewall verdict is sound in the common cases; both case-study corpora
(`gdpr.lojban`, `drug-interactions.lojban`) are fixed and test-pinned; and the four-valued contract is
now honest end-to-end (`Unknown(NafDependent)` + host-translated `ResourceExceeded(Fuel/Memory)` both
land). The human-readable rendering layer is fully consolidated into the `nibli-render` crate (WS1–WS6
of `triad-trace-improvement.md`): back-translation is IR-driven, the proof trace renders through one
walker, the S-expression debug emitter is gone, and `:debug` renders the typed `LogicBuffer` host-side
as a `[Logic]` structural tree + `[English]` gloss — no S-expression string crosses any boundary. The
long tail below covers correctness remainders, documentation-vs-code mismatches, and DRY duplication.
(Panel provenance: 35 agents, 11 confirmed + 3 partial + 0 refuted; full output in
`code-review-panel-2026-06-10.json`.)

## P1 — High (soundness + production)

_No open items — the high-priority soundness/production backlog is clear; the remaining work below is correctness/completeness long-tail, docs-vs-code reconciliation, and DRY cleanup._

## P2 — Medium

_No open items._

## P3 — Low (long tail)

### gerna (parser/lexer)

### smuni (AST → FOL IR)

### logji core

### full pipeline + Transparency Triad
- [ ] **Cmevla whose inner form collides with a suppressed cmavo is silently dropped in the LEXICAL-gloss fallback** — now that WS4 made IR back-translation the primary path, this is a FALLBACK-path nit: `smuni_dictionary::back_translate` treats any dotted token as a cmevla, strips the dots, and consults the DICTIONARY first; a name like `.la.`/`.cu.` maps to the suppressed empty gloss and is dropped by `.filter(|s| !s.is_empty())`. _Location:_ `smuni-dictionary/src/lib.rs:25-33`. _Fix:_ in the cmevla branch return the inner name directly. (robustness)

### case studies
- [ ] **readme.lojban data-protection rule has convoluted polarity vs its comment** — `readme.lojban:107` `ro lo se kurji datni cu se fanta lo na se curmi` ties data protection to a double-negative whose intent is unclear; compiles but the predication doesn't cleanly express the stated intent. _Fix:_ reformulate so the agent holds the permission/right; verify via the back-translation. (correctness)

### engine guarantees / firewall claims
- [ ] **Residual non-REPL output surfaces still HashSet-order dependent (ordering only, verdicts unaffected)** — surfaces NOT reachable from gasnu REPL output: (1) `check_contradictions` violation order iterates `negative_facts`/`all_facts()` (engine/server API only); (2) `[Forward] Derived:` print order iterates a `lookup_predicate` HashSet clone (forward rules off by default). _Location:_ `logji/src/lib.rs` (check_contradictions); `logji/src/rules.rs` (trigger_forward_rules). _Fix:_ sort before returning/printing. (correctness)
- [ ] **Direct ForAll/Exists query quantifies over event Skolems and le-descriptions, risking spurious counterexamples for bare universal bodies** — `ensure_domain_members_cached` unions `known_entities`/`known_event_entities`/`known_descriptions` into one flat cache the ForAll/Exists evaluators iterate. Latent: a bare-predicate ForAllNode body would yield a spurious event-Skolem counterexample, but no current compilation path produces one (the guarded `Or(Not(P),Q)` makes event/desc members vacuously satisfy). _Location:_ `logji/src/reasoning.rs`; `kb.rs`. _Fix:_ have the quantifier evaluators range only over the appropriate sort (defensive). (correctness)

## Investigated — not issues

(No findings refuted in the audit or the 2026-06-10 panel; several were downgraded/reclassified, nuances captured inline above. Narrowings: the Python backend failure mode is uncaught-exception thread death, not CPU/RAM burn; gerna error LINE numbers are test-asserted, only exact COLUMN values are untested; "benches measure only failure paths" applies to bench_query_latency specifically.)
