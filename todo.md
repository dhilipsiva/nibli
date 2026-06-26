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

### case studies

### engine guarantees / firewall claims
- [ ] **Residual non-REPL output surfaces still HashSet-order dependent (ordering only, verdicts unaffected)** — surfaces NOT reachable from gasnu REPL output: (1) `check_contradictions` violation order iterates `negative_facts`/`all_facts()` (engine/server API only); (2) `[Forward] Derived:` print order iterates a `lookup_predicate` HashSet clone (forward rules off by default). _Location:_ `logji/src/lib.rs` (check_contradictions); `logji/src/rules.rs` (trigger_forward_rules). _Fix:_ sort before returning/printing. (correctness)
- [ ] **Direct ForAll/Exists query quantifies over event Skolems and le-descriptions, risking spurious counterexamples for bare universal bodies** — `ensure_domain_members_cached` unions `known_entities`/`known_event_entities`/`known_descriptions` into one flat cache the ForAll/Exists evaluators iterate. Latent: a bare-predicate ForAllNode body would yield a spurious event-Skolem counterexample, but no current compilation path produces one (the guarded `Or(Not(P),Q)` makes event/desc members vacuously satisfy). _Location:_ `logji/src/reasoning.rs`; `kb.rs`. _Fix:_ have the quantifier evaluators range only over the appropriate sort (defensive). (correctness)

### Others

The proof trace is not intuitive. Could make it more user friendly. People who look at trace root may not be tech saavy / understand lojban. There could be robot translations and ProofNode / ProofTerm short summarizations.

