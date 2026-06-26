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

### Others

The proof trace is more user-friendly now: a render-only plain-English `[Why]` summary sits above the detailed trace in the gasnu REPL (`nibli_render::summarize_proof`, reusing the place-frame templates). Remaining (follow-up): (1) wire the same `summarize_proof`/`fact_to_english` into nibli-ui (above the proof tree) + nibli-server (a `proof_summary` response field) — the API is ready; (2) the fuller per-step collapse — a compressed macro-logical DAG (Modus Ponens / Universal Instantiation) that hides the role/event scaffolding inside expandable clusters (the product-vision proof viz), replacing rather than summarizing the trace; (3) better English for complex multi-predicate / deontic / abstraction conclusions (today they gracefully degrade — a clean conclusion drops rather than renders rough).

