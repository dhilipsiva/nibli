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

The proof trace is more user-friendly now: a render-only plain-English `[Why]` summary (`nibli_render::summarize_proof`, reusing the place-frame templates) sits above the detailed trace on every human surface — the gasnu REPL (`[Why] …` line), nibli-server (the `proofSummary` GraphQL field), and nibli-ui (a `.proof-why` callout above the proof tree).

**Per-step macro-logical-DAG collapse (in progress, phased):** the product-vision proof viz — a compressed DAG of surface-level steps (Modus Ponens / Universal Instantiation) with the role/event scaffolding folded into expandable clusters, REPLACING the verbose trace everywhere (UI + gasnu + book) while keeping the verbose trace reachable (a gasnu `:proof-verbose`, the UI's expandable clusters, a book "Under the Hood" section).
- **Phase 1 (DONE):** the render-only engine in nibli-render — `collapse_proof(trace) -> RenderedNode` + `render_node_text` (reuses `RenderedNode`/`RenderedNodeView`, no parallel type; shares `regroup_event_leaves` with `summarize_proof`). Ships inert.
- **Phase 2 (DONE):** nibli-ui — `ProofTreeView` calls `collapse_proof`; the `proof-role-detail` cluster is an expandable `<details>` (reusing `RenderedNodeView`); `auto_open`/CSS tuned.
- **Phase 3 (pending):** gasnu — `?` shows the collapsed text by default; a `:proof-verbose` command keeps the verbose trace.
- **Phase 4 (pending):** book — Ch 11 rewrite (collapsed default, verbose demoted to "Under the Hood") + recapture C08/C11 (the case studies elide their traces).
- **Phase 5 (pending):** nibli-server (`proof_trace` text → collapsed; `proof_trace_json` stays the full canonical trace) + nibli-wasm.

Also remaining: better English for complex multi-predicate / deontic / abstraction conclusions (today they gracefully degrade — a clean conclusion drops rather than renders rough).

