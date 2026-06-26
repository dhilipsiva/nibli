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

**Per-step macro-logical-DAG collapse (DONE — all phases):** the product-vision proof viz — a compressed DAG of surface-level steps tagged `[given]` / `[by the rule: …]` with the role/event scaffolding folded into expandable clusters — is now the DEFAULT proof view everywhere, with the verbose trace reachable (gasnu `:proof-verbose`, the UI's expandable clusters, the server's full `proof_trace_json`).
- **Phase 1 (DONE):** the render-only engine in nibli-render — `collapse_proof(trace) -> RenderedNode` + `render_node_text`/`render_collapsed_text` (reuses `RenderedNode`/`RenderedNodeView`, no parallel type; shares `regroup_event_leaves` with `summarize_proof`).
- **Phase 2 (DONE):** nibli-ui — `ProofTreeView` calls `collapse_proof`; the `proof-role-detail` cluster is an expandable `<details>`.
- **Phase 3 (DONE):** gasnu — `?` shows the collapsed text by default (`run_proof_query`); `:proof-verbose` keeps the verbose trace; `smoke-gasnu-collapse` in `ci-wasm`. (Also fixed a dependent-Skolem grouping bug via `term::is_event_skolem_arg`.)
- **Phase 4 (DONE):** book (separate repo) — Ch 11 introduces/showcases the collapsed view (Preview + REPL section); the data-model/memoization sections are reframed as the "under the hood" view; the multi-hop Case Study + Exercises and the application chapters (Ch 8/12/18/20/21) use `:proof-verbose` (the full audit trace they discuss). `verify-book-capture` byte-clean across all 8 transcript chapters. (Editorial follow-up noted in book `revisions.md`: optionally showcase the collapsed view in the GDPR/pharma case studies.)
- **Phase 5 (DONE):** nibli-server (`proof_trace` text → collapsed via `collapsed_text_from_json`; `proof_trace_json` stays the full canonical trace) + nibli-wasm.

Remaining proof-UX polish: better English for complex multi-predicate / deontic / abstraction conclusions (today they gracefully degrade — a clean conclusion drops or renders the functional fallback rather than smooth English; e.g. `curmi → javni` falls back to `[by rule: curmi → javni]`).

