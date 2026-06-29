# Nibli — Backlog (ordered)

This backlog records the still-open gaps, ordered top-down by what to tackle next.

**Status.** Overall fidelity is high: the parser, semantic compiler, reasoning core,
WASM/WIT surface, and the Transparency Triad do what the book describes; both case-study
corpora (`gdpr.lojban`, `drug-interactions.lojban`) are fixed and test-pinned; the
human-readable rendering layer is fully consolidated into `nibli-render` (IR-driven
back-translation, one proof-trace walker, host-side typed-`LogicBuffer` `:debug`). The
four-valued contract (`True/False/Unknown(CycleCut|IncompleteKnowledge|NafDependent)/
ResourceExceeded(Depth|Fuel|Memory)`) is the right design and is *mostly* honest — but a
2026-06-28 crate-wide review (43-agent read-only panel + by-hand verification of the
soundness-critical paths) surfaced a handful of genuine soundness/honesty gaps against the
"zero-hallucination / every conclusion formally derived" headline. Those are the live P1–P4
items below.

Legend: 🐞 genuine bug · ⚖️ honesty/framing · 🧪 test rigor.

---

## P1 — Soundness bugs (contradict the "zero-hallucination" contract)

_(none open)_

---

## P2 — Correctness / robustness

_(none open)_

---

## P3 — Test rigor

_(none open)_

---

## P4 — Honesty of claims (mostly docs/UX, no engine change)

- [ ] ⚖️ Default proof views collapse trusted-backend and local-arithmetic to the same
  `⊢ computed` label, erasing the derived-vs-trusted distinction (recoverable only via
  `:proof-verbose`). Thread `method` through `MacroKind::Computed`.

- [ ] ⚖️ The CWA-honesty flag (`ProofTrace.naf_dependent`) fires for `na→True` NAF steps but
  not for the equally-CWA-dependent positive `FALSE`. Consider flagging CWA-dependent FALSE
  too, or document that every non-numeric FALSE is closed-world.

- [ ] ⚖️ **LOW** — No NaN/Infinity guards in built-in arithmetic (only reachable via
  ~309-digit input → non-finite result returns a confident FALSE). Return None/Unknown on
  non-finite operands or results.

---

## Verified NON-issues (do not act on)

- `IncompleteKnowledge` "unreachable for bare atoms" → correct CWA design; atoms still reach
  `CycleCut`/`NafDependent`.
- "dunli vs arithmetic equality is exploitable" → the specific exploit is not constructible
  (no dataflow from a computed sum into `dunli`).
- Missing occurs-check in `unify_terms` → non-issue; unification is one-directional
  pattern-vs-ground, so cyclic bindings are impossible.

---

## Verification (when implementing)

- `just ci` (fmt + clippy + native tests), `just test` for logji (`--test-threads=1`, shared
  global state), `just ci-wasm` (six gasnu smokes), `just ci-all` before push.
- Combiner/deontic/find-path fixes need **nibli-engine integration tests** — flat logji test
  helpers skip event decomposition, so witness/skolem-dependent behavior must be exercised
  through the full pipeline.
- Run via the WSL Nix dev shell per `CLAUDE.md`.

---

## Completed (historical record)

Carried over from the prior backlog (the book-vs-code audit + the 2026-06-10 deep
code-review panel: 35 agents, 11 confirmed + 3 partial + 0 refuted). These shipped and are
retained only as a record:

- **Plain-English `[Why]` proof summary** — `nibli_render::summarize_proof` (reusing the
  place-frame templates) sits above the detailed trace on every human surface: gasnu REPL
  (`[Why] …`), nibli-server (`proofSummary` GraphQL field), nibli-ui (`.proof-why` callout).
- **Per-step macro-logical-DAG proof collapse (all phases)** — the compressed DAG of
  surface-level steps tagged `[given]` / `[by the rule: …]`, role/event scaffolding folded
  into expandable clusters, is now the DEFAULT proof view everywhere; verbose trace reachable
  via gasnu `:proof-verbose`, UI expandable clusters, server `proof_trace_json`. P1 render
  engine (`collapse_proof`/`render_collapsed_text`), P2 nibli-ui `ProofTreeView`, P3 gasnu
  default + `smoke-gasnu-collapse` in `ci-wasm`, P4 book Ch 11, P5 nibli-server + nibli-wasm.
- **`go'i`-bare "nondeterminism" — re-characterized + smoke hardened (2026-06-29).** The bare
  `? go'i` verdict is provably DETERMINISTIC at the default fuel budget: `:debug` shows it
  compiles to `∃ev. gerku(ev) ∧ gerku_x1(ev, adam) ∧ gerku_x2(ev, zo'e)`, the ground `adam`
  anchors the candidate set to a single event, the search short-circuits, and `query_holds` is
  a yes/no verdict where hash-seed iteration order affects COST not ANSWER (250/250 TRUE over
  repeated standalone runs). The one observed `ci-all` flake was a rare WASM-host/CI transient,
  NOT a reasoning nondeterminism (the original P1 framing was wrong). `smoke-gasnu-goi-bare` now
  RETRIES ONCE so a transient cannot false-red CI, while a persistent fail across both attempts
  still fails as a real regression. (Follow-up 2026-06-29: the suspected "rebuild/replay-on-trap
  spin" was investigated and found INVALID — the trap-recovery retry IS bounded: the rebuild runs
  once per command, the journal replay breaks on first failure, and a trapped command is never
  auto-retried (whole 11-command low-fuel session completes in ~4s). The ~800% CPU was Wasmtime's
  parallel cranelift compilation of the component at each gasnu startup, amplified by the repro
  loop spawning many processes — not a reasoning spin. A separate, bounded, pathological residual
  remains: at fuel set below the session constructor's cost (≤~1000 vs the 1e10 default), the
  rebuild can't reconstruct the session, so each command prints a raw backtrace + "cannot enter
  component instance" until fuel is raised. Cosmetic, not a soundness issue.)
- **Better English for complex conclusions** — multi-place rule clauses pad non-x1 places
  with "something" (`frame::template_max_place`); curated literal place-frames for corpus
  proxy words (`zanru`/`pilno`/`katna`/`zenba`/`cinla`/`ckape`/`vimcu`). Render-only.
  *Honest residual limits (documented):* a multi-variable join (`fanta ∧ katna → zenba`)
  renders with a shared "X" subject; a nested abstraction (`se bilga lo nu se vimcu`) renders
  as a flat conjunction — recovering these needs carrying rule structure through the trace (a
  WIT/protocol change). Note P1 above re-flags the multi-variable paraphrase honesty gap.
