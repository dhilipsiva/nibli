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

- [ ] 🐞 **MEDIUM** — Parser fail-OPEN holes (contradict the fail-closed posture).
  Unterminated `zoi` swallows the rest of input as one opaque constant with no error;
  dangling `zo` at end-of-stream silently dropped; predicate-less clause (`mi do`) fabricates
  a `go'i` selbri with no distinction from an explicit one (`gerna/src/preprocessor.rs`). The
  preprocessor has no error channel.
  **Fix:** give `preprocess` an error channel; reject truncated `zo/zoi/zei`.

- [ ] 🐞 **MEDIUM** — `lasna` `go'i` per-place merge bypasses smuni's fail-closed guards:
  duplicate FA places (`fe X fe Y go'i`) silently overwritten (smuni rejects "same place set
  twice"). Confined to the go'i merge path.
  **Fix:** apply the same arity/duplicate guards smuni's authoritative compiler uses.

- [ ] 🐞 **MEDIUM** (multi-node only) — 2P-Set CRDT merges on a non-namespaced `u64` id;
  independently-minted facts collide and one is silently dropped (no `MergeResult.added`, no
  error). Gated behind `:merge` (experimental).
  **Fix:** key fact identity on `(node_id, local-id)` / a UUID dot; detect payload mismatch
  and surface a conflict.

---

## P3 — Test rigor

- [ ] 🧪 **MEDIUM** — ~80 negative assertions use `!is_true()`, which passes for `False`,
  `Unknown`, AND `ResourceExceeded` alike — blunting the safety-critical False-vs-Unknown
  boundary. (This blind spot is why the P1 combiner bug survived.)
  **Fix:** sweep `assert!(!query(...))` → `assert!(query_result(...).is_false())` wherever
  the intended verdict is FALSE.

- [ ] 🧪 **LOW** — No test pins the CWA/CDA-relativity of `ForallVerified` / "False for
  missing fact". Add a regression test documenting these verdicts are closed-world-relative.

---

## P4 — Honesty of claims (mostly docs/UX, no engine change)

- [ ] ⚖️ Scope the README headline. "Every conclusion is formally derived — no
  hallucination, no approximation" should read as: derived **from asserted facts/rules under
  a closed-world + closed-domain assumption, plus results trusted from the compute backend.**
  `FALSE` = "not derivable," not "proved ¬P".

- [ ] ⚖️ Disclose that built-in arithmetic (`pilji/sumji/dilcu`) uses tolerant float
  equality (`isclose`, rel_tol 1e-9) — literally an approximation (while `dunli` is exact `==`).

- [ ] ⚖️ External compute (`tenfa/dugri`) is a **trusted oracle** auto-asserted as ground
  facts that rules chain on — an axiom source, not a derivation. State this where the
  "formally derived" claim appears.

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
- **Better English for complex conclusions** — multi-place rule clauses pad non-x1 places
  with "something" (`frame::template_max_place`); curated literal place-frames for corpus
  proxy words (`zanru`/`pilno`/`katna`/`zenba`/`cinla`/`ckape`/`vimcu`). Render-only.
  *Honest residual limits (documented):* a multi-variable join (`fanta ∧ katna → zenba`)
  renders with a shared "X" subject; a nested abstraction (`se bilga lo nu se vimcu`) renders
  as a flat conjunction — recovering these needs carrying rule structure through the trace (a
  WIT/protocol change). Note P1 above re-flags the multi-variable paraphrase honesty gap.
