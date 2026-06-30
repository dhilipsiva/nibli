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

Legend: 🐞 genuine bug · ⚖️ honesty/framing · 🧪 test rigor · 📐 verification · 🚪 adoption.

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

_(none open)_

---

## P5 — Foundations & adoption (raising the ceiling)

These are NOT gaps against the current headline (P1–P4 cleared all of those). They are the
frontier the honest engine review identified: the ceiling now is soundness-by-PROOF and the
adoption story, not code quality. Each is bigger than a single `engine-todo` item — scope
into phases.

- [ ] 📐 **Soundness by proof, not just tests.** Today soundness is empirical (639+ tests);
  `GUARANTEES.md` openly admits a bug in gerna/smuni/logji could mint a valid-looking proof
  of a false statement. Two tracks:
  - **Track A — differential testing against an established prover (near-term, high ROI).**
    **Phase 1 — Horn/NAF-free gate: DONE.** The `nibli-verify` crate exports the smuni FOL IR
    (`LogicBuffer`) of the cleanly-mappable fragment to TPTP FOF and checks nibli's verdict
    against **Vampire** over a curated corpus; gated in CI via `just verify-soundness` (part of
    `ci`). A conservative filter (source-level negation scan, since a rule's implication arrow
    and a real `na` both flatten to `Not`; + a buffer non-classical-node scan; + a
    definitive-verdict / non-NAF check) keeps only the negation-free definite-Horn fragment,
    where nibli-True ⟺ Vampire `Theorem` and nibli-False ⟺ `CounterSatisfiable` both hold. 14/14
    curated cases agree; an anti-vacuity check (negated conjecture) confirms the gate detects
    divergence and is not passing by skipping. **Remaining:** (a) feed the
    `fuzz-assert`/`fuzz-query` generators + property-based gen so the corpus is large/random,
    not just curated; (b) map the mappable sub-slice of the `gdpr`/`ddi` corpora; (c) **Phase 2**
    — extend the oracle to an ASP/Datalog solver (clingo / DLV) for the stratified-NAF +
    closed-domain fragment, where perfect/stable-model semantics matches (the semantics gap a
    classical open-world prover cannot cover).
  - **Track B — mechanized proof (long-term).** Formalize the soundness-critical core in a
    proof assistant (Lean 4 / Coq / Isabelle): the unifier (one-directional pattern-vs-ground),
    rule firing, the NAF stratification check, and the four-valued combiner (which had a real
    bug — `True ∧ Unknown` must be Unknown). Prove: a recorded proof trace ⇒ the conclusion
    holds in the stratified/perfect model. Scope to the core, not the parser.
  - **Milestone order:** Track-A Horn-fragment differential gate ✓ DONE (cheap, catches real
    bugs), then the fuzz/corpus expansion + the ASP oracle for NAF (Phase 2), then optionally
    Track B.

- [ ] 🧪 **Close the flat-vs-surface test gap so the unit layer can't lie.** logji's flat test
  helpers (`logji/src/tests.rs`: `make_query` / `make_numeric_query` / `make_compute_query` /
  `query_with_proof`) hand-build `LogicBuffer`s, skipping the event/Neo-Davidsonian
  decomposition smuni emits on the real path — so a flat unit test can pass/fail DIFFERENTLY
  from the shipped pipeline. Proven this session: the `cwa_false` numeric case was correct
  through nibli-engine (surface) but the flat helper mis-flagged it (no `ComputeCheck(numeric)`
  step). Whole behavior classes (witness/skolem dependency, compute decomposition, the
  numeric-vs-absence FALSE distinction) are only catchable at integration level. Options:
  (a) generate flat buffers FROM smuni (`smuni::compile_from_gerna_ast(gerna::parse_checked(..))`)
  so the unit shape matches the real one; (b) a metamorphic/differential test that builds each
  query BOTH ways and asserts verdict + trace-shape agree; (c) route the `make_*` helpers
  through the same event decomposition; (d) a CLAUDE.md/CI discipline requiring a paired
  nibli-engine integration test for any reasoning behavior. **Recommend (a)+(b) for the
  compute/numeric helpers (proven-divergent), (d) as the standing guard.** Audit every flat
  helper for shapes smuni builds differently.

- [ ] 🚪 **Demonstrate the authoring problem is tractable for a non-Lojbanist.** The engine is
  sound + transparent, but knowledge-in requires writing Lojban (or the BYO-key LLM Translate).
  No evidence yet that a non-Lojbanist can author a CORRECT KB — and "sound relative to what
  you asserted" is hollow if authoring silently asserts the wrong thing. Build a reproducible
  **authoring study/benchmark** (a study, not just code): a non-Lojbanist + the playground
  (Translate + Transparency Triad) authors a KB for a real domain (GDPR subset / drug
  interactions / an eligibility or access-control ruleset). Measure (1) round-trip fidelity
  (does the LLM's Lojban back-translate to the author's intent?), (2) error-catch rate (how
  often the back-translation + proof let the author catch a mistranslation BEFORE it corrupts
  the KB), (3) time-to-correct-KB + iterations, and — most important — (4) the **silent
  mistranslation rate** (wrong premises that pass undetected → a confident wrong proof; the
  worst case for a "zero-hallucination" engine). Deliverable: the benchmark + a written report
  (book appendix), and any authoring-assist UX the failure modes demand (back-translation
  diffing, ambiguity flags, a "did you mean" loop).

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
