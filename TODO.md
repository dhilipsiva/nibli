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
    divergence and is not passing by skipping. **Random-corpus coverage DONE:** a deterministic
    property-based generator (`nibli-verify/src/generator.rs`) builds random NAF-free
    definite-Horn programs (facts + `ro lo P cu Q` taxonomy rules + an atomic query over the
    fallback vocabulary); the CI gate runs a seeded batch (`NIBLI_VERIFY_RANDOM_COUNT`, default
    200) and asserts nibli agrees with Vampire on every mappable case (200/200 agree).
    **gdpr/ddi mappable-slice coverage DONE:** `run_corpus_slice` (`nibli-verify/src/corpora.rs`
    + lib) auto-extracts the classical Horn/NAF-free sub-slice of `gdpr.lojban` /
    `drug-interactions.lojban` (the filter decides — deontic/NAF lines skipped), mines the
    entities + type-predicates, and checks every atomic `la .E. cu P` query vs Vampire (gdpr
    50/50, ddi 56/56 agree). This caught + fixed a real translator bug — `zo'e` was dropped to
    `$true` (existential) instead of a rigid `zoe` constant, diverging from nibli on
    specified-vs-unspecified fillers. **Phase 2 — the ASP/clingo stratified-NAF oracle: DONE.**
    A second oracle (`nibli-verify/src/asp.rs` + `oracle_asp.rs`) covers the stratified
    negation-as-failure + closed-world fragment Vampire cannot (no CWA). The translator
    **regroups the event decomposition back to function-free surface Datalog** (ASP heads can't
    hold existentials, and Skolemizing the event to a function would break clingo's grounding),
    emitting `q(V0) :- p(V0), not r(V0).` for `ro lo P poi na R cu Q`; the reified `goal` atom's
    membership in clingo's unique stable model = nibli's closed-world verdict (sound because a
    stratified program's perfect model = its unique answer set, per `proofs/Stratification.lean`;
    and nibli rejects unstratified KBs at assert time, so only unique-model programs reach
    clingo). Gated in CI via `just verify-soundness`: a curated NAF corpus (`corpus_naf.rs`, 11/11
    agree) + random stratified-NAF programs (`generator::random_naf_case`, stratified by
    construction; `NIBLI_VERIFY_NAF_RANDOM_COUNT`, default 100; 95/100 checked, 0 diverge). Needs
    `clingo` (Nix shell; skips if absent). **Remaining:** deontic-headed NAF (the real
    `gdpr.lojban:101` erasure rule) and `du`-equality are conservatively skipped — a later slice
    could model deontic heads as plain ASP atoms.
  - **Track B — mechanized proof (long-term).** **Phase 1 — the four-valued combiner: DONE**
    (Lean 4 chosen as the assistant). `proofs/Combiner.lean` proves the verdict combiner's
    soundness algebra — conjunction/disjunction/negation never fabricate a definitive verdict
    nor swallow a non-definitive operand (the `True ∧ Unknown → False` bug closed), plus the
    RE-precedence and negation laws. Bridged to the real Rust by the exhaustive
    `exhaustive_soundness_matches_lean_model` conformance test in `logji` — for the finite
    combiner, model proof + exhaustive conformance = a complete guarantee. Gated in CI via
    `just verify-proofs`. **Phase 2 — the NAF stratification criterion: DONE.**
    `proofs/Stratification.lean` proves the dependency-graph condition the engine checks
    ("no negative edge with both endpoints in one SCC") is equivalent to the existence of a
    valid stratification (level function) — so the check accepts ⇒ genuinely stratifiable
    (soundness) and never wrongly rejects a stratifiable program (completeness). Mathlib-free
    (`level = |reachable set|`). Bridged to the real Tarjan-based `check_stratification` by the
    `check_stratification_matches_proven_criterion` corpus conformance test (hand-crafted +
    randomized graphs; corpus, not exhaustive — graphs are unbounded). **Phase 3 — the SCC
    decomposition: DONE.** `proofs/Scc.lean` proves SCCs are the mutual-reachability equivalence
    classes (`SameSCC` refl/symm/trans), so the partition is well-defined + unique (`decomp_unique`,
    `canonicalComp_correct`), and that the SCC-based check the engine runs equals the criterion
    (`sccRejects_iff_criterion`: a negative edge with both endpoints in one SCC ⟺
    `RejectsByCriterion`, which composes with Phase 2 to `⟺ ¬Stratifiable`). Bridged to the real
    Tarjan `compute_sccs` by the `compute_sccs_matches_scc_spec` conformance test (output is a
    partition + same-SCC ⟺ mutually-reachable, over the shared corpus). **Phase 4 — the
    one-directional unifier: DONE.** `proofs/Unify.lean` models `GTerm`/`Subst`/`subst`/`unify`
    (mirroring `logji/src/kb.rs` `unify_terms`/`substitute_term`) and proves `unify_sound`
    (`NoVar c → unify t c σ₀ = some σ → subst σ t = c` — a successful match instantiates the
    template to exactly the ground goal), via the `unify_extends` + `subst_stable` lemmas that
    discharge the `depPair` accumulator case, plus `unify_minimal` (no extraneous bindings). Bridged
    to the real `unify_facts`/`substitute_fact` by the `unify_conformance` corpus test (soundness +
    determinism + minimal bindings over hand-crafted + random term pairs). **Phase 5 — rule firing:
    DONE.** `proofs/RuleFiring.lean` lifts `unify_sound` from terms to atoms (`unifyArgs_sound` /
    `unifyAtom_sound` — the arg-wise fold mirroring `unify_facts`) and then to a firing step:
    `firing_sound` proves that if a rule holds in the model M, its head unifies with the ground goal
    via σ, and σ discharges the conditions (positive in M; negated not in M, by NAF), then the goal
    is in M — a sound universal-instantiation + modus-ponens step, with NAF-condition soundness
    delegated to Phases 2–3; `firing_no_fabrication` is the contrapositive. Bridged by the
    `rule_firing_conformance` engine test (fires exactly when conditions discharged — all four
    corners — never fabricates, and records the σ-instantiated head). **Remaining:** only the
    headline theorem — a recorded proof trace ⇒ the conclusion holds in the stratified/perfect model
    (per-`ProofRule` local soundness + induction over the trace DAG, composing all five proofs).
    Scope to the core, not the parser.
  - **Milestone order:** Track-A Horn-fragment differential gate ✓ DONE; Track-A random-corpus
    coverage ✓ DONE; Track-A gdpr/ddi mappable-slice coverage ✓ DONE; Track-A Phase 2 ASP/clingo
    stratified-NAF oracle ✓ DONE; Track-B combiner proof ✓ DONE; Track-B stratification-criterion
    proof ✓ DONE; Track-B SCC-decomposition proof ✓ DONE; Track-B unifier proof ✓ DONE; Track-B
    rule-firing proof ✓ DONE. Next: the headline trace ⇒ model theorem (and, optionally, deontic-NAF
    coverage in the ASP oracle).

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
