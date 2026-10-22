# Soundness & CI index

Every guarantee in
[GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md)
is backed by a gate you can run. This page indexes them: what each gate
checks, what it needs, and when it runs. The `Justfile` is the source of
truth for recipe contents.

## The umbrella recipes

| Recipe | What it is |
|--------|------------|
| `just ci` | The fast native gate (no WASM build): `fmt-check`, `release-check`, `clippy-runtime`, the unit sweep (`test`), `test-engine`, `test-host`, `test-ui`, `test-formalize`, `test-backend`, `test-store`, `test-persistence-replay`, and every `verify-*` gate in the table below — including `verify-proofs` (plus `verify-book-vocab`, which self-skips when the private `book/` checkout is absent) |
| `just ci-wasm` | The WASM behavioral gate: builds the component + host once, then runs 15 `smoke-host-*` scripts (trap recovery, persist-replay, statement split, schema-v3 migration, NAF note, CWA-false note, `:debug`, proof collapse, backend-unavailable, quiet, strict, existential-import, materialize, determinism, script) plus `verify-wasm-node` |
| `just ci-all` | `ci` + `ci-wasm` — the comprehensive pre-push gate |

GitHub Actions (`.github/workflows/ci.yml`) runs parallel jobs, all inside
the Nix shell: **native** (`just build-wasm` — bindings are generated,
gitignored, absent on fresh checkouts — then `just ci`), **wasm**
(`just ci-wasm`), **auth** (`just test-auth` + `check-auth-axum`),
**auth-py** (`just test-auth-py`), **docs** (`just docs`), and **fuzz**
(`just fuzz-ci`, time-boxed). Together, native and wasm are `just ci-all`.

## The `verify-*` gates

Track A proper is the differential-oracle family (the first row); the rest are
supporting native gates that ride the same `ci` umbrella.

| Gate | Oracle / method | Notes |
|------|-----------------|-------|
| `just verify-soundness` (Track A) | **Vampire** (classical FOL over the Horn/NAF-free fragment, via TPTP) and **clingo** (ASP over the stratified-NAF + closed-world fragment) check nibli's verdicts on curated + seeded-random programs, the mappable corpus slices, and the Predilex taxonomy leg; the tense pre-pass emits every rule once, preserving bare and explicit same-/cross-flavor literals, and every curated `tense_*` case must reach its oracle; plus the **non-stratified-rejection differential** (every accept/reject decision checked against an independent implementation of the proven criterion, with a post-rejection fresh-replay battery) and two engine-vs-engine metamorphic differentials: **retraction** (retract ≡ never-asserted) and **materialisation** (saturated ≡ backward-chained) | Solvers come from the Nix shell; each oracle side skips cleanly if its solver is absent. Batch sizes via `NIBLI_VERIFY_RANDOM_COUNT` (200), `…_NAF_…` (100), `…_TENSE_NAF_…` (100), `…_COUNT_…` (100), `…_STRAT_…` (300), `…_RETRACT_…` (200), `…_MATERIALIZE_…` (60) |
| `just verify-nibli-kr-seam` | Hand-verified FOL structural goldens + the full construct-inventory acceptance sweep + KR-internal metamorphic relations + the native determinism leg | The front-end's oracle; never skips |
| `just verify-alias-map` | The committed corpus's shape/provenance/compound invariants + a behavioral twin for **every** shipped entry (named ≡ positional; converted ≡ canonical base) | Never skips |
| `just verify-dict` | Corpus arities must cover independent **Predilex** lower bounds (vendored, SHA-pinned), keyed through the gismu provenance bridge | 132 words checked, floor 120; arity-only scope |
| `just verify-pins` | KB-level behavioural pins (`pins/*.nibli`) run by the native `nibli-pin` runner | Distinct exit codes: 1 = pinned property regressed, 2 = harness broken, 3 = a pinned defect no longer reproduces |
| `just verify-harness` | The known-failures control tests (the FOL control must pass; the red backlog stays opt-in) | |
| `just verify-doc-fences` | Every statement in a ` ```nibli-kr ` fence — under `mdbook/src/` and in the repo-root specs — must compile through `NibliEngine::assert_text`, the same path as the REPL's `:load` | Lives here, not in the `docs` CI job, which has no Rust toolchain and stays a ~2-minute `mdbook build`. The scope boundary is compilable example vs. metasyntax, carried by the info string: notation and the v2-only `pred` declarations sit in ` ```text ` fences, because tagging either ` ```nibli-kr ` claims it compiles today |
| `just verify-grammar-parity` | `grammars/nibli.tmLanguage.json`'s keyword alternation must equal `nibli_lexicon::RESERVED_WORDS` — set, order, and the `\b` anchors | The shipped TextMate grammar is a third mirror of the keyword list; the pest twin was already pinned inside nibli-kr, this closes the last one |

**Determinism** is a three-way gate: the same pinned corpus
(`determinism-corpus.nibli`) must produce identical verdicts on the native
engine (in `verify-nibli-kr-seam`), the Wasmtime component
(`smoke-host-determinism`), and node/V8 (`verify-wasm-node`, skips without
wasm-pack) — the browser-class runtime of the live playground.

## Track B — mechanized proofs

Six Lean 4 proofs in `proofs/` (no mathlib — self-contained, offline), checked
by `just verify-proofs` (skips cleanly without `lean`; the Nix shell provides
it). Each proof is bridged to the real engine by a Rust conformance test that
runs even when Lean skips:

| Proof | What it proves | Rust bridge |
|-------|----------------|-------------|
| `Combiner.lean` | The four-valued verdict combiner never fabricates a definitive verdict nor swallows a non-definitive sibling | `exhaustive_soundness_matches_lean_model` — all 10×10 inputs, so the guarantee is **complete** |
| `Stratification.lean` | The NAF criterion (“no negative edge whose target reaches back to its source”) is *equivalent* to a valid stratification existing | `check_stratification_matches_proven_criterion` |
| `Scc.lean` | The SCC-based check the engine actually runs equals the proven reachability criterion | `compute_sccs_matches_scc_spec` |
| `Unify.lean` | The one-directional unifier is sound and minimal (`subst σ t = c`; never binds a variable absent from the template) | `unify_conformance` |
| `RuleFiring.lean` | Universal-rule firing is sound modus ponens — a model-sound rule can never conclude a goal outside the model | `rule_firing_conformance` |
| `Trace.lean` (capstone) | A recorded proof trace, read as a certificate, is sound w.r.t. the stratified perfect model: TRUE ⇒ in the model, closed-world FALSE ⇒ not in it | `trace_soundness_conformance` (bridges each model axiom, with exercised-counters) |

Honest scope (stated in `proofs/README.md` and GUARANTEES): the proofs are
model-level plus corpus conformance tests — not one end-to-end machine-checked
pipeline from source text to model. The KR→semantics seam is conformance-gated
(the seam gate), which narrows but does not close that gap.

## On-demand gates

| Recipe | What |
|--------|------|
| `just fuzz-ci [SECS]` | Seeds `fuzz/corpus/` from the shipped `.nibli` files, then runs all three libFuzzer targets (`fuzz_assert`, `fuzz_query`, `fuzz_nibli_kr`) time-boxed; crash/OOM/leak fails. Runs as the parallel `fuzz` CI job. Needs the Nix shell's pinned nightly (`NIBLI_NIGHTLY_BIN`) |
| `just mutants [JOBS]` | Mutation testing over the soundness paths (scope in `.cargo/mutants.toml`); each process capped at 12 GiB so runaway mutants die alone as a *catch*; survivors diffed against `mutants-baseline.txt` — any new survivor fails. ~2.5 h full sweep; use `cargo mutants --in-diff` for incremental changes |
| `just bench-naf` / `just bench-book` | Release-profile timing pins — the only legitimate source for any quoted latency figure |
| `just count-tests` | Derives test-suite counts — the only legitimate source for any quoted test count |

## Reading GUARANTEES.md

The contract document is organized as: Front-End Language, **Soundness**
(Tracks A + B, the seam gate, the mutation baseline, determinism),
Completeness, Negation Policy, Equality Semantics, Predicate Validation,
Integrity Constraints, Resource Limits, Retraction Model, Query Result
Contract, Hypothetical Reasoning, Aggregation, Disclosed Sharp Edges, What the
Engine Cannot Do, Closed Base Vocabulary, and Time and Order. Its core
statement: *if the engine says TRUE, a formal derivation from your asserted
facts and rules exists — and the proof trace shows it.*
