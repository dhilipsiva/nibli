# Nibli engine — audit remediation backlog (target: 9/10)

Derived from the 2026-07-02 full audit (engine reconciled **7.6/10**; 0 S0 / 0 S1 findings — everything below is drift, hardening, or assurance-coverage work, not bug-fixing). Pending items only; **delete each when it lands**. Each item names the rating dimension it moves and its acceptance criterion. Work this file to completion **before** starting `book/TODO.md` — the book items quote the engine state these items produce.

Audit measurements referenced below (machine: Ryzen 9 9950X3D, WSL2, release build unless noted): total passing tests 1,287 (integration ≈127); release `lasna.wasm` = 1,272,722 B; GDPR corpus load <5 ms; load + single lawful-basis query ≈20 ms (WASM path); full Ch-20 pinned sequence ≈330 ms.

## A. Soundness assurance (8.0 → 9): close the un-oracled fragments

1. **Tense-fragment oracle coverage.** The engine treats tense wrappers as opaque fact flavors (exact-match unification), so `Past(P)` can be soundly mapped to a distinct predicate (`p__past`) in both TPTP and ASP translations. Un-skip tense nodes; add curated cases for the wrapper-isolation matrix (audit probe P9). *Done when:* tensed cases run under both oracles, 0 divergences.
2. **Exact-count oracle coverage (ASP).** Map `NumericExact`/`AtLeast` to clingo `#count` aggregates over the regrouped surface atoms. *Done when:* count cases (incl. counts over `du`-merged entities, item 20) are oracle-checked.
3. **Strengthen the `Trace.supported` conformance bridge.** Extend `validate_cert` (`logji/src/tests.rs:1043-1071`) to assert (a) candidate-completeness — every registered rule whose head unifies with the goal appears as a blocked child of a `PredicateNotFound` step — and (b) blocker-definitiveness, matching `Trace.lean:91`'s `Neg` constructor. *Done when:* the conformance test enforces the Lean certificate shape, and item 22's doc change is no longer an overstatement.
4. **Groundness invariant: mechanism, not discipline.** Add a `fact_has_unbound_pattern_var` (exists at `logji/src/reasoning.rs:72`) reject-and-log check at the top of `assert_typed_fact` (`logji/src/rules.rs:837-849`); close or reject the `ce'u`-outside-`ka` free-variable leak in smuni (`smuni/src/semantic/helpers.rs:252-258` — the safety net at `compile.rs:404-414` only closes `da/de/di`); add `debug_assert!` on the combiner dead arm (`reasoning.rs:191`). *Done when:* a stored fact can never contain a PatternVar regardless of upstream discipline.
5. **Parser differential (front-end gap).** Add a camxes/ilmentufa parse-differential: agreement on accept/reject (and gross structure where mappable) over the shipped corpora + a seeded random-sentence batch, for the covered fragment. Skip-if-absent like the other oracles. *Done when:* a `verify-parser` recipe exists and runs in `ci`.
6. **Permanent non-stratified-rejection differential.** Port audit probe P6 into `nibli-verify`: seeded random rule programs checked against an independent ~20-line reference implementation of "no negative edge whose target reaches its source" (written from `proofs/Stratification.lean`'s statement, not from `rules.rs`), plus a KB-uncorrupted-after-rejection replay check. *Done when:* part of `verify-soundness`.

## B. Correctness evidence (8.0 → 9)

7. **Retraction metamorphic harness.** Port audit probe P3: seeded random op sequences (ground / ∃-skolemizing / ∀-rule / `du` / stratified-NAF asserts + retractions); after each retraction the verdict vector over a fixed query battery must equal a fresh KB replaying only surviving ops. *Done when:* ~200 seeded sequences run in `verify-soundness` or `test-engine`.
8. **Three-way determinism gate.** One consolidated verdict corpus run through (a) native `nibli-engine`, (b) gasnu/Wasmtime script mode, (c) browser via `nibli-wasm` headless test — byte-identical verdicts and trace shapes. *Done when:* wired into `ci-wasm` (or a new recipe in `ci-all`).
9. **Release-build depth-boundary pin.** A release-profile test pinning `RESOURCE_EXCEEDED(Depth)` at chain length `max_chain_depth + 1` vs `TRUE` at `max_chain_depth` (debug is too slow — the audit's high-fuel debug run did not terminate; default fuel trips at ~9 deep). *Done when:* the depth/fuel boundary is a pinned test, closing the audit's one unresolved probe leg.

## C. Test rigor (7.5 → 9)

10. **Fuzzing in CI.** Add `cargo-fuzz` (nightly) to `flake.nix`; seed corpora from the shipped `.lojban` files; time-boxed `just fuzz-ci` (e.g. 3 targets × 120 s) in the GitHub workflow — nightly job if too slow for the PR gate. *Done when:* fuzz runs unattended in CI and `cargo fuzz` works inside the Nix shell (it currently is not installed — audit could not run it).
11. **Mutation testing baseline.** Run `cargo-mutants` over the soundness paths (`logji/src/{reasoning,rules,kb}.rs`, `smuni/src/semantic`); triage survivors (kill or document); keep a `just mutants` recipe + baseline count. *Done when:* documented baseline exists and CI-adjacent recipe runs clean.
12. **Missing negative-control tests.** (a) `lo`-under-connective per-occurrence-∃ reading (`smuni .../compile.rs:498-562` — currently untested, undocumented); (b) count-vs-`du` (see item 20); (c) `unify_conformance` case feeding a **non-ground** concrete (must reject — currently the `NoVar c` precondition of `proofs/Unify.lean` is never exercised); (d) flat `try_numeric_comparison` non-finite guard (after item 16).

## D. Code quality (8.0 → 9): fail-closed smells

13. **Bounds-checked accessors on the public `compile_from_gerna_ast` path** (`smuni/.../compile.rs:110,469,572`, `helpers.rs:166,195`, `selbri.rs:180`) — return `Result` instead of raw slice indexing (panics on a hand-built/corrupt `AstBuffer`).
14. **f64 overflow guard at the `li` parse boundary** (`gerna/src/grammar/sumti.rs:232-244`) — fail closed like the u32 quantifier path instead of relying on downstream NonFinite catches.
15. **Replace the latent `_ => unreachable!()`** at `gerna/src/lib.rs:451` with an explicit `Lo | Le` match (compile error on producer-set widening).
16. **Mirror the non-finite guard in `try_numeric_comparison`** (`logji/src/compute.rs:29-37`) for flat-path consistency with the event-decomposed path.

## E. Production-readiness (6.0 → 8+)

17. **`RedbFactStore` schema guard.** Add a `SCHEMA_VERSION` check and surface postcard decode failures as `StoreError` (`nibli-store/src/typed_store.rs:73-75`), matching sibling `NibliStore` (`lib.rs:174-193`). Today a silent drop is masked only by the caller's clear+rebuild.
18. **Propagate persistence-write errors** (`gasnu/src/main.rs:374,400`; `typed_store.rs:148-172`) — no more `let _ =` on insert/commit; log at minimum, surface ideally.
19. **Ship strict mode.** Opt-in flag (env var + REPL command) that **rejects** arity mismatches and integrity-constraint violations instead of warn-and-insert (GUARANTEES.md calls strict mode "future work" — make it present-tense).
20. **Decide and implement count/witness semantics × `du`.** Audit finding: `?? da broda` over `broda(adam)`, `broda(karl)`, `adam du karl` returns 4 binding tuples (2 event-skolems × 2 names) for one entity. Either collapse `du`-equivalence classes + dedupe event-skolem multiplicity in `??`/`count_witnesses`, or explicitly define tuple semantics — in both cases document in GUARANTEES §Aggregation and pin with the item-12b negative-control test.

## F. Docs honesty (6.5 → 9)

21. **Fix `GUARANTEES.md:11` test counts.** "639+ unit tests and 21 integration tests" → actual (≈1,287 total / ≈127 integration at audit time). Better: drop hard integers for a `just`-derived figure or a floor phrase, and add "re-derive counts" to the pre-commit checklist so it cannot go stale again.
22. **Align `GUARANTEES.md:28`** ("load-bearing, not merely proof-conditional") to `proofs/README.md:176-177`'s qualified phrasing on the `supported` axiom — or land item 3 first and keep the strong sentence truthfully.
23. **Document the disclosed-direction limitations** found by the audit: silent over-arity sumti drop on the unknown-arity fallback path (`compile.rs:182-202`); the tense×NAF sharp edge (`NOT P` is TRUE by CWA when only `Past(P)` is stored); the div-by-zero exact guard (finite operands → decided FALSE, not NonFinite) in the Query Result Contract; the per-occurrence-∃ reading of `lo` under `.e`/`.a`; the `na`/tense relative-scope collapse.
24. **CLAUDE.md crate table:** add the four missing workspace members (`nibli-protocol`, `nibli-store`, `nibli-render`, `nibli-import` — or note its removal per item 25).
25. **Resolve `nibli-import`.** Zero production dependents; README:319 advertises it as a feature. Either wire an entrypoint (a `nibli` subcommand or `just` recipe) or remove it from the workspace and soften README:319.
26. **Delete/relocate stale root files:** `difft.patch` (targets the renamed `parser/`), empty `questions.md`, `triad-trace-improvement.md`, `ideas/crdt-egraph-architecture.lojban`. Decide `jbovlaste-en.xml` (~10 MB): CLAUDE.md says replaced by the lensisku JSON, but `book/tools/verify_book.py` still reads it — either migrate the vocab check to `dictionary-en.json` or keep the file and document why.

## G. Book-enabling (do these LAST — `book/TODO.md` quotes their outputs)

27. **Timing pins for the book's numbers.** A release-profile timing test (or `just bench-book` recipe) that measures and prints: GDPR corpus load, the single lawful-basis query, and the full Ch-20 sequence (load + query + retract + 2 re-queries). These become the figures Ch 13/Ch 20 quote (audit: <5 ms / ≈7–20 ms / ≈330 ms) — the book claims "single-digit ms" for the full sequence today, which is wrong.
28. **String-pin the corpus transcripts.** Tests asserting the exact printed fact ids (GDPR `#21`/`#24` consent/contract; DDI `#4`/`#10`) and `[Load] N asserted, M skipped` counts for `gdpr.lojban`/`drug-interactions.lojban`, so the book's Ch 20/21 transcripts break loudly on any corpus reorder instead of silently drifting.
29. **Build the book-reference conformance gate (`verify-book-refs`).** Tooling only in this phase (it will fail until the book pass): a `book/tools` script + `just` recipe that checks, against the repo: (a) every WIT interface/world/type/function name the book quotes exists in `wit/world.wit`; (b) REPL command tables match gasnu's dispatch/`:help`; (c) quoted struct field lists (`proof-trace`, `UniversalRuleRecord`, session methods) match source; (d) the notation rule catches `(gerku`-style S-expr forms (the current grep only keys on `(Pred`/`(SkolemFn`); (e) no removed commands (`:merge`, `> sentence`). *Done when:* the recipe runs and emits a per-claim report — enabling it in CI is a `book/TODO.md` item after the book is reconciled. This is the structural fix for the audit's core book finding: WIT/struct/REPL drift is currently caught by **no** gate.
