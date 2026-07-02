# Nibli engine — audit remediation backlog (target: 9/10)

Derived from the 2026-07-02 full audit (engine reconciled **7.6/10**; 0 S0 / 0 S1 findings — everything below is drift, hardening, or assurance-coverage work, not bug-fixing). Pending items only; **delete each when it lands** (plain bullets, no numbering — always work the FIRST remaining item). Each item names the rating dimension it moves and its acceptance criterion. Work this file to completion **before** starting `book/TODO.md` — the book items quote the engine state these items produce.

Audit measurements referenced below (machine: Ryzen 9 9950X3D, WSL2, release build unless noted): total passing tests 1,287 (integration ≈127); release `lasna.wasm` = 1,272,722 B; GDPR corpus load <5 ms; load + single lawful-basis query ≈20 ms (WASM path); full Ch-20 pinned sequence ≈330 ms.

## A. Soundness assurance (8.0 → 9): close the un-oracled fragments


## B. Correctness evidence (8.0 → 9)


## C. Test rigor (7.5 → 9)


## D. Code quality (8.0 → 9): fail-closed smells


## E. Production-readiness (6.0 → 8+)


## F. Docs honesty (6.5 → 9)

- **Fix `GUARANTEES.md:11` test counts.** "639+ unit tests and 21 integration tests" → actual (≈1,287 total / ≈127 integration at audit time). Better: drop hard integers for a `just`-derived figure or a floor phrase, and add "re-derive counts" to the pre-commit checklist so it cannot go stale again.
- **Document the disclosed-direction limitations** found by the audit: silent over-arity sumti drop on the unknown-arity fallback path (`compile.rs:182-202`); the tense×NAF sharp edge (`NOT P` is TRUE by CWA when only `Past(P)` is stored); the div-by-zero exact guard (finite operands → decided FALSE, not NonFinite) in the Query Result Contract; the per-occurrence-∃ reading of `lo` under `.e`/`.a`; the `na`/tense relative-scope collapse; the `li`-numbers-never-enumerate sharp edge (a universal over a number-restricted predicate is vacuously TRUE — pinned by `numeric_terms_are_not_universal_domain_members`).
- **CLAUDE.md crate table:** add the four missing workspace members (`nibli-protocol`, `nibli-store`, `nibli-render`, `nibli-import` — or note its removal per the resolve-nibli-import item below).
- **Resolve `nibli-import`.** Zero production dependents; README:319 advertises it as a feature. Either wire an entrypoint (a `nibli` subcommand or `just` recipe) or remove it from the workspace and soften README:319.
- **Delete/relocate stale root files:** `difft.patch` (targets the renamed `parser/`), empty `questions.md`, `triad-trace-improvement.md`, `ideas/crdt-egraph-architecture.lojban`. Decide `jbovlaste-en.xml` (~10 MB): CLAUDE.md says replaced by the lensisku JSON, but `book/tools/verify_book.py` still reads it — either migrate the vocab check to `dictionary-en.json` or keep the file and document why.

## G. Book-enabling (do these LAST — `book/TODO.md` quotes their outputs)

- **Timing pins for the book's numbers.** A release-profile timing test (or `just bench-book` recipe) that measures and prints: GDPR corpus load, the single lawful-basis query, and the full Ch-20 sequence (load + query + retract + 2 re-queries). These become the figures Ch 13/Ch 20 quote (audit: <5 ms / ≈7–20 ms / ≈330 ms) — the book claims "single-digit ms" for the full sequence today, which is wrong.
- **String-pin the corpus transcripts.** Tests asserting the exact printed fact ids (GDPR `#21`/`#24` consent/contract; DDI `#4`/`#10`) and `[Load] N asserted, M skipped` counts for `gdpr.lojban`/`drug-interactions.lojban`, so the book's Ch 20/21 transcripts break loudly on any corpus reorder instead of silently drifting.
- **Build the book-reference conformance gate (`verify-book-refs`).** Tooling only in this phase (it will fail until the book pass): a `book/tools` script + `just` recipe that checks, against the repo: (a) every WIT interface/world/type/function name the book quotes exists in `wit/world.wit`; (b) REPL command tables match gasnu's dispatch/`:help`; (c) quoted struct field lists (`proof-trace`, `UniversalRuleRecord`, session methods) match source; (d) the notation rule catches `(gerku`-style S-expr forms (the current grep only keys on `(Pred`/`(SkolemFn`); (e) no removed commands (`:merge`, `> sentence`). *Done when:* the recipe runs and emits a per-claim report — enabling it in CI is a `book/TODO.md` item after the book is reconciled. This is the structural fix for the audit's core book finding: WIT/struct/REPL drift is currently caught by **no** gate.
