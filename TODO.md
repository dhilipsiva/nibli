# Nibli engine — audit remediation backlog (target: 9/10)

Derived from the 2026-07-02 full audit (engine reconciled **7.6/10**; 0 S0 / 0 S1 findings — everything below is drift, hardening, or assurance-coverage work, not bug-fixing). Pending items only; **delete each when it lands** (plain bullets, no numbering — always work the FIRST remaining item). Each item names the rating dimension it moves and its acceptance criterion. Work this file to completion **before** starting `book/TODO.md` — the book items quote the engine state these items produce.

Audit measurements referenced below (machine: Ryzen 9 9950X3D, WSL2, release build unless noted): total passing tests 1,287 (integration ≈127); release `lasna.wasm` = 1,272,722 B; GDPR corpus load <5 ms; load + single lawful-basis query ≈20 ms (WASM path); full Ch-20 pinned sequence ≈330 ms.

## A. Soundness assurance (8.0 → 9): close the un-oracled fragments


## B. Correctness evidence (8.0 → 9)


## C. Test rigor (7.5 → 9)


## D. Code quality (8.0 → 9): fail-closed smells


## E. Production-readiness (6.0 → 8+)


## F. Docs honesty (6.5 → 9)

## G. Book-enabling (do these LAST — `book/TODO.md` quotes their outputs)

- **Build the book-reference conformance gate (`verify-book-refs`).** Tooling only in this phase (it will fail until the book pass): a `book/tools` script + `just` recipe that checks, against the repo: (a) every WIT interface/world/type/function name the book quotes exists in `wit/world.wit`; (b) REPL command tables match gasnu's dispatch/`:help`; (c) quoted struct field lists (`proof-trace`, `UniversalRuleRecord`, session methods) match source; (d) the notation rule catches `(gerku`-style S-expr forms (the current grep only keys on `(Pred`/`(SkolemFn`); (e) no removed commands (`:merge`, `> sentence`). *Done when:* the recipe runs and emits a per-claim report — enabling it in CI is a `book/TODO.md` item after the book is reconciled. This is the structural fix for the audit's core book finding: WIT/struct/REPL drift is currently caught by **no** gate.
