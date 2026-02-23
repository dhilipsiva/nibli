## Missing Capabilities

4. **Causal connectives (#5)** — `ri'a/mu'i/ni'i` completely absent from parser/semantics.
5. **`ganai...gi` implication (#6)** — No bare conditional without a quantifier.
6. **Numerical comparison predicates (#4, partial)** — Parser handles `li` + PA digits and `LogicalTerm::Number` exists in the IR/WIT, but the reasoning schema has zero comparison predicates. Numbers pass through structurally but can't be reasoned about.
7. **`sa` proper implementation (#14)** — Still degraded to single-word erase.

## Architectural Debt

8. **wasip1/wasip2 misalignment (#9)** — Build targets wasip1, flake says wasip2.
9. **`reconstruct_sexp` duplication (#10)** — Identical logic in orchestrator and reasoning.
10. **`ast-types` interface naming (#11)** — `logical-term`/`logic-node` still in `ast-types`.
11. **Global state non-resettability (#12)** — No `:reset` command, must restart process.

## Long-term (acknowledged as future work)

12. **Event semantics / Neo-Davidsonian (#15)**
13. **Non-monotonic reasoning / belief revision (#16)**
14. **Description term opacity (#17)**
15. **E-Graph cycle detection (#18)**
16. **Conjunction introduction rule (#19)**
