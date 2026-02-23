Cross-referencing the todo against the actual codebase, several items listed as "not started" are actually **already implemented**, and the todo is stale. Here's what's genuinely still open:

## Bugs (producing wrong results now)

1. **Multi-sentence root tracking** — `Flattener::flatten` only pushes the last sentence as a root. Multi-sentence input loses all but the final sentence.
2. **Temporal node semantics in reasoning** — `PastNode/PresentNode/FutureNode` all map to `(Not ...)` in both `reconstruct_sexp_with_subs` and `check_formula_holds`. Tense-marked assertions are silently corrupted.
3. **`inject_variable` still fragile (#7)** — It now scans for the first `Unspecified` anywhere (better than position-0-only), but there's no `ke'a` explicit pronoun support. Relative clauses where all slots are filled will fail silently.

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

## Items the todo lists as "not started" but ARE implemented

- **`nu` abstraction (#1)** — Fully in: parser handles `nu...kei`, AST has `Selbri::Abstraction`, semantics reifies as Davidsonian event, WIT has `abstraction(u32)`.
- **Tense markers (#2)** — Structurally complete: parser has `try_parse_tense` for `pu/ca/ba`, semantics wraps in `Past/Present/Future`. Broken in reasoning (bug #2 above), but not "not started."
- **Tanru semantics (#3)** — Fixed. Modifier gets only `[args[0], Unspecified, ...]`, not the full vector.
- **`bevri` arity (#13)** — Already corrected to 5 in `CORE_GISMU_ARITIES`.
- **`ast-buffer` roots (#8)** — `roots: list<u32>` already exists in the WIT definition and is populated.

---

**Total: 16 open items** — 3 correctness bugs, 4 missing capabilities, 4 architectural debt, 5 long-term research items. Bugs #1 and #2 are the most urgent since they silently produce wrong output on valid input that the engine already claims to support.
