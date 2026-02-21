Here's the cross-reference of what's done, what remains, and the final prioritized list.

## Status Audit

**Phase 1 (Semantics bugs)** — **ALL DONE.** 1.1–1.7 fully addressed. `bridi.negated`, `Selbri::Negated`, `Sumti::Tagged` (positional insertion), `Sumti::Restricted` (rel clauses), `WithArgs`, `Connected`, `Grouped` — all handled.

**Phase 2 (Type system)** — **ALL DONE.** `Not`/`Or`/`Exists`/`ForAll` in IR, WIT, flatten, reconstruct.

**Phase 3 (Reasoning)** — **ALL DONE.** Saturation, conjunction elimination, modus ponens (both forms), disjunctive syllogism, De Morgan's, double negation, Skolemization, Herbrand instantiation.

**Phase 4 (Hygiene)** — **PARTIALLY DONE.**
- 4.1 ✅ Query routing moved to runner, WIT exports split
- 4.2 ❌ `reconstruct_sexp` still duplicated (orchestrator + reasoning)
- 4.3 ✅ Functionally solved (separate exports with typed returns)
- 4.4 ❌ `ast-buffer` still mixes top-level sentences with rel clause bodies
- 4.5 ❌ `logical-term`/`logic-node` still in `ast-types` interface
- 4.6 ❌ wasip1/wasip2 misalignment (build targets wasip1, flake says wasip2)

**Phase 5 (Parser hardening)** — **MOSTLY DONE.**
- 5.1 ✅ MAX_DEPTH=64 with enter/leave
- 5.2 ✅ Place tag backtracking with save/restore
- 5.3 ❌ `bevri` still listed as arity 4 (CLL says 5)
- 5.4 ⚠️ `sa` degraded to `si` with warning — documented but not fixed

**Phase 6 (Research)** — 6.2 partially done (ro lo/ro le universal quantification added). 6.1, 6.3 untouched.

**Phase 7–11 (Roadmap)** — Phase 10 (poi/noi) is already done. Everything else untouched.

---

## Final Prioritized Action List

Ranked by impact on application surface area and reasoning capability.

### Tier 1 — Capability Blockers (without these, the engine can't represent most real-world knowledge)

**1. `nu` abstraction (propositions as arguments)**
Status: Not started. Parser has `"nu"` in `looks_like_selbri_na` lookahead — dead code anticipating this.
Impact: Blocks *every* domain. You cannot express beliefs ("I know that X"), causation ("the fact that A causes B"), evidence relations, desires, commands, or any higher-order claim. Every predicate is limited to entity arguments. This single feature probably doubles structural diversity of representable knowledge.
Scope: Parser (new AST node `Abstraction`), grammar (parse `nu ... kei`), semantics (reify bridi as entity term), WIT (new sumti variant or selbri variant), reasoning (handle reified propositions).

**2. Tense markers (`pu`/`ca`/`ba`)**
Status: Not started.
Impact: All assertions are timeless. Can't express "X happened before Y", "X is currently true", "X will occur". Blocks temporal reasoning — your evolutionary biology target domain is fundamentally about temporal ordering of events.
Scope: Small. Parser (three cmavo → wrap selbri). Semantics (emit `Past(P)`/`Present(P)`/`Future(P)` wrappers). No reasoning changes needed initially — just structural markers that become queryable.

**3. Tanru semantics fix**
Status: Current implementation is *wrong*, not missing. `sutra gerku` → `sutra(x,zo'e) ∧ gerku(x,zo'e)` shares the full argument vector between modifier and head. This generates false entailments. "fast dog" doesn't mean "is-fast AND is-a-dog with the same x2".
Impact: Every tanru in your training data produces semantically incorrect FOL. This is the most dangerous current bug because it silently produces wrong results rather than failing.
Fix: Modifier should apply only x1 (the shared referent). Change `apply_selbri` for `Tanru` to give the modifier `[args[0], Unspecified, Unspecified, ...]` instead of the full args vector. Alternatively, use a tanru-specific predicate: `tanru_mod(sutra, gerku, x)`.

### Tier 2 — Reasoning Depth (without these, inference chains are too shallow)

**4. Numerical predicates and comparisons**
Status: Not started.
Impact: Blocks every quantitative domain. "HbA1c > 7.0", "dN/dS > 1", "temperature above threshold". No numbers, no quantitative science.
Scope: Extend `LogicalTerm` with numeric variant, add comparison predicates to the reasoning schema, parser support for Lojban number system (`li` + PA cmavo).

**5. Causal connectives (`ri'a`/`mu'i`/`ni'i`)**
Status: Not started. Depends on `nu` (#1) since causes/motivations operate on propositions.
Impact: Can't distinguish correlation from causation from logical entailment. Three distinct modalities that Lojban gives you for free. Critical for scientific reasoning.
Scope: Parser (new binary connective cmavo), semantics (map to typed implication/causation predicates), reasoning (optional new inference rules for causal transitivity).

**6. `ganai...gi` bare implication**
Status: Not started. Currently universals encode `∀x.(A→B)` as `∀x.(¬A∨B)`, but there's no way to assert a bare conditional without a quantifier.
Impact: "If it rains, the ground is wet" has no direct representation. Small diff, significant expressiveness gap.
Scope: Parser (recognize `ganai` ... `gi` pattern), semantics (emit `Implies` or `Or(Not(A), B)`).

**7. `inject_variable` fragility**
Status: Known limitation (documented in limitations.md). Only replaces `Unspecified` in position 0 of a predicate.
Impact: Relative clauses where the bound variable isn't x1 produce wrong results. "lo gerku poi mi nelci" (the dog that I like) — `nelci` has the variable in x2, not x1. The injector misses it.
Fix: Either use `ke'a` explicit pronoun support, or scan all `Unspecified` positions (or at minimum, the first one that matches the expected binding site based on the relative clause's structure).

### Tier 3 — Architectural Integrity (not capability blockers, but accumulating debt)

**8. `ast-buffer` sentence mixing (todo 4.4)**
Top-level sentences and rel clause body sentences are in the same flat array with no way to distinguish them. When you add `nu` abstraction, this gets worse — abstracted bridi will also be in the mix. Add `roots: list<u32>` to `ast-buffer` mirroring what `logic-buffer` already has.

**9. wasip1/wasip2 alignment (todo 4.6)**
Build targets `wasm32-wasip1`, flake shellHook says "wasip2 is active". Pick one. If you're using `cargo-component` and WAC fusion, wasip2 is the correct target. The current setup works by accident because cargo-component handles the translation, but it's a ticking bomb for toolchain updates.

**10. `reconstruct_sexp` duplication (todo 4.2)**
Identical logic in orchestrator and reasoning. When you add new `LogicNode` variants (and you will, for `nu`, tense, causation), you'll need to update both. Extract to a shared crate or have one component own the debug-print function.

**11. `ast-types` interface naming (todo 4.5)**
`logical-term` and `logic-node` don't belong in `ast-types`. This is confusing and will get worse as types proliferate. Split into `ast-types` and `logic-types`.

**12. Global state non-resettability**
The reasoning engine's `OnceLock<Mutex<EGraph>>` plus entity set plus universal templates plus Skolem counter are all irrecoverable. No `:reset` command. For REPL-driven development this is painful — you have to restart the process to clear state. Add a `reset` export to the reasoning WIT interface that reinitializes all globals.

**13. `bevri` arity (todo 5.3)**
Listed as 4-place in `CORE_GISMU_ARITIES`. CLL defines it as 5-place. One-line fix.

### Tier 4 — Long-term (not blocking current phases)

**14. `sa` proper implementation** — Requires selma'o classification. Low priority since `sa` is rarely used in training data.

**15. Event semantics (Neo-Davidsonian)** — The correct long-term foundation. Every predication becomes `∃e. P(e) ∧ agent(e, x) ∧ ...`. This changes everything. Don't touch until Tiers 1–2 are solid.

**16. Non-monotonic reasoning / belief revision** — Fact retraction. Fundamentally changes the egglog model. Research-grade problem.

**17. Description term opacity** — `le gerku` becomes `(Desc "gerku")` which the reasoner can't decompose. For now this is acceptable (specific referents vs. quantified entities is a genuine semantic distinction), but eventually you'll want the reasoner to know that `le gerku` refers to something that satisfies `gerku(x)`.

**18. E-Graph cycle detection / occurs check** — The `saturate` with fallback to `run 100` works but isn't principled. Pathological inputs can diverge. Low priority unless you're feeding untrusted input.

**19. Conjunction introduction rule** — Conspicuously absent from the reasoning schema. You have conjunction *elimination* (`And(A,B) → A, B`) but not introduction (`A, B → And(A,B)`). This is likely intentional (introduction is expensive — quadratic blowup), but it means the reasoner can never *construct* conjunctions, only decompose them. If you ever need to query "is A∧B true?" where A and B were asserted separately, the Rust-side `check_formula_holds` handles it via recursive decomposition. But egglog-internal rules can't chain through constructed conjunctions.

---

## Recommended Execution Order

```
Immediate:  #3 (tanru fix — it's generating wrong results NOW)
            #13 (bevri — one line)
            
Phase 7:    #1 (nu) + #2 (tense) — unlock training data
            #7 (inject_variable fix — wrong results for rel clauses)
            
Phase 8:    #4 (numerical predicates)
            #6 (ganai/gi implication)
            #8 (ast-buffer roots)
            
Phase 9:    #5 (causal connectives — depends on #1)
            #9, #10, #11 (architectural cleanup batch)
            #12 (reset command)
            
Later:      #14–#19 as needed
```

Items #3 and #7 are correctness bugs — they produce wrong output on valid input. Everything else is missing capability. Fix correctness first.
