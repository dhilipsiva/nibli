#### I6. Implement recursive descent parser with `nom`

The current parser is a flat single-pass loop that only handles `[sumti*] cu? selbri [sumti*]`. Everything downstream is bottlenecked by this. Priority constructs to implement, in order:

1. **Sentence separator `.i`** — enables multi-sentence input
2. **Place tags `fa`/`fe`/`fi`/`fo`/`fu`** — explicit argument positions
3. **Negation `na`/`naku`** — required for reasoning to be non-trivial
4. **Relative clauses `poi`/`noi`** — restrictive vs. non-restrictive (maps to conjunction vs. apposition in FOL)
5. **Sumti raising `be`/`bei`** — arguments inside selbri
6. **Grouping `ke`/`ke'e`** — tanru structure
7. **Connectives `je`/`ja`/`jo`/`ju`** — logical connectives map directly to FOL ∧/∨/↔/⊕
8. **Terminators `ku`/`vau`/`kei`** — proper scope closure

You already have `nom` in deps. Use it. `nom` is a better fit than `pest` for this — Lojban's grammar is context-sensitive in places (metalinguistic operators, elidable terminators), which PEG handles poorly.

#### I7. Handle `lo`-descriptions as quantified forms in semantics

This is the single biggest semantic gap. Currently:

```
"mi prami lo gerku" → prami(mi, Desc("gerku"))
```

Correct FOL:

```
"mi prami lo gerku" → ∃x. gerku(x) ∧ prami(mi, x)
```

Your IR already has `Exists` and `And` constructors. Use them. The `SemanticCompiler` needs to generate fresh variables (e.g., a counter-based `x0`, `x1`, ...) and wrap predicates with existential quantifiers when processing `Sumti::Description`.

---

### Phase 3: Reasoning improvements

#### I8. Batch `(run N)` instead of per-assertion

Move `(run N)` out of `assert_fact` and into a separate `saturate()` call, or invoke it only before queries:

```rust
fn query_entailment(sexp: String) -> bool {
    let mut egraph = get_egraph().lock().unwrap();
    egraph.parse_and_run_program(None, "(run 100)").ok();  // saturate before checking
    let command = format!("(check (IsTrue {}))", sexp);
    // ...
}
```

#### I9. Replace `Pred1`..`Pred5` with variadic representation

The arity-indexed constructors don't scale to BAI-extended arities (which you've explicitly said you want to preserve by not truncating args). The `.clamp(1, 5)` in `to_sexp` silently drops data for arity > 5.

Options:
- Variadic S-expression: `(Pred "klama" (Args (Const "mi") (Const "do") (Zoe) (Zoe) (Zoe)))`
- Keep `Pred1`..`Pred5` but add `PredN String (Vec Term)` as overflow

#### I10. Add Lojban-specific rewrite rules to egglog

The current rules (commutativity of `And`, double-negation elimination) are generic FOL. Lojban has productive transformations that map directly to e-graph rewrites:

```scheme
;; se-conversion: swap x1 and x2
(rewrite (IsTrue (Pred2 rel a b)) (IsTrue (Pred2 (se rel) b a)))

;; te-conversion: swap x1 and x3
(rewrite (IsTrue (Pred3 rel a b c)) (IsTrue (Pred3 (te rel) c b a)))
```

These would enable non-trivial entailment queries: assert `mi prami do`, query `do se prami mi` → `true`.

#### I11. Add `se`/`te`/`ve`/`xe` conversion support (parser + semantics + reasoning)

This is a cross-cutting feature:
- **Parser**: Recognize `se`/`te`/`ve`/`xe` as selbri modifiers
- **Semantics**: Permute argument positions in the generated `LogicalForm`
- **Reasoning**: Add rewrite rules (I10) for bidirectional inference

---

### Phase 4: Architecture improvements

#### I12. Eliminate `map_buffer_to_semantics` in runner

The 50-line identity mapping between parser and semantics types exists only because `bindgen!` generates separate types per world. Options:

- **Best:** Use `wasm-tools compose` to compose the three `.wasm` components into a single `engine-pipeline` component (your WIT already defines this world). The runner then instantiates one component.
- **Good:** Write a macro that generates `From` impls between the structurally identical types.
- **Minimum:** At least add a comment explaining why this exists so it doesn't look like a mistake.

#### I13. Separate REPL commands for assert vs. query [runner/main.rs]

Currently, every input is parsed → compiled → asserted → trivially queried (same fact). Implement command prefixes:

```
lojban> mi prami do          # default: assert
lojban> :query do se prami mi   # query entailment
lojban> :facts                  # dump knowledge base
lojban> :clear                  # reset e-graph
```

#### I14. Consider separate `Store` instances per component

Currently all three WASM components share one Wasmtime `Store` (one linear memory). A bug in the parser can corrupt reasoning state. For production sandboxing, use separate stores. The tradeoff is negligible — you're already serializing across the WIT canonical ABI.

#### I15. Verify egglog compiles to `wasm32-wasip2`

egglog's dependency tree includes `log`, `hashbrown`, symbol tables, and a parser. Some of these may use `std::time` or platform-specific features that fail under WASI P2. If you haven't done a clean `cargo component build --release --target wasm32-wasip2 -p reasoning`, this is a likely blocker. Test early.

---

### Phase 5: Long-term semantic completeness

#### I16. Tanru modifier preservation

`Selbri::Tanru` currently extracts only the head's string, discarding the modifier. `sutra gerku` becomes just `gerku`. The modifier relationship should be represented in the IR, e.g.:

```scheme
(And (IsTrue (Pred1 "gerku" x)) (IsTrue (Pred1 "sutra" x)))
```

#### I17. Non-monotonic reasoning / negation

egglog is inherently monotonic. You can add equalities, never remove them. This blocks:
- `na` (bridi negation)
- `naku` (logical negation)
- `da'i` (hypothetical/counterfactual)
- Belief revision / retraction

Long-term options: fork the e-graph per hypothetical context, layer a Datalog engine with stratified negation (ascent, crepe, or Scallop as originally planned) alongside egglog, or implement a truth-maintenance system (TMS) on top.

#### I18. Proper quantifier scope for `lo`/`le`/`la`

Beyond I7 (basic existential for `lo`), Lojban has a rich quantifier system:
- `lo` — veridical description (∃)
- `le` — non-veridical reference (specific referent, not necessarily satisfying the predicate)
- `la` — named entity (constant)
- `ro` — universal (∀)
- `su'o` — existential with cardinality
- `pa`, `re`, `ci`... — numeric quantifiers

Each requires different FOL translation. This is where the semantics crate becomes genuinely interesting.

#### I19. Event semantics (neo-Davidsonian)

The current IR uses flat predicates: `prami(mi, do)`. The standard approach in formal semantics is to reify events:

```
∃e. prami(e) ∧ agent(e, mi) ∧ theme(e, do)
```

This enables temporal reasoning, adverbial modification, and causality chains — all expressible in Lojban via tense/aspect system (`pu`/`ca`/`ba`, `za'o`/`co'a`, etc.). This is a fundamental architectural shift but the correct long-term target for a neuro-symbolic engine.



---


### B4. `sa` (EraseClass) panics at runtime [parser/preprocessor.rs]

```rust
LojbanToken::EraseClass => {
    unimplemented!("'sa' (EraseClass) resolution requires...");
}
```

Any Lojban input containing `sa` causes a WASM trap, killing the pipeline. Same for valid Lojban text that happens to contain `sa` as a substring matched by the lexer.

**Fix:** Replace with a no-op that logs a warning, or return `Err`:

```rust
LojbanToken::EraseClass => {
    // V1: treat as no-op, log warning
    eprintln!("Warning: 'sa' erasure not yet supported, ignoring");
}
```

---

### B5. `to_sexp` panics on `ForAll`/`Exists` [semantics/semantic.rs]

```rust
_ => unimplemented!("Other forms deferred for V1 MVP"),
```

If any code path ever constructs a quantified `LogicalForm` and serializes it, the WASM component traps. The variants exist in the IR enum but can't be serialized.

**Fix:** Either implement stub serialization or remove the variants from the enum until supported:

```rust
LogicalForm::ForAll(var, body) => {
    format!("(ForAll \"{}\" {})", self.interner.resolve(var), self.to_sexp(body))
}
LogicalForm::Exists(var, body) => {
    format!("(Exists \"{}\" {})", self.interner.resolve(var), self.to_sexp(body))
}
```
