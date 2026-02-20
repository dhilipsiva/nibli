### Phase 2: The Master Execution Roadmap

Here is the comprehensive, radically prioritized sequence of improvements. This order minimizes rework and attacks the highest-risk structural bottlenecks first.

#### Tier 1: The "Go/No-Go" Checks & Trap Removal (Immediate)

Before writing another line of Lojban grammar, we must ensure the engine won't panic or fail to compile to the target architecture.

1. **Verify Egglog WASI P2 Compilation (Claude I15):** `egglog` relies on `rayon` (threading), `std::time`, and file I/O. These often fail or trap under strict WASI Preview 2 constraints. Run the component build for the `reasoning` crate immediately to verify if a fork or alternative engine is required.
2. **Remove WASM Traps (Claude B4 & B5):** * Degrade the `sa` token in `parser/preprocessor.rs` to a safe warning and a `si` (single-word) erasure.
* Remove the `unimplemented!()` panic in `semantic.rs` for `ForAll`/`Exists`. Return an `Err` or a stub string instead.



#### Tier 2: The Zero-Copy Architectural Overhaul (Critical Impact)

We must fix the pipeline's memory and serialization fallacies before expanding the grammar.
3. **Fuse the Pipeline (Claude I12 / My Review):** Stop using the native `runner` as a data mule. Use `wac compose` (or `cargo-component`) to statically link `parser`, `semantics`, and `reasoning` into a single `engine-pipeline.wasm`. Completely delete the `map_buffer_to_semantics` boilerplate.
4. **Direct-to-Buffer Parsing (My Review):** Discard the intermediate heap allocations in `parser/ast.rs`. Rewrite `grammar.rs` to write integers directly into the `wit::AstBuffer` passed by the host.
5. **Eliminate String Serialization (My Review):** Rewrite the `reasoning` interface to accept the binary `LogicalForm` (or an array of `u32` integer IDs). Use `egglog`'s programmatic Rust API (`egraph.add_expr`) instead of forcing it to re-parse S-expression strings at runtime.

#### Tier 3: Core Reasoning & Semantic Fixes (High Priority)

Once the plumbing is zero-copy and stable, fix the logic mapping.
6. **Shatter the Arity Wall (Claude I9 / My Review):** Replace the hardcoded `Pred1`...`Pred5` in the FOL schema with a variadic structure (e.g., linked lists `Cons(Term, Nil)`) to support Lojban's infinite BAI modal extensions.
7. **Batch E-Graph Saturation (Claude I8):** Remove `(run 10)` from the `assert_fact` loop. Expose a `saturate()` function to the host, or run it only immediately before `query_entailment` to drastically save CPU cycles.
8. **Quantified lo-descriptions (Claude I7):** Update the semantic compiler to output `Exists(x, And(gerku(x), ...))` for `lo` descriptors instead of treating them as constants.

#### Tier 4: Grammar Expansion & Domain Rules (Standard Feature Work)

With a robust engine, you can map the rest of the Lojban specification.
9. **Implement `nom` / Deterministic Parsing (Claude I6):** Replace the single-pass loop with a robust parser capable of handling relative clauses (`poi`/`noi`), connectives (`je`/`ja`), and sumti raising (`be`).
10. **Lojban Rewrite Rules (Claude I10 & I11):** Add the specific `egglog` rewrite rules for `se`/`te`/`ve`/`xe` place-structure permutations.
11. **Preserve Tanru Modifiers (Claude I16):** Ensure `sutra gerku` is mapped as an intersection (`And`) of two predicates, rather than dropping the modifier entirely.

---

Would you like me to rewrite `semantics/src/semantic.rs` to apply the Phase 1 compiler fixes right now, so we can run a clean `cargo component build` and verify `egglog`'s compatibility?
