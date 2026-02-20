**2. Direct-to-Buffer Parsing**

* **The Flaw:** While the *WASM boundary* is zero-copy, your `parser/grammar.rs` and `parser/ast.rs` are still allocating thousands of intermediate `Box<Sumti>` and `String` objects on the heap, only to flatten them into the `AstBuffer` and throw the tree away.
* **The Fix:** We must rewrite the parser to write integer IDs directly into the `wit::AstBuffer` as it reads the tokens, achieving absolute zero-allocation parsing.

**3. Batch E-Graph Saturation**

* **The Flaw:** In `reasoning/src/lib.rs`, we are calling `(run 10)` inside the `assert_fact` loop. This forces `egglog` to execute equality saturation every time a single fact is loaded, which will cripple startup time for large knowledge bases.
* **The Fix:** We need to move the `(run 10)` saturation step to occur only when `query_entailment` is called.

**4. Implementing `nom` & Deterministic Parsing

* **The Flaw:** Your recursive descent parser in `grammar.rs` is still a flat, single-pass loop that fails on complex relative clauses, sumti raising (`be`/`bei`), and logical connectives (`je`/`ja`).
* **The Fix:** Replace the hand-rolled loop with strict parser combinators.

**5. Long-Term Semantics**

* Non-monotonic reasoning (handling negation and belief retraction).
* Proper scoping for all other Lojban descriptors (`le`, `la`, `ro`, `su'o`).
* Neo-Davidsonian Event Semantics (reifying events so we can reason about time and causality: `∃e. prami(e) ∧ agent(e, mi) ∧ theme(e, do)`).
