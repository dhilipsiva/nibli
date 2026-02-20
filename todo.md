**1. Shattering the Arity Wall (Claude I9 / My Review Target)**

* **The Flaw:** Take a look at `reasoning/src/lib.rs`. We are still hardcoding `(Pred1 ...)` through `(Pred5 ...)` in the `egglog` schema. If a user inputs a sentence with a BAI modal tag (a 6th argument, e.g., adding a time or location), the reasoning component will instantly trap.
* **The Fix:** We must rewrite the FOL schema in `egglog` to use a recursive linked list (e.g., `(Cons Term (Cons Term Nil))`) to support infinite arities mathematically.

**2. Direct-to-Buffer Parsing (My Review Target)**

* **The Flaw:** While the *WASM boundary* is zero-copy, your `parser/grammar.rs` and `parser/ast.rs` are still allocating thousands of intermediate `Box<Sumti>` and `String` objects on the heap, only to flatten them into the `AstBuffer` and throw the tree away.
* **The Fix:** We must rewrite the parser to write integer IDs directly into the `wit::AstBuffer` as it reads the tokens, achieving absolute zero-allocation parsing.

**3. Batch E-Graph Saturation (Claude I8)**

* **The Flaw:** In `reasoning/src/lib.rs`, we are calling `(run 10)` inside the `assert_fact` loop. This forces `egglog` to execute equality saturation every time a single fact is loaded, which will cripple startup time for large knowledge bases.
* **The Fix:** We need to move the `(run 10)` saturation step to occur only when `query_entailment` is called.

**4. Implementing `nom` & Deterministic Parsing (Claude I6)**

* **The Flaw:** Your recursive descent parser in `grammar.rs` is still a flat, single-pass loop that fails on complex relative clauses, sumti raising (`be`/`bei`), and logical connectives (`je`/`ja`).
* **The Fix:** Replace the hand-rolled loop with strict parser combinators.

**5. Long-Term Semantics (Claude I17, I18, I19)**

* Non-monotonic reasoning (handling negation and belief retraction).
* Proper scoping for all other Lojban descriptors (`le`, `la`, `ro`, `su'o`).
* Neo-Davidsonian Event Semantics (reifying events so we can reason about time and causality: `∃e. prami(e) ∧ agent(e, mi) ∧ theme(e, do)`).
