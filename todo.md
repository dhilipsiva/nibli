Would you like to refactor world.wit and ast.rs to support the recursive Sentence structure required to parse ganai...gi, or must we fix the mathematically unsound OrNode evaluation in the reasoning crate first so the logic actually holds water?


### Tier 1: Critical Systemic Failures (Security & Commercial Blockers)

* **[NEW] WASM Unbounded Execution (DoS Vulnerability):** Add Wasmtime fuel/epoch interruption limits and transition to asynchronous execution via `tokio`. Synchronous execution without bounds guarantees host thread starvation on pathological logic queries.
* **[NEW] WASI Ephemerality & State Persistence:** Replace the anti-pattern of `OnceLock<Mutex<...>>` in the reasoning component. Utilize WASI Resources to hoist the knowledge base state to the host level. This allows for multi-tenant database persistence and directly resolves the issue where global state cannot be reset without restarting the process.
* **[NEW] Opaque Error Boundaries:** Strip out stringified error passing. Implement strict WIT error variants (e.g., `SyntaxError(position: u32)`) to enable programmatic recovery loops by upstream LLM agents.
* **[NEW] WASI Capability Sandboxing:** Remove the blanket `inherit_stdio()` from the host environment to enforce the principle of least privilege.

### Tier 2: Algorithmic & Memory Bottlenecks

* **[NEW] AST Double-Allocation Churn:** Eliminate the recursive heap `Box` usage across the parser and semantics components. Write directly into the flat, index-based arrays (`AstBuffer` / `LogicBuffer`) or implement an arena allocator like `bumpalo`.
* **[NEW]  String Allocations:** Refactor the left-fold `format!` loop in `reconstruct_sexp` to use pre-allocated `String::with_capacity()` buffers.
* **wasip1/wasip2 misalignment (#9):** The build targets wasip1, but the flake specifies wasip2.
* **`reconstruct_sexp` duplication (#10):** Identical logic exists in both the orchestrator and reasoning crates.
* **`ast-types` interface naming (#11):** `logical-term` and `logic-node` are incorrectly housed within `ast-types`.

### Tier 3: Logical Soundness & Theorem Proving

* **[NEW] Herbrand Combinatorial Explosion:** Eradicate naive `ForAll` template grounding. Map universal rules directly into `egglog` Datalog-style `(rule ...)` definitions to prevent exponential memory consumption during inference.
* **[NEW] Heuristic Variable Injection Flaw:** Remove the `inject_variable` AST search for resolving implicit relative clauses. Implement strictly scoped De Bruijn indices for bound variables.
* **[NEW] Unsound Disjunction Evaluation:** Push `OrNode` evaluation down into `egglog` or an external SMT solver. Splitting `Or` checks inside the Rust AST evaluator objectively breaks valid  entailments.
* **[NEW] Temporal Semantic Erasure:** Encode `Past`, `Present`, and `Future` wrappers directly into the e-graph. Do not strip them out during S-expression serialization.
* **Numerical comparison predicates (#4, partial):** The parser handles `li` + PA digits, and `LogicalTerm::Number` exists in the IR/WIT. However, the reasoning schema has zero comparison predicates. Numbers pass through structurally but cannot be reasoned about.

### Tier 4: Syntactic & Linguistic Integrity

* **[NEW] Naive Lexical Regex:** Enforce strict Lojban phonotactics (valid consonant clusters) within the `logos` lexer to reject morphologically invalid strings prior to AST construction.
* **[NEW] Parser Synchronization:** Implement standard error recovery mechanisms (skipping tokens until the next `.i` boundary) rather than hard-failing the entire parse tree on a single syntactic deviation.
* **`sa` proper implementation (#14):** The operator is still degraded to a single-word erase.
* **Causal connectives (#5):** `ri'a/mu'i/ni'i` are completely absent from the parser and semantics.
* **`ganai...gi` implication (#6):** There is no bare conditional support without a quantifier.

### Tier 5: Long-Term Theoretical (Future Work)

* **Event semantics / Neo-Davidsonian (#15):** This is required to resolve the Tanru Intersective Fallacy currently hardcoded into the semantics compiler.
* **Non-monotonic reasoning / belief revision (#16)**.
* **Description term opacity (#17)**.
* **E-Graph cycle detection (#18)**.
* **Conjunction introduction rule (#19)**.
