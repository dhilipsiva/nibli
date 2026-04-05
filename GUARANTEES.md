# Nibli Engine Guarantees

Formal statement of the reasoning engine's properties, boundaries, and contracts.

## Soundness

**Guarantee:** The engine never returns TRUE for a formula that does not follow from the asserted facts and compiled rules, given a correct implementation.

If the engine says TRUE, a formal proof trace exists showing the derivation chain from asserted axioms through named inference rules to the conclusion. Every step is mechanically verifiable.

**Caveat:** The engine is software. A bug in the parser (gerna), semantic compiler (smuni), or reasoning engine (logji) could produce a valid-looking proof of a wrong statement. Such a bug would be deterministic, reproducible, and testable — fundamentally different from stochastic hallucination. The engine is tested with 639+ unit tests and 21 integration tests across the full pipeline.

## Completeness

**Guarantee:** For non-recursive rule sets with chain depth <= N (default 10), backward chaining with iterative deepening is complete — if a proof exists within the depth bound, it will be found.

**Iterative deepening:** Queries try depth 1, 2, 3, ..., up to `max_chain_depth`. This guarantees finding the shallowest proof first. If the proof exists at depth D <= max_chain_depth, it is found. If no proof exists at any depth, the engine returns FALSE (not ResourceExceeded).

**ResourceExceeded(Depth):** Returned only when all depths up to max_chain_depth are exhausted without finding a proof — the conclusion may exist at a deeper level but the engine cannot determine this within its configured bound.

**For recursive rule sets:** The engine uses a visited-set to detect cycles, returning `Unknown(CycleCut)` instead of diverging. This makes it sound but incomplete for recursive programs — a derivable conclusion may be reported as Unknown if the proof path goes through a cycle.

## Negation Policy

**Semantics:** Global negation-as-failure (NAF) under the Closed-World Assumption (CWA). `NOT P` holds when `P` cannot be proved from the current knowledge base.

**Stratification:** Enforced at rule registration time. The engine builds a predicate dependency graph and rejects any rule that would create a negative cycle (a cycle containing at least one negation edge). This guarantees NAF is applied only in stratifiable programs, where it is sound.

**NAF visibility:** Proof traces mark Negation steps with `holds: true` as NAF-dependent. The `ProofTrace::has_naf_dependency()` method reports whether a conclusion relies on the CWA. Under open-world semantics, the same conclusion would be Unknown rather than True.

**CWA implication:** `FALSE` means "not derivable from the current KB and therefore assumed false." It does NOT mean "known to be false in the real world." If the KB is incomplete, NAF may give True for conclusions that would be Unknown with complete information.

## Equality Semantics

**Predicate:** `du(a, b)` — identity/equivalence. Means `a` and `b` are the same entity.

**Properties:**
- **Reflexivity:** `du(x, x)` holds for any x without explicit assertion.
- **Symmetry:** `du(a, b)` implies `du(b, a)` — checked via canonical representative.
- **Transitivity:** `du(a, b)` + `du(b, c)` implies `du(a, c)` — union-find with path compression.
- **Substitutivity:** `du(a, b)` + `P(a)` implies `P(b)` — checked in both direct fact lookup and backward chaining.

**Scope:** Untensed only. `Past(du(a, b))` is stored but does not activate the equivalence index. Tensed equality is future work.

**Implementation:** Union-Find in `KnowledgeBaseInner` with path compression and union-by-size. Equivalence classes rebuilt from surviving `du` facts on retraction.

## Predicate Validation

**Arity checking:** The engine tracks predicate arities via a `PredicateRegistry`. First assertion of a predicate registers its arity (from the 10,521-entry PHF dictionary if known, otherwise inferred from first use). Subsequent assertions with mismatched arity produce a warning.

**Mode:** Permissive (v1). Arity mismatches are warned, not rejected. The fact is still inserted. Strict mode (rejection on mismatch) is future work.

## Integrity Constraints

**Mechanism:** `register_constraint(label, conjuncts)` declares a set of facts that must NOT all hold simultaneously. Checked after every fact insertion.

**Mode:** Permissive (v1). Violations are warned via stderr, not rejected. The fact is still inserted. Strict mode is future work.

**Scope:** Constraints are structural declarations — they survive KB reset but are not persisted to disk.

## Resource Limits

**Backward-chaining depth:** Configurable `max_chain_depth` (default 10). Iterative deepening tries 1..=max_chain_depth. Exceeding returns `ResourceExceeded(Depth)`.

**WASM fuel:** Wasmtime fuel-based execution limits prevent unbounded computation. Configurable via `NIBLI_FUEL` env var or `:fuel` REPL command. Exceeding returns `ResourceExceeded(Fuel)`.

**WASM memory:** `StoreLimits` caps linear memory growth. Configurable via `NIBLI_MEMORY_MB` env var (default 512 MB). Exceeding returns `ResourceExceeded(Memory)`.

**Contract:** When a resource limit is hit, the engine returns `ResourceExceeded(kind)` — never FALSE. The engine honestly reports that it cannot determine the answer within its resource bounds, rather than guessing.

## Retraction Model

**Incremental TMS:** For simple ground facts (no Skolemization, no rules), retraction removes the fact directly from the fact store and all indexes — O(1) per fact.

**Full rebuild fallback:** For complex assertions (ForAll rules, existential variables, Skolemized facts), retraction falls back to full rebuild from surviving base facts. This is O(total_non_retracted_facts) but guaranteed correct.

**Equivalence rebuild:** When `du` facts are retracted, the equivalence index is rebuilt from all surviving `du` facts.

**Public rebuild:** `KnowledgeBase::rebuild()` forces a full rebuild — available as a consistency check or recovery mechanism.

## Query Result Contract

Every query returns exactly one of four results:

| Result | Meaning |
|--------|---------|
| `True` | The formula is derivable from the KB. A proof trace is available. |
| `False` | The formula is not derivable (CWA: assumed false). |
| `Unknown(reason)` | The engine cannot determine the answer: `CycleCut` (recursive cycle detected), `IncompleteKnowledge`, or `NafDependent`. |
| `ResourceExceeded(kind)` | A resource limit was hit: `Depth`, `Fuel`, or `Memory`. The answer may exist but cannot be found within the configured bounds. |

There is no confident-sounding middle ground. The engine never guesses.

## Hypothetical Reasoning

**Mechanism:** `KnowledgeBase::with_assumptions(assumptions, callback)` creates a temporary clone of the KB, asserts assumptions into the clone, runs the callback, and discards the clone. The original KB is untouched.

**Isolation:** Multiple independent hypotheticals and nesting are supported. Each gets its own snapshot.

**Cost:** O(KB_size) per clone (acceptable for v1). Copy-on-write overlay is future work.

## Aggregation

**count_witnesses:** Returns the number of distinct witness binding sets satisfying an existential formula.

**aggregate(formula, variable, op):** Extracts numeric values from a named variable across all witness bindings and applies Sum, Min, Max, or Avg. Returns None if no numeric witnesses found.

## What the Engine Cannot Do

- **Probabilistic reasoning:** No confidence scores, no uncertainty propagation. Every result is True, False, Unknown, or ResourceExceeded.
- **Abductive reasoning:** Cannot generate hypotheses ("what facts would make this true?"). Can test hypotheses via `with_assumptions`.
- **Higher-order reasoning:** First-order logic only. No quantification over predicates.
- **Common-sense reasoning:** No default reasoning beyond NAF. No frame axioms, no inertia.
- **Fuzzy logic:** No degrees of truth. Binary true/false within the formal core.
- **Intentional vagueness:** Legal terms like "reasonable" or "good faith" cannot be formalized. The engine handles the deductive, rule-based layer only.
