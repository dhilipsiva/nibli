# Nibli — Reasoning Engine Backlog

Ordered by impact on the book ("Ultimate Symbolic Reasoning for AI Engineers").

## Tier 1: Core Reasoning Gaps

1. **Selective forward chaining (contradiction detection at assertion time)**
   Nibli is purely backward-chaining. Forward chaining eagerly derives consequences when facts are asserted. Critical for:
   - Contradiction detection at assertion time (not just query time)
   - Data-driven reasoning (sensor values → derived alerts)
   - Materializing hot derived predicates for query performance

   Implementation:
   - Add `forward: bool` flag to `UniversalRuleRecord` (default false).
   - On fact assertion, check all `forward: true` rules whose conditions might be satisfied by the new fact. If all conditions met, assert conclusion immediately.
   - REPL: `:forward <rule-id>` to mark a rule for forward propagation.
   - Primary use: contradiction detection rules. Secondary: hot derived predicates.

2. **Tabling / SLG resolution (recursive completeness)**
   Iterative deepening finds the shallowest proof but doesn't cache intermediate results. Full tabling guarantees termination for all Datalog programs and caches sub-derivations.

   Implementation:
   - Maintain a table of (goal, result) pairs across recursive calls.
   - When a goal is encountered that is already in the table, return the cached result.
   - SLG-style completion: goals that depend on themselves through positive recursion are resolved to the least fixpoint.
   - Subsumes the current visited-set cycle detection.

3. **Defeasible / prioritized rules (exception hierarchies)**
   No mechanism for "rule A takes precedence over rule B." Legal reasoning frequently has exception hierarchies (lex specialis). Currently, conflicts are silent.

   Implementation:
   - Add priority: u32 to UniversalRuleRecord (default 0).
   - When multiple rules derive conflicting conclusions, the highest-priority rule wins.
   - REPL: `:priority <rule-id> <N>` to set rule priority.
   - For defeasible defaults: lower-priority default rules are overridden by higher-priority specific rules.

## Tier 2: Domain Modeling & Interop

4. **Sorted logic / type hierarchy (compile-time sort checking)**
   No way to declare `person ⊂ animal` as a sort hierarchy. Currently encoded as rules which works but doesn't catch ill-sorted queries at compile time.

   Implementation:
   - Add `SortHierarchy` to KnowledgeBaseInner: `HashMap<String, HashSet<String>>` (sort → parent sorts).
   - Predicate signatures gain argument sort annotations: `gerku(x: animal, y: place)`.
   - On assertion, validate that argument entities belong to the declared sort (or a subsort).
   - Compile-time rejection of ill-sorted queries.

5. **Knowledge base import/export in standard formats (OWL, RDF)**
   No support for standard KR formats. The engine only ingests Lojban text and LogicBuffer. Importing existing ontologies (SNOMED-CT, FIBO) would expand practical applicability.

   Implementation:
   - Add `nibli-import` crate with parsers for OWL/XML, RDF/Turtle, and CSV/TSV.
   - Map OWL class hierarchies to sort declarations + universal rules.
   - Map RDF triples to ground facts.
   - Export: serialize KB facts to RDF/Turtle or JSON-LD.

## Tier 3: Developer Experience

6. **Interactive debugging / step-through tracing**
   No way to set breakpoints on predicates, step through backward chaining, or inspect the search tree live. Proof traces are post-hoc.

   Implementation:
   - Add `:trace <predicate>` REPL command to enable per-predicate tracing.
   - When a traced predicate is encountered during backward chaining, print the current goal, depth, bindings, and matching rules.
   - Add `:step` mode that pauses after each backward-chaining step and waits for user input.
   - Add `:search-tree` command that renders the full search DAG (not just the successful path).
