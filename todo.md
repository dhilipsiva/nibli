# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Semantic Correctness & API Truthfulness

1. **Introduce a first-class query result type**
   Replace bool-only entailment across `logji`, `nibli-types`, WIT, `lasna`, `nibli-engine`, `nibli-server`, `nibli-ui`, and the REPL with a shared result model such as `True`, `False`, `Unknown`, `ResourceExceeded`, and `Inconsistent`.
   Required work:
   - Define the status enum and wire format.
   - Decide how proof traces and failure traces attach to each status.
   - Add regression tests for depth-limited search, fuel exhaustion, and ambiguous/incomplete KB states.

2. **Make negation semantics explicit**
   Stop treating negation policy as an implicit implementation detail. Keep current NAF/CWA behavior explicit until a richer world-assumption model lands.
   Required work:
   - Surface whether a conclusion depends on negation-as-failure.
   - Define how open-world vs closed-world behavior is represented in APIs and UI.
   - Document what `False` means under each policy.

3. **Enforce stratification or reject unsafe recursive negation**
   The current engine assumes negation safety; it should verify or reject unsupported rule graphs.
   Required work:
   - Build a predicate dependency graph from asserted/compiled rules.
   - Detect negative cycles and return structured errors.
   - Add tests covering safe negation, unsafe negation, and mixed direct-assert / replay paths.

4. **Add logic-layer predicate signature validation**
   Arity and signature rules must be enforced inside `logji`, not only during Lojban compilation.
   Required work:
   - Introduce a predicate registry owned by the reasoning layer.
   - Validate all entry paths: parsed assertions, direct `assert-fact`, compute ingestion, replay, and any other trusted internal path.
   - Replace silent fallback behavior with warnings or hard failures where appropriate.

5. **Add general equality / identity reasoning**
   Numeric `dunli` is not enough. The engine needs logical identity with substitutivity.
   Required work:
   - Define `du` / identity semantics in the logic layer.
   - Support alias propagation, transitive equality chains, and proof trace integration.
   - Add tests for identity-based inference, equality cycles, and interaction with tense/deontic wrappers.

## Tier 2: Completeness & Scaling

6. **Replace fixed-depth search as the only completeness strategy**
   A depth cutoff is a guardrail, not a complete recursion story.
   Required work:
   - Add tabling / SLG-style caching or an equivalent recursion-safe strategy.
   - If a fixed bound remains, expose it through the query result type instead of silently collapsing to `False`.
   - Evaluate iterative deepening as a fallback where full tabling is not yet available.

7. **Add argument-position indexing**
   Predicate-name indexing alone will not scale for large, partially-bound query workloads.
   Required work:
   - Extend the fact store with relation+argument-position indexes.
   - Use the new indexes in witness search and backward-chaining condition lookup.
   - Benchmark the before/after cost of common query shapes.

8. **Add incremental truth maintenance**
   Full replay is currently sound and simple, but it is not the long-term retract story.
   Required work:
   - Track justifications / dependency cones for derived conclusions.
   - Support surgical invalidation on retract while keeping full rebuild as a fallback until trusted.
   - Preserve proof/provenance semantics across retract and re-derive.

9. **Selective forward propagation for marked rules**
   Keep backward chaining as the primary engine, but allow opt-in forward propagation where it pays for itself.
   Candidate uses:
   - contradiction alerts
   - hot derived predicates
   - proactive monitoring / watch conditions

## Tier 3: Code Quality & Measurement

10. **Break up oversized core files**
    The core engine is reviewable only with too much effort. Split `logji/src/lib.rs`, `gerna/src/grammar.rs`, and `smuni/src/semantic.rs` by responsibility without changing behavior.

11. **Benchmark the must-have changes**
    Add repeatable measurements for:
    - query latency at 10^2 / 10^3 / 10^4 facts
    - recursive rule chains
    - witness extraction
    - equality-heavy workloads
    - retract latency before and after truth maintenance work

12. **Publish explicit engine guarantees**
    Write down the actual semantics once the must-haves land:
    - soundness / completeness boundaries
    - negation policy
    - equality guarantees
    - resource-limit behavior
    - retract / provenance guarantees

## Tier 4: Infrastructure & Deployment

13. **Fine-grained server locking**
    Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in `nibli-server` (`check_mod_deathness` panic prevents compilation with `RwLock`). Retry after rustc upgrade past `1.94.0`.
