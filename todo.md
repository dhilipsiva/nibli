# Nibli — Technical Debt & Improvements

Ordered by impact, priority, and dependency.

## Tier 1: Semantic Correctness & API Truthfulness

1. **Make negation semantics explicit and surfaceable**
   Currently NAF is applied uniformly with no user visibility into which conclusions depend on it.

   Required work:
   - Tag proof trace steps that depend on negation-as-failure with a `NafDependency` marker.
   - When a conclusion's proof contains NAF-dependent steps, the `QueryResult` should carry metadata: `naf_dependent: bool`.
   - Add a `:naf-deps` REPL command that shows which active conclusions depend on NAF.
   - Document the semantics: "Under CWA, `False` means 'not derivable and therefore assumed false.' Under open-world (future), it would mean `Unknown`."
   - This is prerequisite work for per-predicate open/closed world controls (future).

2. **Enforce stratification or reject unsafe recursive negation**
   The engine assumes stratification by construction. It should verify.

   Required work:
   - On each `process_assertion` that registers a `UniversalRuleRecord`, build/update a predicate dependency graph.
   - Edges: conclusion predicate -> condition predicate. Mark edges through negation as "negative."
   - On assertion, check for negative cycles in the dependency graph.
   - If a negative cycle is detected: return `NibliError::Semantic("Unstratifiable negation: predicates X and Y form a negative cycle")`.
   - Performance: incremental graph update is O(rules), cycle check is O(V+E) via DFS. Acceptable overhead.
   - Add tests: safe stratified negation, unsafe mutual recursion through negation, safe recursion without negation.
   - This must also cover rules ingested via gossip (`tavla` ingest path) and replay.

3. **Add logic-layer predicate signature validation**
   `logji` accepts any predicate with any arity from any entry path.

   Required work:
   - Add a `PredicateRegistry` to `KnowledgeBaseInner`:
     ```rust
     pub struct PredicateSignature {
         pub name: String,
         pub arity: usize,
         pub source: SignatureSource,  // Dictionary, UserDeclared, Inferred
     }
     predicate_registry: HashMap<String, PredicateSignature>,
     ```
   - On KB construction, seed from the PHF dictionary (known gismu/lujvo arities).
   - On fact assertion (`assert_typed_fact`), validate arity against the registry. If the predicate is unknown:
     - Option A (strict): reject with `NibliError::Semantic("Unknown predicate: {name}")`.
     - Option B (permissive, recommended initially): accept, register with `SignatureSource::Inferred`, log a warning.
   - Validate ALL entry paths: `process_assertion`, `assert_fact_with_id` (replay), compute backend ingestion, gossip ingest.
   - The arity-2 default in `smuni/src/dictionary.rs` should emit a warning when triggered, not silently succeed.
   - Add tests: valid arity, invalid arity, unknown predicate with both strict and permissive modes.

4. **Add general equality / identity reasoning**
   The biggest classical logic gap.

   Required work:
   - Reserve `du` as a special predicate in `logji` (not just another relation name).
   - When `du(a, b)` is asserted, register the equality pair in a new `EqualityIndex` structure.
   - Implement congruence closure (union-find based): if `du(a,b)` and `du(b,c)` then `du(a,c)`.
   - Modify `check_predicate_in_kb_typed`: when checking `P(a)`, also check `P(x)` for all `x` in `a`'s equivalence class.
   - Modify `try_backward_chain_typed`: when unifying rule conclusions against a query, treat equivalent terms as matching.
   - Add a `ProofRule::EqualitySubstitution { from: String, to: String, via: String }` variant for proof traces.
   - Interaction with tense: `Past(du(a,b))` means `a` was `b` in the past — the equality applies only within that tense context. This is complex; consider starting with untensed equality only.
   - Add tests: simple alias (`du(alice, queen)` -> properties transfer), transitive chain, interaction with universal rules, interaction with Skolem terms.

## Tier 2: Completeness, Explanation & Scaling

5. **Add failure traces / "why not?" explanation**
   When `check_formula_holds` returns FALSE, capture the failure path.

   Required work:
   - Define `FailureTrace` in `nibli-types`:
     ```rust
     pub struct FailureTrace {
         pub steps: Vec<FailureStep>,
         pub root: u32,
     }
     pub enum FailureStep {
         PredicateNotFound { relation: String, args: Vec<LogicalTerm> },
         NoMatchingRule { goal: String, rules_tried: u32 },
         ConditionFailed { rule_label: String, failed_condition: String, children: Vec<u32> },
         DepthExceeded { goal: String, depth: usize },
         CycleCut { goal: String },
     }
     ```
   - Modify `check_formula_holds`: collect dead-end information when returning false. This is similar to `check_formula_holds_traced` but captures failures instead of successes.
   - Add a `query_failure_trace` API alongside `query_entailment_with_proof`.
   - REPL: `:why-not <query>` command.
   - GraphQL: `whyNot` query returning the failure trace.
   - UI: render failure traces in the proof panel with distinct styling (red/grey instead of green).

6. **Add hypothetical / counterfactual reasoning**
   Temporary assumption contexts without mutating the real KB.

   Required work:
   - Add `KnowledgeBase::with_assumptions<F, R>(assumptions: &[LogicBuffer], f: F) -> R`:
     - Clone the KB (or use a copy-on-write overlay).
     - Assert assumptions into the clone.
     - Run the callback `f` against the clone.
     - Discard the clone.
   - REPL: `:assume <lojban> then <query>` syntax.
   - GraphQL: `queryWithAssumptions(kb: String, assumptions: [String], query: String)` mutation.
   - Performance: `KnowledgeBase::clone()` exists and works. For v1, cloning is acceptable. Copy-on-write overlay is an optimization for later.
   - Add tests: assumption doesn't persist after query, nested assumptions, assumption that creates a contradiction.

7. **Replace fixed-depth search with tabling or iterative deepening**
   The depth cutoff silently collapses "not found within depth N" to FALSE.

   Required work (iterative deepening — lower effort, recommended first):
   - Modify `check_formula_holds` to accept a max_depth parameter.
   - Add a wrapper that calls with depth 1, 2, 3, ... up to `max_chain_depth`.
   - If the proof is found at depth D, return `True`. If exhausted all depths up to max, return `False`. This guarantees finding the shallowest proof.
   - The `ResourceExceeded` result handles the case where max_chain_depth itself is hit.

   Required work (tabling — higher effort, future):
   - Maintain a table of (goal, result) pairs across recursive calls.
   - When a goal is encountered that's already in the table, return the cached result instead of re-deriving or cycle-cutting.
   - Implement SLG-style completion: goals that depend on themselves through positive recursion are resolved to the least fixpoint.
   - This subsumes the visited-set cycle detection.

8. **Add argument-position indexing**
   `typed_predicate_facts` indexes by relation name only. Queries like "everything where x2 is adam" scan all facts for that predicate.

   Required work:
   - Add `typed_arg_index: HashMap<(String, usize, GroundTerm), HashSet<StoredFact>>` to `KnowledgeBaseInner`.
   - On `assert_typed_fact`, index each fact by (relation, arg_position, arg_value) for ground arguments.
   - Modify `check_predicate_in_kb_typed` and witness extraction to use the argument index when the query has ground arguments in specific positions.
   - Benchmark: compare query latency before/after on a KB with 1000+ facts for a single predicate.

9. **Add incremental truth maintenance**
    Replace full-rebuild retraction with dependency tracking.

    Required work:
    - Add `justification: Option<Justification>` to derived facts:
      ```rust
      pub struct Justification {
          pub rule: Arc<UniversalRuleRecord>,
          pub bindings: HashMap<String, GroundTerm>,
          pub supporting_facts: Vec<StoredFact>,
      }
      ```
    - When backward chaining derives a fact and it's materialized (e.g., for forward propagation), record its justification.
    - On retraction, walk the dependency cone: find all derived facts whose justifications reference the retracted fact, retract those recursively.
    - Keep full rebuild as a fallback (`:rebuild` REPL command) for consistency verification.
    - Add tests: retract a base fact, verify derived facts in the dependency cone are removed, verify unrelated facts survive.

10. **Selective forward propagation for marked rules**
    Keep backward chaining as the primary engine. Allow opt-in forward propagation for specific rules.

    Required work:
    - Add a `forward: bool` flag to `UniversalRuleRecord` (default false).
    - On fact assertion, check all `forward: true` rules whose conditions might be satisfied by the new fact.
    - If all conditions are met, assert the conclusion immediately (with `Derived` provenance).
    - Primary use case: contradiction detection rules. Mark the negation-checking rules as forward so contradictions are caught at assertion time.
    - REPL: `:forward <rule-id>` to mark a rule for forward propagation.
    - Secondary use case: hot derived predicates that should be pre-materialized for query performance.

## Tier 3: Code Quality & Measurement

11. **Break up oversized core files**
    Three files are disproportionately large and hard to review:
    - `logji/src/lib.rs` — 4,715 lines
    - `gerna/src/grammar.rs` — 4,452 lines
    - `smuni/src/semantic.rs` — needs verification but estimated large
    - `tavla/src/lib.rs` — 1,375 lines

    Split by responsibility:
    - `logji/src/lib.rs` -> extract `assertion.rs` (fact assertion pipeline), `query.rs` (entailment checking), `witness.rs` (witness extraction), `proof.rs` (proof trace generation). Keep `lib.rs` as the public API surface.
    - `gerna/src/grammar.rs` -> already partially split (`selbri.rs`, `sentence.rs`, `sumti.rs`). Move more parse functions out of the main file.
    - `tavla/src/lib.rs` -> extract `gossip_node.rs` (GossipNode state and operations), `crdt.rs` (OR-Set CRDT), `envelope.rs` (envelope creation/verification), `contradiction.rs` (contradiction detection/resolution).

12. **Benchmark the must-have changes**
    Add repeatable `criterion` benchmarks for:
    - Query latency at 10^2 / 10^3 / 10^4 facts (parametric)
    - Recursive rule chains (depth 2, 5, 10)
    - Witness extraction over growing domain sizes
    - Equality-heavy workloads (once equality lands)
    - Retract + rebuild latency (before TMS) and retract + invalidate (after TMS)
    - Argument-position indexing vs relation-only indexing
    - Forward propagation overhead per assertion

    Store baseline results in `benches/baseline.json` so regressions are detectable.

13. **Publish explicit engine guarantees (GUARANTEES.md)**
    Once the must-haves land, write a formal document stating:
    - Soundness: "The engine never returns TRUE for a formula that does not follow from the asserted facts and rules (given a correct implementation)."
    - Completeness: "For non-recursive rule sets with chain depth <= N, backward chaining is complete. For recursive rule sets, [tabling/iterative deepening] guarantees [X]. For depth-bounded search without tabling, the engine is sound but incomplete — UNDETERMINED may be returned for derivable conclusions."
    - Negation policy: "Global closed-world assumption via negation-as-failure. Stratification is [checked/assumed]. Per-predicate open-world is [not yet supported]."
    - Equality: "Identity via `du` with [congruence closure/transitive substitution]. Equality reasoning is [tensed/untensed only]."
    - Resource limits: "Fuel, memory, and chain depth are bounded. Exceeding any limit returns `ResourceExceeded`, not FALSE."
    - Retraction: "[Full rebuild / incremental TMS]. Provenance is [preserved/re-derived]."

## Tier 4: Infrastructure & Deployment

14. **Fine-grained server locking**
    Replace `Arc<Mutex<>>` with `RwLock` for read-heavy gossip queries. Blocked by rustc ICE in `nibli-server` (`check_mod_deathness` panic prevents compilation with `RwLock`). Retry after rustc upgrade past `1.94.0`.

15. **Gossip-layer contradiction detection push-down**
    Currently contradiction detection lives in `tavla` (syntactic negation toggle on `cu na`). It should also exist in `logji` (semantic contradiction via the proof engine).

    Required work:
    - On assertion, optionally run a quick backward-chain check: does `Not(new_fact)` hold in the current KB?
    - If yes, flag the contradiction with a proof trace showing *why* they contradict (not just "na toggle matched").
    - This is more powerful than syntactic negation: it catches contradictions that arise from rule interactions, not just direct negation.
    - Gate behind a flag (`contradiction_check_on_assert: bool`) since it adds per-assertion cost.

16. **WebRTC transport for tavla gossip**
    The README and memory notes indicate WebRTC P2P as the designated transport. `tavla/src/webrtc.rs` exists (15K) but verify completeness relative to TCP transport.
    Required work:
    - Verify WebRTC transport is feature-complete relative to TCP (connect, send envelope, receive envelope, sync, disconnect).
    - Ensure signaling server dependency is minimal (STUN/TURN for NAT traversal, disposable after connection).
    - Test browser-to-browser peering via the Dioxus UI.
