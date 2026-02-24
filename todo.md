
~/projects/dhilipsiva/lojban_nesy_engine〉:debug ganai mi klama gi do sutra                                                                                                                                                                           02/23/2026 03:13:07 PM
[Error] Parse: parse error at token 0: expected selbri or terms
~/projects/dhilipsiva/lojban_nesy_engine〉:debug ganai mi klama gi ganai do sutra gi la .djan. ciska                                                                                                                                                  02/23/2026 03:13:19 PM
[Error] Parse: parse error at token 0: expected selbri or terms
~/projects/dhilipsiva/lojban_nesy_engine〉:debug ganai ro lo gerku poi barda cu sutra gi lo mlatu cu bajra                                                                                                                                            02/23/2026 03:13:26 PM
[Error] Parse: parse error at token 0: expected selbri or terms
~/projects/dhilipsiva/lojban_nesy_engine〉:debug mi djica lo nu ganai do klama gi mi ciska kei                                                                                                                                                        02/23/2026 03:13:35 PM
[Error] Parse: parse error at token 2: unconsumed tokens remaining
~/projects/dhilipsiva/lojban_nesy_engine〉:debug mi nelci lo ke barda sutra ke'e gerku be la .alis.                                                                                                                                                   02/23/2026 03:13:41 PM
[Logic] (Exists "_v0" (And (And (And (Pred "barda" (Cons (Var "_v0") (Cons (Zoe) (Cons (Zoe) (Nil))))) (Pred "sutra" (Cons (Var "_v0") (Cons (Zoe) (Nil))))) (Pred "gerku" (Cons (Var "_v0") (Cons (Const "alis") (Nil))))) (Pred "nelci" (Cons (Const "mi") (Cons (Var "_v0") (Nil))))))

## Phase 1 — Expressivity foundation
*Parser + semantics work. No architectural changes. Unlocks: faithful encoding of ANY domain.*

**1. Fix `ganai` lexer classification**
`ganai` lexes as Gismu (5 letters). Match on token text, not token kind.
Complexity: 20 minutes. Blocks: nothing downstream, but it's broken right now.

**2. Sumti connectives (`.e` / `.a` / `.o` / `.u` + negated forms)**
"Electrons and muons are leptons." "Drug X or drug Y inhibits CYP3A4."
Every single application needs this — taxonomy is the foundation of every domain.
Parser: afterthought connectives between sumti. Semantics: `.e` → conjunction of two predications sharing the selbri, `.a` → disjunction. Negatable: `.e nai`, `.a nai`, etc.
Complexity: medium. Pattern matches existing selbri connective implementation.

**3. `du'u` / `ka` / `ni` / `si'o` abstractions**
- `du'u` (proposition): "I know THAT the drug inhibits the enzyme" — propositional embedding
- `ka` (property): "the property of being toxic" — needed for classification predicates, symmetry properties, quality attributes
- `ni` (quantity): "the amount of mass" — the bridge between qualitative reasoning and numerical computation dispatch
- `si'o` (concept): "the concept of conservation" — useful for meta-level reasoning

Parser: same structure as `nu...kei`, different selma'o tag. Semantics: each gets a distinct reification strategy. `du'u` → propositional node. `ka` → lambda-like property with `ce'u` as the open variable. `ni` → quantity node (this is where computation dispatch will hook in later).
Complexity: medium-high. `nu` sets the pattern but `ka` needs `ce'u` (lambda variable) support.

**4. BAI modal tags (minimum viable set)**

The full BAI series is ~60+ tags. You need these to start:

| Tag | Meaning | Applications |
|---|---|---|
| `ri'a` | physical cause | drug interactions, physics, biology, climate |
| `ni'i` | logical entailment | legal reasoning, requirements, all formal domains |
| `mu'i` | motivation | legal intent, medical decision reasoning |
| `ki'u` | justification | audit trails, explainability |
| `pi'o` | used by / tool | supply chain, synthetic biology |
| `ba'i` | replaced by | belief revision, theory comparison |
| `fi'o...fe'u` | generic modal | escape hatch for any relation not covered |

Parser: BAI tags behave like place tags but create a new predicate relation rather than filling an existing place. `mi klama ri'a lo nu brife` → "I go, caused-by the event of wind."
Semantics: compile as conjoined predication with the modal relation connecting the main bridi to the tagged sumti.
Complexity: high. This is a new grammatical category, not an extension of existing ones.

**5. Numeric quantifiers**
`re lo kuark` (two quarks), `ci lo elektron` (three electrons), `no lo lepton` (zero leptons), `su'o` (at least one — explicit existential).
Parser: number + gadri as a quantifier position. Semantics: existential with cardinality constraint, or universal with count. This is where Lojban's number system intersects with quantifier logic.
Complexity: medium. Parser part is simple. Semantics for "exactly N" in FOL is verbose (conjunction of N existentials + pairwise inequality + nothing else) — you'll want a dedicated `CountNode` in the IR rather than expanding it.

**6. Sumti-tail `noi` / `poi` on descriptions with `voi`**
Incidental (`noi`) vs restrictive (`poi`) relative clauses are implemented. But `voi` (non-veridical restrictive) is missing, and you can't currently stack multiple relative clauses. Stacking matters for complex classifications: "the protein which binds ATP and which is phosphorylated."
Complexity: low-medium. Extension of existing relative clause machinery.

**7. Afterthought sentence connectives (`.i je` / `.i ja` / `.i jo` / `.i ju`)**
Currently `.i` only separates sentences. You need `.i ja` (or), `.i je` (and — explicit), `.i naja` (implication — afterthought form of `ganai...gi`), `.i jo` (iff).
"The reactor is critical. Therefore the control rods insert." — `.i ni'ibo` or `.i se ni'i bo`.
Parser: recognize connective after `.i`. Semantics: combine adjacent sentence logic forms with the connective.
Complexity: low.

## Phase 2 — Reasoning engine power
*egglog schema + Rust-side reasoning changes. Unlocks: actual inference over encoded knowledge.*

**8. Numerical comparison predicates in egglog**
`zmadu` (greater), `mleca` (lesser), `dunli` (equal) operating on `Number` terms.
Add to egglog schema:

```
(relation NumVal (Term f64))
(rule ((IsTrue (Pred "zmadu" (Cons a (Cons b (Nil)))))
       (NumVal a va) (NumVal b vb))
      ((if (> va vb) (IsTrue ...))))
```

This is where "the mass of the Higgs is greater than the mass of the W boson" becomes machine-checkable.
Complexity: medium. egglog supports primitives but wiring them into your schema needs care.

**9. Non-monotonic reasoning / belief revision**
Currently, assertions are permanent. You can't retract. Every application involving changing knowledge needs this: new drug data contradicts old, new experimental results invalidate a theory, contract amendments override prior clauses.
Implementation: tagged assertions with retraction support. TMS (Truth Maintenance System) style — each fact tracks its justification chain. When a supporting fact is retracted, derived facts are invalidated.
Complexity: high. This is a fundamental change to the reasoning architecture. egglog doesn't natively support retraction — you'll likely need a wrapper layer.

**10. `:reset` command**
Your REPL currently can't reset state. This is listed on your todo and it's blocking development iteration on everything above.
Complexity: low. Export a `reset` function that reinitializes the `OnceLock` statics. Requires `OnceLock` → `Mutex<Option<>>` migration since `OnceLock` can't be reset.

**11. Existential witness extraction (answer variables)**
Currently `query_entailment` returns bool. You need: "WHICH entity satisfies this query?" — `ma klama` should return `mi` if `mi klama` was asserted. This is needed for every application that involves search: "which drugs inhibit CYP3A4?", "which particles have spin 1/2?", "which contract clauses create obligation?"
Implementation: modify `check_formula_holds` to return bindings, not just bool. Existential branch already enumerates entities — capture the successful binding.
Complexity: medium.

**12. Conjunction introduction rule**
Item #19 on your todo. Without it, asserting `A` and `B` separately doesn't let egglog derive `A ∧ B`. This blocks queries like "is it true that BOTH the electron has charge AND the electron has spin?" when charge and spin were asserted independently.
Complexity: low for egglog (one rule), but risk of combinatorial explosion — needs guarding.

## Phase 3 — Computation dispatch architecture
*New WIT interfaces + host-level integration. Unlocks: quantitative reasoning across all domains.*

**13. Computation dispatch protocol**
The WIT interface for external backend routing. The reasoning engine recognizes when a predicate requires numerical computation (via annotation or predicate registry) and emits a `ComputeRequest` instead of attempting egglog resolution.
New IR node: `ComputeNode { backend: Backend, expression: String, bindings: Vec<(String, LogicalTerm)> }`.
Host-side: Wasmtime runner routes requests to registered backends.
Complexity: high. This is new architecture, not an extension.

**14. Backend adapters (at least 2 to prove generality)**
- **Mathematica** via WSTP or WolframScript CLI — covers symbolic + numeric computation
- **Python** via subprocess or embedded interpreter — covers SciPy, SymPy, domain-specific packages (RDKit for chemistry, BioPython, etc.)

Start with Python. It's the lingua franca of scientific computing and covers 80% of backends you'd want (MadGraph, lattice QCD wrappers, PK/PD solvers, optimization solvers all have Python APIs).
Complexity: medium per backend.

**15. Result ingestion — computation results as assertions**
When a backend returns a value, it needs to flow back into the knowledge base as a Lojban assertion. "The computed mass is 125.1 GeV" becomes a new fact that participates in further reasoning.
This closes the loop: reason → compute → assert result → reason further.
Complexity: medium. Needs a trusted assertion path (computation results bypass user input parsing).

## Phase 4 — Production readiness
*Unlocks: real users, real deployments.*

**16. Deontic modals (`e'e` / `e'o` / `ei` / `bilga` / `curmi`)**
Obligation, permission, prohibition. Required for: legal contracts, AV traffic rules, aerospace requirements, medical guidelines, regulatory compliance.
"The vehicle must yield" — `ei lo karce cu jundi`. "The drug is permitted for patients over 18" — `.e'e lo mikce cu pilno`.
Lojban has attitudinals for this but they're currently unparsed. Alternative: use predicates `bilga` (obligated), `curmi` (permitted) which work with existing grammar.
Complexity: if predicate-based, low. If attitudinal-based, high (new parser category).

**17. Event semantics depth (Neo-Davidsonian)**
Current `nu` creates a flat event. Real applications need: events with participants in named roles, temporal ordering between events, events causing other events.
"The reaction in which enzyme E catalyzes substrate S producing product P" — one event, three participants, each in a specific role.
Implementation: extend `nu` compilation to create structured event nodes with role bindings. Connect to BAI modals for inter-event relations.
Complexity: high. Research-grade work.

**18. Module / namespace system**
When you encode the Standard Model AND drug interactions AND traffic law, you need namespaces. Predicates from different domains will collide (`tcarge` means "charged" in physics but could mean something else in legal).
Implementation: Lojban doesn't have native namespaces, but you can use `zoi` quoting or a convention like `xukmi.tcarge` vs `flalu.tcarge`. Engine-side: prefixed predicate resolution.
Complexity: medium.

**19. Persistence layer**
The knowledge base currently lives in WASM memory and dies with the process. Every application needs persistence. Minimum: serialize the egglog state + universal templates + known entities to disk. Better: a proper triple store or graph database backend that the egglog state syncs with.
Complexity: medium for serialization, high for a real database backend.

**20. Explanation / proof trace generation**
"WHY did you conclude this drug interaction exists?" Every high-stakes application (medical, legal, aerospace, regulatory) requires explainability. The reasoning engine needs to emit the derivation chain, not just the boolean result.
Implementation: modify `check_formula_holds` to build a proof tree as it recurses. Each node records which rule/axiom was applied.
Complexity: medium-high.


═══════════════════════════════════════════════════════════════
PHASE 0 — Broken right now (fix before anything else)
═══════════════════════════════════════════════════════════════

0.1  Lexer phonotactic enforcement
     ganai lexes as Gismu. Will keep causing bugs for every
     new cmavo compound that matches CVCCV/CCVCV.
     Fix: validate consonant clusters in logos regex, or
     add a cmavo lookup table that overrides classification.
     Complexity: medium (regex rework) or low (lookup table)
     Blocks: 0.2

0.2  ganai...gi end-to-end verification
     Parser code exists but untested in REPL due to 0.1.
     Once lexer fixed, verify full pipeline.
     Complexity: minutes
     Blocks: nothing

0.3  Disjunction query soundness
     assert "lo mlatu ja gerku" → Or(mlatu, gerku)
     query "? lo mlatu ja gerku" → FALSE (wrong)
     Fix: check_formula_holds OrNode branch should first
     try (check (IsTrue (Or sexp_l sexp_r))) in egglog,
     fall back to component check only if egglog check fails.
     Complexity: low
     Blocks: correct reasoning on any disjunctive knowledge


═══════════════════════════════════════════════════════════════
PHASE 1 — Expressivity foundation
Grammar coverage to encode any domain.
═══════════════════════════════════════════════════════════════

1.1  Sumti connectives (.e / .a / .o / .u + negated forms)
     Needed by: every application (taxonomy is universal)
     Complexity: medium
     Pattern: mirrors existing selbri connectives

1.2  du'u / ka / ni / si'o abstractions
     Needed by: drug interactions (du'u), physics (ka/ni),
     legal (du'u), all meta-reasoning
     Complexity: medium-high
     Depends on: ce'u (lambda variable for ka)

1.3  BAI modal tags (ri'a, ni'i, mu'i, ki'u, pi'o, ba'i,
     fi'o...fe'u)
     Needed by: causation in every domain
     Complexity: high (new grammatical category)

1.4  Numeric quantifiers (re lo, ci lo, su'o, no)
     Needed by: particle physics, chemistry, biology
     Complexity: medium

1.5  Afterthought sentence connectives (.i je / .i ja /
     .i naja / .i jo)
     Needed by: natural discourse encoding
     Complexity: low

1.6  Relative clause stacking + voi
     Needed by: complex entity classification
     Complexity: low-medium

1.7  Deontic predicates (bilga/curmi/nitcu/e'e/ei)
     Needed by: legal, regulatory, AV, aerospace
     Complexity: low if predicate-based (bilga/curmi already
     work as gismu — just need dictionary entries)
     High if attitudinal-based (new parser category)


═══════════════════════════════════════════════════════════════
PHASE 2 — Reasoning engine correctness + power
═══════════════════════════════════════════════════════════════

2.1  WASI state hoisting (replaces OnceLock anti-pattern)
     Move knowledge base to host-managed WASI Resource.
     Enables: reset, multi-tenant, persistence.
     Subsumes: :reset command, persistence layer.
     Complexity: high (architectural rework)
     Blocks: 2.2, 2.5, deployment

2.2  Herbrand explosion → egglog native rules
     Replace eager N×M grounding with lazy (rule ...) defs.
     Current approach hits wall at ~10K entities.
     Needed by: any real-world knowledge base.
     Complexity: high (changes assertion pipeline)
     Blocks: scaling to real datasets

2.3  Numerical comparison predicates in egglog
     zmadu/mleca/dunli operating on Number terms.
     Needed by: physics, pharma (dosage), any quantitative
     Complexity: medium

2.4  Conjunction introduction rule (guarded)
     Assert A, assert B → egglog can derive And(A,B).
     Guard: only fire when both A, B are atomic predicates
     sharing at least one term (prevents combinatorial blow).
     Complexity: low (one rule + guard condition)

2.5  Existential witness extraction (answer variables)
     query_entailment → bool. Need: query_find → bindings.
     "ma klama" → returns "mi".
     Needed by: every search/query application.
     Complexity: medium

2.6  Non-monotonic reasoning / belief revision
     Retraction of facts + justification tracking.
     Needed by: evolving knowledge (drug data updates,
     theory revision, contract amendments).
     Complexity: very high (TMS layer over egglog)


═══════════════════════════════════════════════════════════════
PHASE 3 — Security + deployment readiness
═══════════════════════════════════════════════════════════════

3.1  WASM fuel/epoch limits
     Prevent unbounded execution. Required for any
     networked deployment.
     Complexity: low (Wasmtime API supports this natively)
     Blocks: production deployment

3.2  WIT error variants
     Replace Result<_, String> with typed error enums.
     SyntaxError(pos), SemanticError(msg),
     ReasoningTimeout, BackendError(backend, msg).
     Needed by: LLM agent integration, API clients.
     Complexity: medium (touches all 4 component interfaces)

3.3  WASI capability sandboxing
     Remove inherit_stdio(). Grant minimal capabilities.
     Complexity: low
     Blocks: computation dispatch security

3.4  Parser error recovery
     Skip to next .i on syntax error, continue parsing.
     Return Vec<Result<Bridi, SyntaxError>> instead of
     failing the entire input.
     Needed by: batch processing, robust API usage.
     Complexity: medium

3.5  Explanation / proof trace generation
     check_formula_holds builds proof tree as it recurses.
     Needed by: every high-stakes domain (medical, legal,
     aerospace).
     Complexity: medium-high


═══════════════════════════════════════════════════════════════
PHASE 4 — Computation dispatch
═══════════════════════════════════════════════════════════════

4.1  Computation dispatch WIT protocol
     New interface: compute-backend with dispatch function.
     ComputeNode in logic IR.
     Predicate registry marks which predicates dispatch.
     Complexity: high (new architecture)

4.2  Python backend adapter
     Subprocess or embedded. Covers: SciPy, SymPy, RDKit,
     BioPython, MadGraph, PK/PD solvers.
     Complexity: medium

4.3  Mathematica/Wolfram backend adapter
     Via WSTP or WolframScript CLI.
     Complexity: medium

4.4  Result ingestion as assertions
     Computation results → Lojban assertions → knowledge
     base. Closes the reason→compute→reason loop.
     Complexity: medium


═══════════════════════════════════════════════════════════════
PHASE 5 — Theoretical depth
═══════════════════════════════════════════════════════════════

5.1  Event semantics (Neo-Davidsonian)
     Structured events with named roles, temporal ordering,
     causal links. Resolves tanru intersective fallacy.
     Complexity: research-grade

5.2  Temporal reasoning in e-graph
     Encode Past/Present/Future in egglog schema with
     inference rules (temporal transitivity, persistence).
     Current transparent approach becomes dispatch point.
     Complexity: high

5.3  Description term opacity
     le vs lo distinction in reasoning (intensional vs
     extensional). Matters for belief contexts.
     Complexity: high

5.4  E-graph cycle detection
     Prevent infinite rewrite loops in egglog.
     Complexity: medium (egglog may handle natively)

5.5  Module / namespace system
     Domain-prefixed predicates for multi-domain KBs.
     Complexity: medium


═══════════════════════════════════════════════════════════════
ONGOING — Technical debt (interleave as convenient)
═══════════════════════════════════════════════════════════════

D.1  wasip1 → wasip2 alignment
D.2  reconstruct_sexp deduplication
D.3  ast-types interface naming (split logic types out)
D.4  String pre-allocation in reconstruct_sexp
D.5  Arena allocator for parser AST (when batch processing)
D.6  sa proper implementation
D.7  inject_variable ambiguity warning (when multiple
     Unspecified slots and no ke'a)
