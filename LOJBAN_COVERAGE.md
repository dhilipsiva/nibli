# Lojban Language Coverage

> **Legacy scope.** Lojban is nibli's **legacy front-end** — Klaro (the
> predicate-call surface, spec [SURFACE_SYNTAX.md](SURFACE_SYNTAX.md)) has been
> the default input language on every surface since 2026-07-12 (THE FLIP).
> Lojban stays fully supported behind `:lojban` / `--lang lojban` /
> `NIBLI_LANG=lojban`, and this document remains normative for that mode and
> for the Klaro↔Lojban equivalence battery (`verify-klaro`,
> `verify-klaro-twins`), until the gerna parser retires at the clean-core v2
> milestone (SURFACE_SYNTAX.md §14).

Current coverage of Lojban grammar, semantics, and reasoning in Nibli's legacy front-end (`gerna`).

## Morphology (Lexer)

| Feature | Status | Notes |
|---------|--------|-------|
| Gismu (root words) | Done | Regex-based recognition |
| Lujvo (compounds) | Done | 6+ char brivla ending in vowel; longest-match prevents cmavo prefix theft; PHF dictionary for arity |
| Cmevla (names) | Done | Consonant-final; used with `la` |
| Cmavo (structure words) | Done | Full tokenization by selma'o |
| Explicit pauses (`.`) | Done | Recognized and handled |

## Metalinguistic Operations (Preprocessor)

| Feature | Status | Notes |
|---------|--------|-------|
| `si` (erase word) | Done | Single-word erasure |
| `sa` (erase to class) | Done | 28 selma'o classes; graceful fallback to single-word |
| `su` (erase discourse) | Done | Full discourse erasure |
| `zo` (quote word) | Done | Opaque `Quoted` token |
| `zoi` (quote text) | Done | Zero-copy delimited slicing |
| `zei` (compound glue) | Done | Lujvo creation from adjacent words |

## Gadri & Quantification

| Feature | Status | Notes |
|---------|--------|-------|
| `lo` (veridical existential) | Done | Compiles to `exists x. P(x)` |
| `le` (referential opaque) | Done | Rigid designator `Description` term; opaque domain restrictor |
| `la` (proper name) | Done | Compiles to `Constant` |
| `ro lo` (universal veridical) | Done | `forall x. P(x) -> Q(x)` with selbri restrictor |
| `ro le` (universal referential) | Done | Opaque `le_domain_X` restrictor |
| `PA lo` / `PA le` (numeric) | Done | Exactly-N count quantifier |
| `su'o lo` (at least one) | Done | Existential marker |
| `pa` (unique) gadri | -- | |
| Mass quantifiers (`su'oi`, `piso'u`) | -- | |
| `lo'i` / `le'i` (set gadri) | -- | |
| `loi` / `lei` (mass gadri) | -- | |

## Place Tags & Modal Tags

| Feature | Status | Notes |
|---------|--------|-------|
| `fa` `fe` `fi` `fo` `fu` | Done | x1 through x5 place tags |
| `ri'a` (cause) | Done | BAI -> rinka |
| `ni'i` (entailment) | Done | BAI -> nibli |
| `mu'i` (motivation) | Done | BAI -> mukti |
| `ki'u` (reason) | Done | BAI -> krinu |
| `pi'o` (tool) | Done | BAI -> pilno |
| `ba'i` (replacement) | Done | BAI -> basti |
| `fi'o`...`fe'u` (custom modal) | Done | Generic modal construction |
| `se` on BAI tags | -- | Case structure inversion on modals |
| Modal stacking | -- | Multiple BAI chained |

## Selbri Constructs

| Feature | Status | Notes |
|---------|--------|-------|
| Root selbri (gismu/lujvo) | Done | |
| Tanru (modifier + head) | Done | Neo-Davidsonian shared event variable |
| `se` `te` `ve` `xe` (conversion) | Done | Argument place permutation |
| `na` (bridi negation) | Done | Sentence-level negation |
| `ke`...`ke'e` (grouping) | Done | Explicit tanru bracketing |
| `zei` compounds | Done | Compound selbri via lujvo glue |
| `be`...`bei`...`be'o` (sumti raising) | Done | Binding arguments to selbri |
| `me` (type conversion) | -- | Convert sumti to selbri |
| `nu'a` (abstraction to selbri) | -- | |
| `co` (tanru inversion) | -- | |

## Relative Clauses

| Feature | Status | Notes |
|---------|--------|-------|
| `poi` (restrictive) | Done | Intersective |
| `noi` (non-restrictive) | Done | Appositive |
| `voi` (non-veridical) | Done | |
| `ke'a` (relative variable) | Done | Bound to enclosing description |
| Clause stacking | Done | Multiple clauses on single sumti |
| Implicit variable injection | Done | Auto x1 fill; ambiguous nested cases rejected |
| Afterthought relative clauses | -- | |

## Connectives

### Sumti Connectives
| Feature | Status | Notes |
|---------|--------|-------|
| `.e` (AND) | Done | |
| `.a` (OR) | Done | |
| `.o` (IFF) | Done | |
| `.u` (XOR) | Done | |
| `nai` suffix (right negation) | Done | |

### Selbri Connectives
| Feature | Status | Notes |
|---------|--------|-------|
| `je` `ja` `jo` `ju` | Done | Same semantics as sumti connectives |
| `jenai` `janai` `jonai` `junai` (nai-suffixed) | Done | Right-operand negation. Bare `na` after a plain connective (`X je na Y`) is REJECTED with a diagnostic pointing at the compound form — camxes-std parity (the historical relaxation was an over-acceptance) |

### Bridi-tail Connectives (GIhA)
| Feature | Status | Notes |
|---------|--------|-------|
| `gi'e` (AND) | Done (constant heads) | Each tail is a full predication (own selbri + trailing sumti) sharing the head terms; desugars to the `.i je` Connected shape with the head repeated (one sentence, one logic root); conjuncts independently queryable after assertion. `go'i` afterwards repeats the LAST tail (Connected-sentence parity) |
| Head restriction | Fail-closed | Only constant heads: names (`la .rex.`, `la terdi`), non-variable pro-sumti (`mi`/`do`/`ko'a`…), quoted literals, `li` numbers. A quantified or description head (`da`, `lo gerku`, `re lo …`) is REJECTED — repeating it per tail would re-quantify one surface scope (officially `da klama gi'e citka` binds ONE witness) and return a wrong TRUE on disjoint witnesses. Restate as `.i je` sentences (repetition explicit) until head witnesses are genuinely shared (TODO) |
| `gi'a` (OR) / `gi'o` (IFF) / `gi'u` (XOR) | Done (parse + query) | Compile like their `.i ja`/`.i jo`/`.i ju` counterparts. Assert behavior pinned by tests: bare `gi'a`/`gi'u` fail closed; `gi'o` registers its two conditional rules (a bare side then queries Unknown — cycle, never TRUE). Known completeness gap: `gi'a na <tail>` registers an inert conditional (event-Skolem constants — never fires modus ponens; same as `.i ja … na`, see TODO) |
| `nai` suffix | Done | Right-tail negation — BOTH spellings: fused `gi'enai` (single token via the lexer's `reclassify_fused_giha_nai` pass; without it the fused form lexed as a phantom lujvo tanru that INVERTED the negation) and spaced `gi'e nai` |
| `na` before a tail | Done | Negates that tail only; a negated tail is recorded in the negative-fact registry (contradiction detection), like a standalone `na` assertion — but only when the negation body is a pure positive conjunction (an impure body, e.g. an Xor lowering's `Not(And(P, ¬Q))`, is never recorded: it would degrade to a STRENGTHENED `¬P` and fabricate contradictions) |
| Tense/attitudinal on a tail (`gi'e pu …`) | Not supported | Rejected with a targeted diagnostic; a tense before the first selbri applies to the first tail only |

### Sentence Connectives
| Feature | Status | Notes |
|---------|--------|-------|
| `ge`...`gi` (forethought AND) | Done | |
| `ga`...`gi` (forethought OR) | Done | |
| `ganai`...`gi` (forethought conditional) | Done | Material conditional |
| `go`...`gi` (forethought IFF) | Done | Biconditional |
| `gu`/`genai`/`ginai`/`gonai`/`gunai` | Not supported | Removed from the lexer; parser handles only ge/ga/ganai/go |
| `.i je/ja/jo/ju` (afterthought) | Done | With `na`/`nai`; both spaced (`.i je`) and solid (`.ije`, `.ijenai`, `.inaja`, …) spellings — the lexer's `fix_dot_i_ja_connective` pass splits the solid compounds |

## Abstractions

| Feature | Status | Notes |
|---------|--------|-------|
| `nu` (event/state) | Done | |
| `du'u` (proposition) | Done | |
| `ka` (property) | Done | With `ce'u` variable binding |
| `ni` (quantity) | Done | |
| `si'o` (concept) | Done | |
| `jei` (truth value) | -- | |
| `li'i` (experience) | -- | |
| `su'u` (unspecified abstraction) | -- | |

## Tense

| Feature | Status | Notes |
|---------|--------|-------|
| `pu` (past) | Done | Full temporal reasoning |
| `ca` (present) | Done | Strict tense discrimination |
| `ba` (future) | Done | Temporal lifting of timeless rules |
| `punai` `canai` `banai` | Done | Tense negation |
| Spatial `FAhA` (va/vi/vu) | -- | Distance markers |
| Spatial direction (FAhA proper) | -- | zu'a, ri'u, ga'u, ni'a, etc. |
| `ZEhA` (ze'i/ze'a/ze'u) | -- | Duration/interval |
| `ZI` (zi/za/zu) | -- | Temporal distance |
| `ROI` (roi/re'u/paroi) | -- | Iteration count |
| `KI` (tense context) | -- | Sticky tense |
| `TAhE` (ru'i/di'i/na'o) | -- | Habitual/typical |

## Attitudinals & Indicators

| Feature | Status | Notes |
|---------|--------|-------|
| `ei` (obligation) | Done | Deontic |
| `e'e` (permission) | Done | Deontic |
| `.ui` (happy) | -- | |
| `.iu` (love) | -- | |
| `.ua` (discovery) | -- | |
| `.ue` (surprise) | -- | |
| `.ii` (fear) | -- | |
| Other UI (40+ words) | -- | |
| `CAI` intensity modifiers | -- | `.cu'i`, `.nai` on attitudinals |
| Evidentials (ja'o, ca'e, ba'a, su'a, ti'e, ka'u, se'o, za'a, pe'i, ru'a) | -- | |
| Discursives (ku'i, ji'a, si'a, mi'u, etc.) | -- | |

## Vocatives

| Feature | Status | Notes |
|---------|--------|-------|
| `doi` (direct address) | -- | |
| `coi` (greeting) | -- | |
| `co'o` (farewell) | -- | |
| `mi'e` (self-identification) | -- | |
| `fi'i` (welcome) | -- | |
| `ki'e` (thanks) | -- | |
| `je'e` (acknowledged) | -- | |
| `ju'i` (attention) | -- | |
| Other COI words | -- | |

## Pro-sumti

| Feature | Status | Notes |
|---------|--------|-------|
| `mi` `do` `ko` | Done | Personal |
| `mi'o` `mi'a` `ma'a` `do'o` | Done | Inclusive/exclusive we |
| `ko'a`-`ko'u` | Done | Assignable pronouns |
| `ti` `ta` `tu` | Done | Demonstratives |
| `ri` `ra` `ru` | Done | Anaphoric |
| `da` `de` `di` | Done | Logic variables (existential closure) |
| `ke'a` | Done | Relative clause variable |
| `ce'u` | Done | Lambda/property variable |
| `ma` | Done | Question -> existential witness extraction |
| `zo'e` | Done | Unspecified |
| `vo'a`-`vo'u` | -- | Reflexive pro-sumti |

## Pro-bridi

| Feature | Status | Notes |
|---------|--------|-------|
| `go'i` | Done | Previous bridi selbri (SelbriSnapshot deep-clone) |
| `bu'a` `bu'e` `bu'i` | -- | Predicate variables |
| Other `GOhA` series | -- | |

## Sentence Structure

| Feature | Status | Notes |
|---------|--------|-------|
| Standard bridi (selbri + sumti) | Done | |
| Observative (selbri-less) | Done | Implicit `go'i` |
| `lu`...`li'u` (quoted text) | Done | |
| `li` + PA (number sumti) | Done | Float parsing |
| `zo'u` (prenex topic-comment) | -- | Variable prenex binding |
| `i` (sentence separator) | Done | Parser recovery on `.i` |
| Termsets (grouped sumti) | -- | |

## MEX (Mathematical Expressions)

| Feature | Status | Notes |
|---------|--------|-------|
| `li` + PA (number literals) | Done | Integer and float |
| Arithmetic via compute backend | Done | pilji, sumji, dilcu, tenfa, dugri |
| MEX operators (+, -, x, /) | -- | In-language math expressions |
| `me'o` (MEX to sumti) | -- | |
| `pi'e` (digit separator) | -- | |

## Reasoning & Inference

| Feature | Status | Notes |
|---------|--------|-------|
| Demand-driven backward-chaining inference | Done | |
| Skolemization (independent) | Done | Fresh `Const` terms |
| Skolemization (dependent/SkolemFn) | Done | Multi-dependency via DepPair |
| Backward-chaining rule templates for universals | Done | O(K) pattern matching |
| Event-decomposed rule compilation | Done | Condition-side exists as pattern vars |
| Structural rewrites | Done | Commutativity, De Morgan, double negation |
| Conjunction elimination/introduction | Done | Guarded by entity domain |
| Disjunctive syllogism | Done | |
| Modus ponens/tollens | Done | Via bidirectional material conditional |
| Numerical comparisons | Done | zmadu (>), mleca (<), dunli (==) |
| Existential witness extraction | Done | `ma` queries return all bindings |
| Proof trace generation | Done | 16 proof rule variants |
| Proof trace memoization | Done | DAG deduplication via ProofRef |
| Backward-chaining provenance | Done | Multi-hop derivation tracing |
| Non-monotonic belief revision | Done | Fact retraction + fact store rebuild |
| Temporal lifting of rules | Done | Timeless rules fire on tensed premises |
| Tense conjunction elimination | Done | Past(A and B) -> Past(A) and Past(B) |
| Compute dispatch | Done | TCP + JSON Lines backend |

## Summary

| Category | Coverage |
|----------|----------|
| Morphology | ~100% |
| Metalinguistic ops | ~100% |
| Gadri & quantification | ~80% (missing set/mass gadri, unique `pa`) |
| Place/modal tags | ~90% (missing `se` on BAI, stacking) |
| Selbri constructs | ~90% (missing `me`, `co`) |
| Relative clauses | ~90% (missing afterthought variants) |
| Connectives | ~90% (missing `gu` forethought variants, GIhA tense-tails) |
| Abstractions | ~70% (5 of 8 NU types) |
| Temporal tense (pu/ca/ba) | ~100% |
| Extended tense (spatial, interval, iteration) | ~0% |
| Attitudinals | ~5% (2 of 40+) |
| Vocatives | 0% |
| Pro-sumti | ~90% (missing reflexive vo'a series) |
| Reasoning & inference | ~98% |

**Overall**: ~70-75% of practical Lojban grammar. Coverage is strategically concentrated on the logically important parts — quantification, connectives, predication, event semantics, and tense — which are what matters for a formal reasoning engine. The main gaps are pragmatic/discourse features (vocatives, attitudinals) and extended tense (spatial, interval).
