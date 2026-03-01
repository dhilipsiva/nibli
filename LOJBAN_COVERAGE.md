# Lojban Language Coverage

Current coverage of Lojban grammar, semantics, and reasoning in Nibli.

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

### Sentence Connectives
| Feature | Status | Notes |
|---------|--------|-------|
| `ge`...`gi` (forethought AND) | Done | |
| `ga`...`gi` (forethought OR) | Done | |
| `ganai`...`gi` (forethought conditional) | Done | Material conditional |
| `go`...`gi` (forethought IFF) | -- | |
| `gu`...`gi` (forethought XOR) | -- | |
| `.i je/ja/jo/ju` (afterthought) | Done | With `na`/`nai` |

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
| `pu` (past) | Done | Full e-graph temporal reasoning |
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
| egglog e-graph equality saturation | Done | |
| Skolemization (independent) | Done | Fresh `Const` terms |
| Skolemization (dependent/SkolemFn) | Done | Multi-dependency via DepPair |
| Native egglog rules for universals | Done | O(K) hash-join matching |
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
| Non-monotonic belief revision | Done | Fact retraction + egraph rebuild |
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
| Connectives | ~85% (missing `go`/`gu` forethought) |
| Abstractions | ~70% (5 of 8 NU types) |
| Temporal tense (pu/ca/ba) | ~100% |
| Extended tense (spatial, interval, iteration) | ~0% |
| Attitudinals | ~5% (2 of 40+) |
| Vocatives | 0% |
| Pro-sumti | ~90% (missing reflexive vo'a series) |
| Reasoning & inference | ~98% |

**Overall**: ~70-75% of practical Lojban grammar. Coverage is strategically concentrated on the logically important parts — quantification, connectives, predication, event semantics, and tense — which are what matters for a formal reasoning engine. The main gaps are pragmatic/discourse features (vocatives, attitudinals) and extended tense (spatial, interval).
