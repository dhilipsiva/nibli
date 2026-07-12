# Klaro — a human-readable FOL surface syntax for nibli (v0.1 — implemented)

> **Status: v0.1 compat profile IMPLEMENTED and shipping** — Klaro is the DEFAULT
> front-end on every runtime surface since 2026-07-12 (THE FLIP; the `klaro` crate,
> tracker `KLARO_TODO.md`). The executable grammar is `klaro/src/klaro.pest` — the
> normative form of §15, from which the parser is generated, so this spec's grammar and
> the shipped parser cannot drift. Working name "Klaro" (a repo-convention Lojban name
> candidate is `klina`, "clear/transparent"). The spec was synthesized from a
> three-design panel judged on parseability, semantic fidelity, and readability, against
> a 61-construct inventory of the Lojban fragment gerna+smuni actually implement, and
> stress-tested on 18 real corpus sentences (GDPR / drug-interaction KBs). Every
> implemented Lojban construct is either given a surface form or explicitly ruled out of
> scope with a justification — no silent drops.
>
> The spec defines **two profiles**: §1–§13 is the **v0.1 compat profile** (mirrors
> implemented Lojban semantics exactly — Klaro and gerna compile to identical buffers,
> CI-enforced by `verify-klaro` / `verify-klaro-twins`); **§14 is the clean-core v2
> profile** — the de-Lojbanized semantics target for replacing Lojban outright. **v2 is
> a spec target, not implemented.**

**Classification:** Klaro is a *declarative knowledge representation language* — a
human-readable surface syntax for function-free first-order logic with equality,
stratified negation-as-failure under closed-world/closed-domain assumptions, exact-count
quantifiers, and tense/deontic operators. Semantically it is a Datalog/ASP-class
language (the fragment the clingo oracle verifies) with Neo-Davidsonian event semantics.
It is not a "loglang" (that term means spoken Lojban-family conlangs) and not a
programming language in the computational sense — the only "execution" is entailment
checking.

Klaro is a one-page predicate-call language: every claim is `pred(args)`, every KB is a
list of period-terminated claims. It compiles to the **same AstBuffer** the Lojban parser
produces and reuses smuni/logji unchanged, so verdicts, proofs, the Vampire/clingo
differential gates, and the Lean soundness proofs all apply as-is.

```klaro
# Lojban: mi klama le zarci
goes(me, to: the market).

# Lojban: ro lo prenu poi na zanru cu se bilga lo nu se vimcu   (GDPR erasure)
obligated(every person where ~consents, duty: event { removed() }).

# Lojban: ro da zo'u ganai ge da ckape gi la .adam. cu pilno da gi da kajde
all $x: at_risk($x) & takes(Adam, $x) -> alert($x).
```

---

## 1. Design principles

> **Design thesis (2026-07-12):** Klaro is a human-intuitive knowledge-representation
> language — MAXIMALLY INTUITIVE *subject to* semantic distinctions staying visible in
> the spelling (the silent-mistranslation ceiling; principles 2–4 below are that
> constraint made concrete). The logji reasoning core stays untouched throughout the
> v0.1 program — no hard freeze: the two §14 items that touch logji (the xorlo
> presupposition-witness flag and the compute-set rename) remain live v2 options for
> after gerna retires; until then `every` mints xorlo witnesses identically to Lojban
> (disclosed in §4). LLM-generability is a tracked side goal, measured via the fanva
> retarget's silent-mistranslation metric.

1. **Total coverage.** Every construct in the implemented Lojban fragment has a surface
   form or an explicit out-of-scope entry (§10). Nothing is silently dropped.
2. **Semantic distinctions stay visible.** Constructs that compile to *different*
   `LogicBuffer` shapes get *visibly different* spellings: `some` (∃) vs `the` (opaque
   designator) vs `every` (∀-implication rule) vs `Name` (rigid constant) vs
   `exactly N` (CountNode); `every` rules vs `all $x:` prenex; `=` (du/union-find) vs
   `num_equal` (exact dunli) vs `sum`/`product` (tolerant compute). Constructs that
   compile to the *identical* shape are deliberately collapsed (§11).
3. **Scope is what you read.** Leftmost written binder is outermost; descriptions inside
   linked arguments and clause bodies close innermost — exactly nibli's rule, now stated
   as a syntax law.
4. **Fail closed, preferably at the grammar.** Wherever Lojban's compiler rejects
   something semantically, Klaro tries to make it *unwritable* instead (n-ary `=`,
   connected sumti inside linked args, ambiguous `ke'a`). Unknown predicate names are a
   compile error (stricter than gerna's arity-2 default — a deliberate tightening).
5. **One operator set.** Lojban's four connective levels (selbri `je`, sumti `.e`,
   bridi-tail `gi'e`, sentence `.ije`/`ganai gi`) all compile to the same And/Or/Not
   shapes, so Klaro has exactly one claim-level operator set and you write the expansion.

## 2. Lexical structure

> **Erratum (2026-07-12, pest switch):** the implementation is a scannerless
> pest parser (`klaro/src/klaro.pest` is the executable grammar — user
> decision; grammar↔parser drift impossible by construction). The load-bearing
> property below is therefore not a separate lexer but its OBSERVABLE
> BEHAVIOR, carried by two grammar rules — every keyword is self-guarded
> (`"every" ~ !ident_char`) and `ident` starts with `!keyword` — and pinned by
> behavioral tests plus a grammar↔reserved-list conformance test.

The token-level behavior (however implemented) is:

- **Maximal-munch equivalence.** `everyday` is one identifier, never `every` + `day`;
  `theory` is never `the` + `ory`.
- **Keywords are reserved by exact match.** The reserved set:
  `some the every exactly no all where also via past now future must may`
  `event fact property amount concept`
  `me you we we_all we_others you_all this that yonder it it_a it_e it_i it_o it_u slot`
  `seeming` (unused; reserved for a future veridicality distinction, §11).
- **Token classes by leading character:** lowercase = predicate/label identifier
  (`[a-z][a-z0-9_]*`), Uppercase = rigid name, `$x` = logic variable, `?` = witness,
  `_` = unspecified, digits = number, `"` = string, `#` = line comment,
  `/* */` = non-nesting block comment.
- ASCII only. Whitespace separates tokens and is otherwise insignificant.
- Identifiers use underscores (`comes_or_goes`, `metabolized_by`), matching programmer
  habit and keeping `-` free for `->`.

## 3. Terms

| Klaro | Lojban | Compiles to |
|---|---|---|
| `Adam`, `Djan_Smit` | `la .adam.`, `la .djan. .smit.` | `Constant("adam")`, `Constant("djan smit")` (rigid; `_` → space, name lowercased) |
| `me`, `you`, `we`, `we_all`, `we_others`, `you_all` | `mi do mi'o ma'a mi'a do'o` | opaque `Constant(cmavo)` |
| `this`, `that`, `yonder` | `ti ta tu` | opaque constants |
| `it_a` … `it_u` | `ko'a` … `ko'u` | opaque session constants (no assignment mechanism, matching the engine) |
| `$x` | `da/de/di` | logic variable; see §6 for binding |
| `?` | `ma` | fresh independent witness per occurrence (never co-refers — exact `ma` semantics); a query containing `?` returns `[Find]` bindings |
| `_` or an omitted place | `zo'e` / elided place | `Unspecified` |
| `2`, `2.5` | `li re`, PA digits | `Number(f64)`; unsigned; overflow = parse error |
| `"any text"` | `zo` / `zoi` quotes | `Constant(exact string)` |
| `it` | `ke'a` | the relativized entity — **only** inside `where`/`also` bodies (§7) |
| `slot` | `ce'u` | the open place — **only** inside `property { }` (fail-closed elsewhere, like `ce'u` outside `ka`) |
| `the market` | `le zarci` | `Description("zarci")` — **opaque rigid designator, NO quantifier** |
| determiner phrases | `lo` / `ro lo` / … | §4 |
| `event { … }` etc. | `lo nu …` | §5 |

**Dropped term forms (out of scope, §10):** `ri/ra/ru` anaphora (the engine does no
antecedent resolution — a surface that *looks* anaphoric but isn't is a
silent-mistranslation trap), `ko` (no imperative semantics in the engine; write `you`).

## 4. Determiners — the quantifier taxonomy

The five determiners mirror the five gadri shapes one-to-one. **These change the logic;
their spellings are deliberately non-interchangeable:**

| Klaro | Lojban | Compiled shape |
|---|---|---|
| `some dog` | `lo gerku` (= `su'o lo`) | `Exists(v, And(restrictor, matrix))` — veridical ∃, xorlo witness handling applies |
| `the dog` | `le gerku` | `Description("gerku")` — a *constant-like term*, no quantifier. **Trap for English speakers** — see lint L1, §12 |
| `every dog` | `ro lo gerku` | `ForAll(v, Or(Not(restrictor), matrix))` — **the rule shape** (becomes a `UniversalRuleRecord` at assert) |
| `every the dog` | `ro le gerku` | ∀ over the opaque `le_domain_gerku` restrictor |
| `exactly 2 dog` | `re lo gerku` | `Count{v, 2, And(restrictor, matrix)}` — entity-level counting (du-classes collapsed, xorlo witnesses excluded) |
| `no dog` | `no lo gerku` | sugar for `exactly 0 dog` |

**Disclosed engine semantic — xorlo existential import:** asserting a universal rule
(`animal(every dog).`) ALSO establishes that a dog exists: the engine mints a
presupposition witness (Lojban xorlo semantics, implemented in logji), and witnesses
are excluded from `exactly N` counting. This is inherited engine behavior, kept
byte-identical across both front-ends during the dual phase (the equivalence battery
checks verdict identity), and re-decidable at clean-core v2 (§14's xorlo flag — a live
option per the §1 thesis).

Determiner phrases appear **in argument position** (`animal(every dog).`) or as a
**binder block** when the matrix is compound or the variable must be named:

```klaro
every dog $d: animal($d) & barks($d).      # ro lo gerku cu … (one rule, shared binder)
some dog $d: big($d) & goes($d).           # shared existential witness across conjuncts
```

The block form also dissolves `gi'e`'s constant-head restriction safely: sharing a
witness across conjuncts is now *explicit on the page* instead of a hidden hazard.

**Restrictors** are predicate words, optionally with tanru modifiers, linked arguments,
a place selector, and relative clauses:

- `every data controller …` — tanru (§5): juxtaposed words, **last word is the head**.
- `every carer(of: some data)` — linked args = `be`/`bei`: fills x2..xN of the
  restrictor's predicate; the bound variable takes x1. Inner descriptions close
  **innermost** (the documented `be`-arg scope boundary).
- `every loves.loved` — **place selector**: the bound variable occupies the named place
  instead of x1 (= `ro lo se prami`). Equivalent long form: `every loves(x2: it)`.
  **O8 (2026-07-12):** the selector binds to a SINGLE predicate word, requires
  adjacency (no whitespace on either side of the dot), and a selected restrictor takes
  no linked args — this keeps the selector dot from colliding with the statement
  terminator (`Kim = every dog. eats(me).` is two statements; the compact collision
  `… dog.eats(me).` is a parse error, never a silent merge). Use the long `it` form
  for anything richer.
- `some ~permitted` — `~` before the restrictor = description-inner negation (`lo na se curmi`).

## 5. Predications

```klaro
pred(term, term, …)                    # positional: fills x1..xN in order
pred(label: term, …)                   # named: label from the place_labels map, or raw x1..x5
goes(me, to: some market).             # mixed: positionals first, then named
rains().                               # observative — all places Unspecified
```

- Parens are **mandatory** — a bare word is never a claim (the "bridi needs a selbri"
  reject becomes structural).
- Named args subsume **FA tags** (`fa/fe/fi/fo/fu` → `x1:`…`x5:` or dictionary labels)
  and **se/te/ve/xe conversion** (put any term in any place; the alias map may also
  carry a fixed permutation, e.g. `metabolized_by ↦ katna⟨x1↔x2⟩`, so common converted
  forms read naturally).
- Re-filling a filled place, or naming a place beyond the predicate's arity, is a
  **static error** (same fail-closed outcome as Lojban's FA checks).
- Omitted places are `Unspecified` — the natural `zo'e`.
- **Tanru:** 2+ juxtaposed predicate words — `health data(Kanrek)` (`kanro datni`).
  Right-grouping; `[ … ]` brackets give explicit grouping (`ke…ke'e`):
  `[big fast] dog`. Compiles to the shared-event tanru shape, never intersection.
- **zei compounds:** `computer+user` ↦ `skami zei pilno` (compiles under the last
  component, preserving compound identity at the surface).
- **Equality:** `Kim = Adam.` — the flat 2-arg `du` (union-find). Binary by grammar, so
  n-ary `du` is inexpressible rather than an error. **Not** the numeric test — that is
  `num_equal(2, 2)` (`dunli`, exact `==`), and arithmetic is ordinary predication:
  `product(50, 5, 10).` (`pilji`; tolerant isclose, trusted-backend policy unchanged).
  There is deliberately **no infix arithmetic sugar** — the three equality notions
  (du / dunli / compute-isclose) must stay unconflatable.
- **Modal tags** (`via`): `goes(me, to: some market) via cause(some rain).`
  = `… ri'a lo carvi`. BAI and `fi'o` are one construct (BAI compiles exactly as `fi'o`
  over the mapped gismu): `cause↦rinka(ri'a)`, `entails↦nibli(ni'i)`, `motive↦mukti(mu'i)`,
  `reason↦krinu(ki'u)`, `tool↦pilno(pi'o)`, `instead_of↦basti(ba'i)`; any predicate name
  works (`via uses(some car)`). Arity<2 modals fail closed at compile, as today.

**Abstractions** are brace-delimited opaque terms (implicit-`some` descriptions over the
content-hash-marked body, exactly the engine's encoding):

| Klaro | Lojban |
|---|---|
| `event { goes(you) }` | `lo nu do klama` |
| `fact { dog(Adam) }` | `lo du'u` — asserting `believes(me, fact{P})` does **not** make `P` derivable |
| `property { fast(slot) }` | `lo ka ce'u sutra` |
| `amount { … }` / `concept { … }` | `lo ni` / `lo si'o` |

## 6. Claims, operators, and rules

Precedence, tightest first: `~` · deontic/tense prefixes · `&` · `|` · `^` · `<->` · `->`
(right-assoc). Parentheses group.

| Operator | Lojban equivalents (all levels collapse — identical compiled shapes) |
|---|---|
| `~A` | `na` — plain `NotNode`; closed-world/NAF reading is the reasoner's |
| `A & B` | `je` / `.e` / `gi'e` / `ge…gi` / `.ije` |
| `A \| B` | `ja` / `.a` / `ga…gi` / `.ija` |
| `A ^ B` | `ju` / `.iju` (xor) |
| `A <-> B` | `jo` / `go…gi` / `.ijo` |
| `A -> B` | `ganai…gi` / `.inaja` — `Or(Not A, B)`; a ground `->` auto-registers as a zero-variable rule |
| `A & ~B` etc. | `jenai`, `.enai`, … — the `~` is explicit, so the bare-`na`-after-connective trap (rejected at the Lojban grammar level 2026-07-10) cannot exist here |

**Prefixes** (at most one of each per bridi, enforced by the grammar):
`past` / `now` / `future` (`pu/ca/ba` wrappers) and `must` / `may`
(`.ei`→Obligatory / `.e'e`→Permitted). Nesting is pinned to smuni's verified emission
order (`smuni/src/semantic/compile.rs:358-383`): deontic outermost, then tense, then
negation innermost — `must past ~P` compiles to `Obligatory(Past(Not(P)))`. This
resolves former open issue O3; the §15 `Modified <- Deontic? Tense? Atom` order stands.
Consequences the grammar enforces fail-closed (2026-07-12 design-review errata):

- `past ~P` is legal (`Past(Not(P))`); **`~past P` is rejected** — `Not(Past(P))` has
  no encoding in the compat profile (the flat AST's only negation carriers are
  bridi-level flags, and smuni's wrapper order is fixed). No fused negated forms
  (`punai` etc. stay nonexistent).
- Prefixes attach to Predication/Equality atoms only — `past (A & B)` is rejected
  (`Sentence::Connected` carries no tense/deontic fields).
- `~` over a parenthesized compound claim (`~(A & B)`) is rejected — the flat AST has
  no sentence-level Not; write the expansion (`~A | ~B`) explicitly.

Tensed rule *conclusions* work (`all $x: dies($x) -> past lives($x)`); whole-rule tense
remains an assert-time reject, as today.

**The two universal forms compile to different shapes and look different:**

```klaro
animal(every dog).                    # ro lo gerku cu danlu
                                      #   ForAll(v, Or(Not(dog v), animal v)) — rule shape
all $x: dog($x) -> animal($x).        # ro da zo'u ganai da gerku gi da danlu
                                      #   ForAll wraps the body DIRECTLY (prenex shape)
```

`all $x, $y: …` nests ForAlls. Prenex is universal-only, like `ro da zo'u` (there is no
existential prenex — a bare `$x` in a body *is* the existential form). Unbound `$x` is
existentially closed at its **first surface position** (leftmost binder outermost); all
occurrences of one `$name` in a statement co-refer. Lowering note: smuni currently
offers three bare variables per scope (`da/de/di`); the compiler maps the first three
distinct names onto them and **rejects a fourth with a clear error** (never silently
merges) until the smuni cap is lifted.

**Integrity constraints** need no keyword, matching the engine: a disjunctive universal
conclusion registers the constraint —
`every duty $d: fulfilled($d) | breached($d).` = `ro lo … cu … ja …`.
The compiler echoes `[Note: registered as integrity constraint]` so the shape switch is
visible (lint L5). Non-stratified NAF rule sets are rejected atomically at assert, as today.

## 7. Relative clauses

| Klaro | Lojban | Side |
|---|---|---|
| `where <body>` | `poi` (and `voi`, §11) | restrictive — domain side (extra implication antecedent under `every`; And-conjunct under `some`/`exactly`) |
| `also <body>` | `noi` | incidental — matrix side |

- **Bare-predicate sugar:** a body that is a bare predicate word (or tanru), optionally
  `~`-negated, applies to the bound entity at x1: `every person where consents` =
  `… where consents(it)`. This is a formal production, not prose (defect fixed in
  synthesis — §13).
- **Mandatory `it`:** any *parenthesized* application in a clause body must place `it`
  explicitly, and a full-claim body with **zero** occurrences of `it` is a parse error.
  This turns Lojban's implicit-ke'a ambiguity firewall (0-or->1-candidate → semantic
  error) into a syntax rule.
- Stack clauses freely (`where A where B`, mixing `where`/`also`) or conjoin inside one
  (`where A & B`) — both compile to the per-kind AND-conjoined fields. Disjunctive
  `where`-bodies DNF-split into one rule per disjunct at assert, as today.
- Rel clauses attach to rigid terms too: `goes(Adam where dog).` (fresh var +
  matrix conjunct, engine's `pending_matrix_conjuncts` path).
- `it` binds to the **innermost** enclosing clause (no ke'a subscripts, matching the
  engine); outer-clause reference is inexpressible, same as today's front-end.
- **Attachment is innermost-wins (O9, 2026-07-12):** in a clause body ending with an
  equality, a following `where`/`also` attaches to the equality's RHS term, not the
  outer restrictor — `… where it = Boss also rich` makes `also rich` describe Boss.
  Write `where (it = Boss) also rich` for the outer attachment. Lint L8 echoes the
  resolved attachment when this shape appears.

## 8. Queries

Queries **are** claims — nibli's model is unchanged: you *state a proposition* and get
`TRUE`/`FALSE`/`UNKNOWN`. The identical statement grammar is used for assert and query;
the host (REPL/API/UI) decides which pipeline a statement enters. There is no
interrogative form (`xu` remains a parse error in the Lojban front-end and has no Klaro
equivalent). A claim containing `?` run as a query returns `[Find]` bindings:

```klaro
eats(Adam).                   # asserted: a fact — queried: an entailment check
goes(?, to: some market).     # ma-style find
```

`?` is anonymous and per-occurrence independent (exact `ma` semantics). Named find-vars
were **deliberately rejected**: `?x … ?x` would *look* co-referring while `ma` semantics
makes each occurrence independent — the precise silent-mistranslation trap this design
family must avoid. Correlated multi-witness finds are inexpressible, exactly as in
Lojban today (future work if the engine grows correlated find).

## 9. Statements and files

- `.` terminates a statement. Each top-level statement is **one independent fact**
  (the bare-`.i` split); operator-joined claims inside one statement stay **one fact**
  — the fact/retraction boundary is exactly the visible period. (A mechanical
  Lojban→Klaro converter must keep `gi'e` chains inside a single statement to preserve
  granularity.)
- `#` line comments; `/* */` non-nesting block comments (KB headers, provenance blocks).
- Encoding: UTF-8 file, ASCII syntax; string literals may carry arbitrary text.

## 10. Out of scope (with justifications)

| Lojban construct | Why it has no Klaro form |
|---|---|
| `ri/ra/ru` anaphora | compile to *fixed* opaque constants with no antecedent resolution — an anaphoric-looking surface would be a silent-mistranslation trap; use names, `$vars`, or `it_a..it_u` |
| `ko` imperative | engine gives it no imperative semantics (just `Constant("ko")`); write `you` |
| `go'i` pro-bridi | REPL/session state (prior-bridi snapshot rewrite), never present in compiled output; a file format has no ambient "previous line" — write the claim again |
| `si/sa/su` erasure | speech-stream self-repair; a written file is edited with an editor, and a self-destruct token invites injection abuse |
| elidable terminators (`cu/vau/ku/kei/ku'o/ke'e/be'o/fe'u/lo'o`) | exist to disambiguate a terminator-elidable stream; Klaro's explicit delimiters (`()`, `{}`, `[]`, `where`, `.`) leave nothing to terminate |
| Lojban morphology/phonotactics | replaced by case/sigil token classes; predicate identity keys on gismu via the alias map |
| gadri × NU product beyond `lo` (`le nu`, `ro lo nu`, counted abstractions) | deliberate narrowing; zero corpus occurrences; abstractions are hard-wired to the implicit-`some` shape the engine uses |

## 11. Deliberate collapses (identical compiled shapes)

Each pair below compiles to the **identical** `LogicBuffer` shape today, so Klaro spells
them one way. If the engine ever distinguishes a pair, Klaro needs a new surface form
there (the reserved `seeming` keyword pre-books the `voi` case):

`su'o lo` = `lo` → `some` · `voi` = `poi` → `where` (non-veridicality unmodeled) ·
`zo` = `zoi` → `"…"` · BAI = `fi'o` → `via` · forethought = afterthought connectives →
one operator set · selbri/sumti/bridi-tail connectives → written-out expansion ·
`la`+cmevla = `la`+selbri → Capitalized name.

## 12. Tooling: the lint catalog

The grammar is deterministic, but a handful of hazards are semantic, not syntactic. The
linter is part of the design, not an afterthought — and it is IMPLEMENTED
(2026-07-12): `klaro/src/lint.rs`, a data-returning pass (`klaro::lint::Linter`,
stateful per file/session for L1/L4/L7, reset with the KB). Surfaces render each note
as `[Note: …]`: the nibli REPL and the lasna session echo them (verbose-gated, so
`NIBLI_QUIET=1` suppresses them alongside `[Skolem]`/`[Rule]`), and the playground
carries them per KB line on `nibli_protocol::LineResult::notes` into the KB status
bar. Surfaces whose stdout is data (nibli-validate, lojban2klaro, the verify harness)
never invoke the linter.

- **L1 — `the` trap:** warn when `the X` is used and `X` was never introduced by a
  `some`/`every` statement — English speakers write `the dog` intending ∃, but `the` is
  the *opaque designator* (`le`), not a quantifier. (Top silent-mistranslation hazard.)
- **L2 — tanru vs conjunction in clause bodies:** `where big fast` is ONE shared-event
  tanru applied to `it`; `where big & fast` is two restrictor conjuncts. Warn on
  multi-word bare tanru in clause bodies.
- **L3 — scope-by-written-order:** warn when one call contains 2+ quantified arguments
  (`eats($x, every dog)` is ∃∀; reordering args flips it) — args are *not* order-free
  when quantified.
- **L4 — alias echo:** on first use of each alias per file/session, echo the resolved
  gismu + place permutation (`metabolized_by ↦ katna⟨x1↔x2⟩`) — the alias map is trusted
  base and a wrong permutation silently reroutes arguments; make it visible.
- **L5 — constraint echo:** note when a disjunctive universal conclusion registers as an
  integrity constraint rather than a rule.
- **L6 — tense×NAF advisory:** `past ~P` composes legally but lands in the corner the
  verify-soundness oracles conservatively skip (tenseless `NegatedExistsGroup`); emit a
  compile-time NOTE until the oracle gap closes. (`~past P` is rejected outright — §6.)
- **L7 — norm-encoding style:** warn when a KB mixes `must`/`may` wrappers with the
  `obligated()`/`permitted()` predicate idiom for what looks like the same norm — both
  are engine-faithful, but they don't chain with each other.
- **L8 — O9 attachment echo (2026-07-12 review):** when a clause-body-final equality's
  RHS term carries its own `where`/`also` clause, echo the resolved innermost-wins
  attachment (§7) — the outer attachment needs the parenthesized spelling.
- **L9 — digit-split warning (2026-07-12 review, Finding 3):** warn when a statement's
  terminating `.` is whitespace-separated from the claim AND the next statement starts
  with a digit — `X = 2 .5 = $y.` silently splits into two statements (a decimal must
  be written without spaces). Detected at the statement driver.

## 13. Implementation notes

**Pipeline:** Klaro text → lexer → recursive-descent/PEG parser → **synthesize
`nibli_types::ast::AstBuffer`** → `smuni::compile_from_gerna_ast` → logji. smuni's
`validate_ast_buffer` already treats hand-built buffers as a designed-for path
(fail-closed structural validation). gerna is simply not in this pipeline; smuni, logji,
the stores, rendering, and every soundness gate are untouched.

**The alias map** (new, generated at build time alongside `smuni-dictionary`):
`english_name → (gismu, optional place-permutation, place_labels[])`.
- English names from the first lensisku gloss keyword (~98% clean; 5 collisions +
  ~25-word pin table, same mechanism as the existing `GISMU_GLOSS_OVERRIDES`).
- **Reserved-word collisions must be resolved at generation time** — e.g. `bilga`'s
  pinned gloss is `must`, which is a Klaro keyword → alias `obligates`/`obligated`.
- `place_labels` populated by a tiered chain: curated table for the ~80–200 core/corpus
  predicates (same scale as the existing `GISMU_PLACE_TEMPLATES`) → lensisku
  `place_keywords` where present (70/1,338 gismu; more for lujvo) → flagged prose
  heuristic → positional `x1..x5` fallback.
- Lojban words pass through as identity aliases (a Klaro file may use gismu directly).
- **Unknown names are a compile error** (no arity-2 default) — stricter than gerna, and
  the right polarity for a zero-hallucination system.

**Verification obligations** (the new-front-end analogs of the existing gates — ALL
BUILT and gated in `ci` as of 2026-07-12):
1. A **seam-conformance gate** mirroring `nibli-verify/src/seam.rs`: compile Klaro text
   end-to-end and check the FOL against hand-verified structure + metamorphic pairs
   (e.g. `pred(x2: a, x1: b)` ≡ the alias-permuted spelling, canonicalized by positional
   var-rename). **Built: `just verify-klaro`** (the CONSTRUCT_INVENTORY sweep with
   Lojban twins, `nibli-verify/src/klaro_battery.rs` + `tests/klaro_gate.rs`).
2. An **alias-map differential gate** (verify-dict style): alias → gismu →
   place-permutation round-trips checked against the smuni dictionary; the alias map is
   new trusted base and L4's echo does not replace a CI gate. **Built:
   `just verify-klaro-dict`** (`tests/alias_differential.rs` — arity equality,
   round-trips, swap/label integrity, plus a per-alias behavioral compile-equality
   battery).
3. A **Klaro↔Lojban translation battery**: mechanically translate the shipped corpora
   and seeded random sentences both ways; compiled `LogicBuffer`s must be equal (up to
   variable renaming). This is *stronger* than the camxes parse-differential (which
   checks acceptance only) and replaces it for this front-end. **Built: the render
   battery inside `just verify-klaro`** plus the committed corpus twins gate
   **`just verify-klaro-twins`** (`tests/klaro_twins.rs` — per-line canonicalized-buffer
   equality + the Klaro determinism leg).
4. **Fuzzing**: a `fuzz-parse`-style libFuzzer target for the Klaro parser. **Built:
   `just fuzz-klaro`** (parse→resolve→emit with a corrupt-buffer oracle; seeded and run
   in the `fuzz-ci` gate).

**Fixed-in-synthesis defects** (from the judge panel, so they don't regress):
maximal-munch keyword-boundary behavior (kills the `everyday`→`every day`,
`theory`→`the ory`, `you-all`-unparseable class — since the 2026-07-12 pest switch this
is carried by self-guarded keyword rules in `klaro.pest` + behavioral tests, not a
separate lexer; see the §2 erratum); the bare-predicate clause-body sugar is
a formal production (`ClauseBody ← Claim-with-it / "~"? PredSeq`), not prose; block and
inline determiner grammars are consistent; underscore identifiers remove the
hyphen-vs-`->` lexing wrinkle.

**Open issues:**
- **O1**: 3-variable lowering cap (§6) — surface promises more than the seam delivers;
  lifting it is a smuni change (widen the bare-variable set), not a syntax change.
- **O2**: whole-rule tense (`past animal(every dog)`) parses and fails at logji assert,
  same as Lojban; static rejection would duplicate an engine check.
- **O3 (RESOLVED 2026-07-12)**: smuni's wrapper emission is
  `Attitudinal(Tense(Not(matrix)))` (`smuni/src/semantic/compile.rs:358-383`), so
  `must past P` → `Obligatory(Past(P))` — the §15 `Modified` order stands. To be pinned
  by a klaro seam-gate golden. The same review produced the §6 reject errata
  (`~past P`, `past (A & B)`, `~(A & B)`).
- **O4**: `every the dog` (ro le) is grammatical but awkward; zero corpus occurrences,
  ugliness accepted.
- **O5**: the five clusivity pronouns (`we_all` etc.) and `it_a..it_u` are semantically
  inert opaque constants — candidates for a v2 minimalism cull.
- **O6**: correlated multi-witness find (§8) — needs engine support first.
- **O7**: block determiners (`every dog $d: …`) must emit via `Prenex + GanaiGi`/`GeGi`
  — gerna rejects description/quantified `gi'e` heads, so the block-`every` form may
  compile to the *prenex* LogicBuffer shape rather than the restrictor-implication rule
  shape. Whether the two coincide after smuni (incl. `UniversalRuleRecord` registration
  at assert time) must be pinned by a seam-gate golden before the grammar freezes; if
  they differ, §6's block-form framing needs an erratum. *Update (2026-07-12, gate
  landed):* the shape IS the prenex shape, CI-pinned by `verify-klaro`'s O7 golden;
  the emitter's `exactly N`/`the` block limitation stays DOCUMENTED fail-closed
  (targeted error + inline-form workaround) rather than lifted — the Lojban→Klaro
  battery direction can never produce those forms.
- **O8 (RESOLVED at introduction, 2026-07-12)**: the place-selector dot collides with
  the statement terminator under whitespace-insensitive parsing (`Kim = every dog.
  eats(me).` vs `every dog.eats`). Resolved fail-closed in the grammar: `selected` is
  compound-atomic (adjacency both sides), single-word, and takes no linked args — every
  residual compact collision is a parse error, never a silent statement merge. Pinned
  by the O8 test battery in klaro/src/parser.rs.
- **O9**: relative-clause attachment to the RHS term of a clause-body-final equality is
  innermost-wins (see §7); the outer attachment needs parens. Surfaced by the
  2026-07-12 adversarial grammar review; lint L8 echoes the attachment. The same
  review found the pre-existing digit-split hazard (`X = 2 .5 = $y.` parses as two
  statements) — lint L9 warns at the statement driver. Both shipped with the §12
  catalog.

## 14. Clean-core v2 profile (de-Lojbanized)

Everything above this section is the **v0.1 compat profile**: it mirrors the implemented
Lojban semantics one-to-one, so Klaro and gerna compile to *identical* buffers and the
Klaro↔Lojban translation battery (§13) can hold while both front-ends live. This section
specifies the **clean-core v2 profile** — the target for replacing Lojban outright. Same
language skeleton; the Lojban-*inherited* semantic decisions are re-decided on their own
merits. v2 is a spec target, not implemented; each item names its engine change and
verification impact. Migration rule: ship v0.1 first (the verified bridge), then land v2
decisions **one at a time**, each with its GUARANTEES/gate re-pin, retiring gerna and the
camxes gate when the shared fragment stops being useful.

### 14.1 Schema declarations replace the dictionary (the deepest cut)

In v2, predicate identity no longer routes through gismu at all. A KB (or an imported
prelude) **declares its vocabulary**:

```klaro
pred goes(goer, destination, origin, route, means).
pred inhibits(inhibitor, inhibited): "blocks the metabolism of".
pred obligated(who, duty).
```

- The **declared name is the canonical predicate identity** — no gismu keying, no
  generated alias map, no place *permutations* (declared order is canonical order). The
  alias-map trust base, its differential gate (§13, obligation 2), and lint L4
  disappear **by construction**, not by mitigation.
- **Arity = declared place count.** No 5-place cap (that was a gadri/FA artifact), no
  arity-2 default, and an undeclared predicate is a compile error (v0.1's fail-closed
  policy, now grounded in user-authored ground truth instead of a derived dictionary).
- **Place labels = declared names**; raw `x1..xN` remain as an escape hatch.
- The optional `: "gloss"` string feeds rendering/back-translation (nibli-render's gloss
  source becomes the schema, not the lensisku export).
- Grammar delta: `Statement <- PredDecl / Claim "."` with
  `PredDecl <- "pred" ident "(" ident ("," ident)* ")" (":" String)? "."`.
- **Engine change:** smuni's arity/label source becomes injectable (a schema registry
  behind the same lookup seam `JbovlasteSchema` occupies today); `smuni-dictionary` +
  lensisku remain only for the Lojban front-end while it lives.
- **Verification impact:** `verify-dict` (Predilex lower bounds) stops covering Klaro
  KBs — it pins the *Lojban* dictionary. Replacement obligation is much weaker: schema
  self-consistency (duplicate place names, reserved-word collisions, arity stability
  across redeclaration = error).

### 14.2 Removals — Lojban-only residue

| v0.1 construct | Why it existed (Lojban) | v2 disposition |
|---|---|---|
| `the X` (`le`, `Description` terms, `le_domain_` restrictors) | non-veridical gadri | **Removed.** Use a named constant or `some`. Kills the language's worst trap; lint L1 obsolete. |
| tanru juxtaposition + `[ ]` grouping | non-intersective modification | **Removed.** Declare compound predicates (`pred health_data(record)`); lint L2 obsolete. |
| `a+b` compounds (`zei`) | morphological compounding | **Removed** — same replacement. |
| pronoun keywords (`me you we we_all we_others you_all this that yonder it_a..it_u`) | cmavo pro-sumti → opaque constants | **Removed.** A file-based KB has no speaker; use named constants (a REPL may offer session macros). `it` and `slot` stay — they are structural binders, not pronouns. |
| xorlo presupposition witnesses | `lo`'s existential-import semantics, minted in logji | **Removed from semantics.** `some` = plain ∃. The one Lojban decision that reached the reasoner core. |
| `amount { }` / `concept { }` (`ni`/`si'o`) | five-way NU split | **Removed.** `event`/`fact`/`property` remain. |
| da/de/di 3-variable lowering cap | cmavo inventory | **Lifted** — arbitrary distinct `$vars` per scope (resolves O1). |
| builtin BAI tag names (`cause entails motive reason tool instead_of`) | BAI→gismu table | **Demoted** to a standard-library schema prelude; the `via` mechanism itself is unchanged. |
| `every the` (`ro le`) | gadri product | Gone with `the` (resolves O4). |
| `seeming` keyword reservation | `voi` placeholder | Dropped — with `le` and `voi` gone there is no veridicality distinction left to reserve for. |
| gismu identity aliases (writing `klama(...)` directly) | Lojban interop | Gone with the dictionary; a migration tool can mechanically rewrite Lojban-named KBs against a schema prelude. |

### 14.3 Kept — deliberately, with reasons

These *look* Lojban-flavored but are load-bearing engine semantics, and v2 keeps them:

- **Neo-Davidsonian event decomposition** — it is what makes omitted/named arguments
  work (`goes(me)` matches a fact `goes(me, market)` via role predicates). Removing it
  would require a replacement subsumption mechanism and would invalidate the verified
  seam, the ASP translator's regrouping, and the conformance surface bridging the Lean
  proofs. Role predicates simply carry declared names (`goes_x1(ev, a)`).
- **`=` (du) union-find equality**; **stratified NAF + CWA** (with assert-time
  stratification rejection); **`exactly N`/`no` CountNode counting** — now *without* the
  witness-exclusion clause, since xorlo witnesses no longer exist; **abstraction opacity
  markers** (`__abs_` content hash); **tense + deontic wrappers**; the **`via` modal
  conjunct shape**; fail-closed validation everywhere.
- **Compute predicates** stay, under canonical names `product`/`sum`/`quotient`
  (engine item: logji's compute set is currently keyed on `pilji/sumji/dilcu` relation
  names — make the set configurable or rename). Tolerant-isclose and the trusted-backend
  policy are unchanged and stay disclosed.

### 14.4 Engine + gate checklist

Engine (each contained, land one at a time):

1. smuni: injectable schema source at the arity/label lookup seam (§14.1).
2. smuni: lift the bare-variable cap (arbitrary variable names through Exists/prenex
   closure).
3. logji: xorlo witness minting behind a flag, **off** for clean-core — re-pin
   GUARANTEES §Aggregation and the ASP count translator's witness-exclusion clause.
4. logji: configurable compute-set relation names (`product/sum/quotient`).
5. `LOGIC_IR.md`: note that clean-core producers never emit `Description` terms or
   `le_domain_`/`ni`/`si'o` predicates, and drop the da/de/di variable-name pin for
   Klaro-originated buffers (variable naming becomes fully internal).

Verification:

- The Klaro **seam-conformance gate** (§13, obligation 1) re-pins to v2 shapes as each
  decision lands — it is the shape authority for this front-end, as `seam.rs` is for gerna.
- The **translation battery** (§13, obligation 3) only covers the shared-semantics fragment; every
  v2 decision shrinks it. Expected. Retire gerna + the camxes differential when the
  shared fragment stops paying for itself.
- **Vampire/clingo differential gates: unaffected** — they consume the IR, below the
  front-end. Point the random-program generators at schema-declared vocabulary.
- **Lean proofs: unaffected** (they live at/below the IR), *except* anything touching
  xorlo-witness counting — audit alongside engine item 3; the conformance tests bridge
  will catch drift.

### 14.5 Open-issue and lint disposition

- Resolved by v2: **O1** (variable cap — engine item 2), **O4** (`every the` gone),
  **O5** (pronoun cull happens here). O3 was resolved in v0.1 (see §13).
- Unchanged: **O6** (correlated multi-witness find — still needs engine support);
  **O7** (block-determiner shape pin) applies to both profiles.
- Lints: **L1, L2, L4 obsolete** (their hazards are unwritable in v2);
  **L3** (scope-by-written-order), **L5** (constraint echo), **L6** (tense×NAF
  advisory), **L7** (norm-encoding style) remain.

### 14.6 The GDPR erasure rule, clean-core

```klaro
pred person(who).
pred consents(who).
pred obligated(who, duty).
pred removed(what).

obligated(every person where ~consents, duty: event { removed() }).
```

Identical logic to the v0.1/Lojban form — but the argument order is the declared one
(no `bilga⟨x1↔x2⟩` permutation), the vocabulary is self-documenting, and nothing on the
page exists because a spoken conlang needed it.

## 15. Grammar (PEG sketch)

> **Erratum (2026-07-12):** the NORMATIVE, executable form of this grammar is
> `klaro/src/klaro.pest` (pest); this sketch is kept as the readable overview.
> Where they differ, the `.pest` file wins — its keyword rules are pinned to
> the reserved-word list by a conformance test, and the §6 errata
> (prefix/negation shape, arg ordering, count integrality) are enforced by the
> walker with targeted errors rather than encoded as grammar.

```peg
# Tokens come from the lexer (maximal munch; keywords reserved by exact match).
# `_` = token separation (whitespace/comments) — implicit between tokens below.

File        <- Statement* EOF
Statement   <- Claim "."                    # one statement = one independent fact

# precedence, tightest first:  ~   deontic/tense   &   |   ^   <->   ->
Claim       <- Prenex / DetBlock / Impl
Prenex      <- "all" Var ("," Var)* ":" Claim          # ForAll wraps body DIRECTLY
DetBlock    <- BlockDet Restr Var ":" Claim            # named-binder block form
BlockDet    <- "every" "the"? / "some" / "exactly" Nat "the"? / "no"
Impl        <- IffE ("->" Impl)?                       # right-assoc; Or(Not A, B)
IffE        <- XorE ("<->" XorE)*
XorE        <- OrE  ("^" OrE)*
OrE         <- AndE ("|" AndE)*
AndE        <- Unary ("&" Unary)*
Unary       <- "~" Unary / Modified
Modified    <- Deontic? Tense? Atom                    # deontic outermost (O3 resolved);
                                                       # prefixes/(~ over prefixed) atoms
                                                       # restricted per §6 errata
Deontic     <- "must" / "may"
Tense       <- "past" / "now" / "future"
Atom        <- "(" Claim ")" / Equality / Predication
Equality    <- Term "=" Term                           # du — binary only
Predication <- PredSeq Args Tag*
Tag         <- "via" PredName "(" Term ")"

PredSeq     <- PredUnit PredUnit*            # 2+ units = tanru (right-grouping, LAST = head)
PredUnit    <- "[" PredSeq "]" / PredName
PredName    <- ident ("+" ident)*            # a+b = zei compound
Args        <- "(" (Arg ("," Arg)*)? ")"
Arg         <- (Label ":")? Term             # positionals first; refill/overflow = static error
Label       <- "x1"/"x2"/"x3"/"x4"/"x5" / ident

Term        <- "_" / "?" / Number / String / Var
             / KeyTerm / DetPhrase / Abstraction / RigidTerm
Var         <- "$" ident
KeyTerm     <- "me"/"you"/"we_all"/"we_others"/"we"/"you_all"
             / "this"/"that"/"yonder" / "it_a"/"it_e"/"it_i"/"it_o"/"it_u"
             / "it" / "slot"                 # ("it"/"slot" position-checked post-parse)
RigidTerm   <- Name RelCl*
DetPhrase   <- Det Restr
Det         <- "some" / "every" "the"? / "the" / "exactly" Nat "the"? / "no"
Restr       <- "~"? PredSeq ("." Label)? Args? RelCl*
             # ("." Label) = place selector: bound var sits at that place (se-family)
             # Args on the restrictor = be/bei linked places (close innermost)
RelCl       <- ("where" / "also") ClauseBody
ClauseBody  <- Claim / "~"? PredSeq          # Claim bodies must contain `it` (>=1) — static check
Abstraction <- ("event"/"fact"/"property"/"amount"/"concept") "{" Claim "}"

Name        <- [A-Z][A-Za-z0-9_]*
ident       <- [a-z][a-z0-9_]*               # keywords excluded by the lexer
Number      <- [0-9]+ ("." [0-9]+)?          # maximal munch: "f(2.5)." is unambiguous
Nat         <- [0-9]+
String      <- '"' ('\\' . / !'"' .)* '"'
```

## 16. Corpus acceptance set (Lojban ↔ Klaro)

> **Reconciled 2026-07-12** to the SHIPPED honest-generic alias vocabulary (the
> earlier draft used domain overlays — `consents`/`inhibits`/`breached`/
> `at_risk`/`rises`/`takes` — which never enter the core map) and to the
> emitter's landed forms (converted aliases carry positional labels, so
> `obligated`'s duty place is `x2:`). The NORMATIVE, executable form of this
> corpus is **`klaro/tests/acceptance.klaro`** (30 statements — this set plus
> operator/selector/block/tag coverage), pinned by klaro's render∘parse
> fixpoint tests and reused as the fuzz seed.

```klaro
person(Adam).                                    # la .adam. cu prenu
prevents(Flukonazol, Siptucin).                  # la .flukonazol. cu fanta la .siptucin.
metabolized_by(Varfarin, Siptucin).              # la .varfarin. cu se katna la .siptucin.
                                                 #   (alias katna⟨x1↔x2⟩; = cuts(x2: Varfarin, x1: Siptucin))
healthy data(Kanrek).                            # la .kanrek. cu kanro datni  (tanru, head = data)
animal(every dog).                               # ro lo gerku cu danlu
obligated(every data, x2: event { correct() }).  # ro lo datni cu se bilga lo nu drani
permitted(every person where approves).          # ro lo prenu poi zanru cu se curmi
obligated(every data governs where flaw, x2: event { message() }).
                                                 # ro lo datni turni poi cfila cu se bilga lo nu notci
obligated(every person where ~approves, x2: event { removes() }).
                                                 # ro lo prenu poi na zanru cu se bilga lo nu se vimcu  (GDPR erasure)
permitted(every person, x2: event { data discovers() }).
                                                 # ro lo prenu cu se curmi lo nu datni facki
beautiful(every person where ~cat).              # ro lo prenu poi na mlatu cu melbi  (stratified NAF)
prevents(Flukonazol, Siptucin) & metabolized_by(Varfarin, Siptucin) -> increases(Varfarin).
                                                 # ganai ge … gi … gi …  (ground conditional → zero-var rule)
dangerous(every chemical where increases where thin).
                                                 # ro lo xukmi poi zenba poi cinla cu ckape
all $x: dangerous($x) & uses(Adam, $x) -> warns($x).
                                                 # ro da zo'u ganai ge da ckape gi la .adam. cu pilno da gi da kajde
Kim = Adam.                                      # la .kim. cu du la .adam.
past dog(Dan).                                   # pu la .dan. cu gerku
red(exactly 2 red).                              # re lo xunre cu xunre
permitted(every tends(some data)).               # ro lo kurji be lo datni cu se curmi
```

---

*Provenance: synthesized 2026-07-11 from a three-design panel (minimal-core "Klaro" —
winner on fidelity 9/10 and parseability 7/10; readable-English "Claimscript" — winner
on readability, source of the token model and lint catalog; modern-PL "Nib" — source of
the place selector and binder-block ideas), each judged by three adversarial lenses
against the full 61-construct inventory. The panel's raw designs and judgments are in
the session workflow output should an alternative flavor ever be wanted.*
