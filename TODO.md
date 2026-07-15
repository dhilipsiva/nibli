# TODO

The single engine tracker (KR_TODO.md was merged in here 2026-07-12; the Klaro v0.1
program it previously tracked is COMPLETE). Plain bullets, never numbered — work the
FIRST remaining bullet; cross-reference items by name. Delete a bullet entirely when
it fully lands; update it if only partially done. The nibli-KR program bullets come
first and take precedence over the engine bullets after them.

**THE PIVOT (user decisions, 2026-07-12, second decision round):**

1. **One surface.** The dual-front-end era ends: Lojban is DROPPED, not kept as a
   legacy mode ("just because I am fascinated by lojban does not mean others will").
   The gerna crate moves to a separate repo and is donated to the Lojban community —
   together with an agentic Lojban translation tool carved from the Transparency
   Triad's formalizer.
2. **The language is named "nibli knowledge representation (KR) language"** — "nibli
   KR" for short. The working name "Klaro" is retired from EVERYTHING: crate names,
   module names, docs, UI strings, file extensions, recipes. The Transparency Triad's
   formal tab reads **"nibli KR"** with a small **"?" icon** whose tooltip reads
   **"nibli knowledge representation (KR) language"**.
3. **Total Lojban purge.** No Lojban word survives in this repo except the engine
   name `nibli` itself (the project exists because of Lojban; the name honors that)
   and the repo name. That includes crate names (nibli-semantics/nibli-reason/nibli-pipeline/nibli-host/fanva…),
   the WIT package (`lojban:nibli`!), env/commands, internal vocabulary
   (selbri/sumti/bridi/tanru/xorlo/goi…), corpora, AND the canonical predicate
   names — **proof traces must contain no Lojban** (today they show
   `Asserted: gerku.x1(adam)`, `Exists: da = adam`, `zo'e` — because the IR
   predicate names ARE gismu and `$vars` lower to the da/de/di pool).

Program discipline unchanged: every bullet lands independently CI-green; the logji
reasoning core's soundness surface stays gate-protected throughout (never delete a
verification oracle before its replacement lands). The full de-Lojbanization
inventory (leak surfaces, rename ripple, gate fates) was mapped 2026-07-12;
load-bearing anchors are quoted per bullet.

**Donation-repo extraction: DONE (2026-07-12, separate session).** The standalone
repo lives at `~/projects/dhilipsiva/fanva` (→ github.com/dhilipsiva/fanva, push by
hand), extracted from nibli @ `6c59357` (pinned in fanva's `NIBLI_REV`) as a fresh
working-tree copy + provenance pointer. It carried the full manifest — gerna (+goi),
the camxes parse-differential (as `fanva-verify`), ilmentufa flake input,
LOJBAN_COVERAGE.md, fuzz_parse, camxes browser assets, the Lojban-only agentic
translator (`fanva` crate + carved UI + `fanva-proxy/`), all four `.lojban` corpora,
`lojban2klaro` (archival), the python flywheel, Predilex + verify-dict, and the
Lojban items from this tracker (fanva-proxy retirement / jbotci-AGPL licensing, GIhA
quantified-head witness sharing, determinism-corpus GIhA lines — those now live in
fanva's TODO, not here) — and its full test matrix is green (411/411 camxes
differential, zero divergences). fanva VENDORS the crate closure
(nibli-types/nibli-semantics/nibli-lexicon/nibli-protocol/nibli-render) under the upstream
names, so nibli's later crate renames do NOT ripple into it.

**THE DROP: LANDED (2026-07-13).** The Lojban front-end is gone: gerna deleted, the
`Language` enum + `NIBLI_LANG` + WIT `set-language` removed (WIT bumped to
`lojban:nibli@0.2.0` — the package RENAME rides the purge bullet), go'i machinery +
smokes deleted, camxes/jbotci/fanva-proxy/tersmu torn out (the deployed worker is
the fanva repo's now), `.lojban` corpora + twins machinery + `verify-klaro`/
`verify-klaro-twins`/`verify-parser` retired (coverage re-anchored in
`verify-nibli-kr-seam`), python flywheel + LOJBAN_COVERAGE.md deleted, every test
surface machine-ported to KR with per-literal round-trip-equality verification.
The last dual-front-end engine is tagged **`v0.1-lojban-final`** (the pin point
for the book harness and the pre-migration demo site). Two known consequences,
both user-accepted: the deployed /nibli demo is BROKEN until the site-migration
session lands (its Lojban-era JS/KB no longer compiles; `nibli-wasm` keeps
`set_language`/`back_translate` as deprecated no-op/gloss shims so the JS at
least loads), and `verify-book` is red until the book migrates or pins the tag.

**CRATE PURGE: LANDED (2026-07-13).** The 6 Lojban-named crates renamed —
`smuni`→`nibli-semantics`, `logji`→`nibli-reason`, `lasna`→`nibli-pipeline`,
`gasnu`→`nibli-host`, `nibli-fanva`→`nibli-formalize`, `smuni-dictionary`→
`nibli-lexicon` (user choice "semantics/reason/host"). WIT package
`lojban:nibli`→`nibli:engine`, world `lasna-pipeline`→`nibli-pipeline`, interface
`lasna`→`engine`, artifact `nibli.wasm`. The flat-AST TYPE names + grammar-vocabulary
fns/fields de-Lojbanized (Sumti→Argument, Selbri→Predicate, Bridi→Proposition,
Gadri→Determiner, BaiTag→ModalRelation, Attitudinal→DeonticMood;
`compile_from_gerna_ast`→`compile_from_ast`, JbovlasteSchema→LexiconSchema, …).
The predicate-name VALUES (gismu in the wire protocol, dictionaries, IR strings,
proof-trace output, redb keys) were the predicate-name de-Lojbanization (since LANDED, below);
the
bullet. `nibli` survives.

**VESTIGE AUDIT + CMAVO VARIANTS: LANDED (2026-07-13).** The dead Lojban-only AST
capacity nibli-kr's emitter can never produce was verify-then-removed
(parity-guard-protected; ~27 dead test fixtures went with it): `ModalRelation`
(ex-BaiTag) + `ModalTag::Fixed` + `modal_relation_name()`, `Determiner::La`,
`RelClauseKind::Voi`, `SentenceConnective::GaGi`/`GoGi`, `Argument::Connected`
(argument connective), `Predicate::Connected` (predicate connective) + the
`connected_bridi` render machinery, and the `Afterthought` na/nai tuple slack.
`PlaceTag` collapsed to a `u8` place index. The surviving cmavo enum VARIANTS were
renamed to English (Pu/Ca/Ba→Past/Now/Future, Se/Te/Ve/Xe→Swap12..15,
Je/Ja/Jo/Ju→And/Or/Iff/Whether, Lo/Le/RoLo/RoLe→Indefinite/Definite/Universal…,
Nu/Duhu/Ka/Ni/Siho→Event/Fact/Property/Amount/Concept, Poi/Noi→Restrictive/Incidental,
Ei/Ehe→Obligation/Permission, GanaiGi/GeGi→Implies/And, Tanru→Pair, ModalTag::Fio→
Custom), and `AstBuffer.selbris`/`.sumtis`→`predicates`/`arguments`. The audit CLEARED
`question_vars`, the presupposition-witness machinery, du-equality, elidable-terminator
logic, and `Sentence::Prenex` as load-bearing (kept); xorlo existential import KEPT by
user choice. Zero reasoning-behavior change — determinism corpus + Vampire/clingo
oracles + verify-nibli-kr-seam unchanged. The da/de/di 3-variable `$var` lowering cap
(`VAR_NAMES`) was a Lojban-shaped limit the predicate-name bullet has since LIFTED (milestone below).

**GRAMMAR-STRUCTURE IDENTIFIERS: LANDED (2026-07-13, next bullet after the vestige
audit, 2 commits).** The lowercase identifiers built on the flat-AST vocabulary were
renamed to the English of the types they name — `bridi`→`proposition`,
`selbri`→`predicate`, `sumti`→`argument`, `tanru`→`pair` — across nibli-kr/src +
nibli-semantics/src + nibli-types comments (private methods, params, ~40 `let bridi =
Proposition{…}` fixtures, test names, descriptive panic/error messages), plus the
`mod selbri`→`mod predicate` submodule + file rename (`selbri.rs`→`predicate.rs`) and
the README/pest comments. Then (user "Option B") nibli-kr's grammar-emission HELPERS,
so the crate has ZERO Lojban production identifiers: `var_cmavo`/`keyterm_cmavo`→
`var_particle`/`keyterm_particle`, and the `gismu` local/param/fn identifiers
(`head_gismu`/`resolved_gismu`/`gismu_parts` + the `let gismu`/`Predicate::Root(gismu)`
bindings)→`word`-based English — while KEEPING the `AliasEntry.gismu` FIELD access
(cross-crate public API) and every gismu/predicate-name string VALUE. Pure,
compiler-guided rename; zero wire/serialization/public-API/behavior change (verified —
methods private, protocol/store/engine carry none of this vocab, no dictionary VALUES
in the two crates).

STILL DE-LOJBANIZING (a holistic identifier/comment pass — cosmetic, post-flip): the
word-class vocabulary as identifiers (`gismu`/`cmavo`/`lujvo`/`cmevla` build locals, the
`GISMU_GLOSS_OVERRIDES`/`GISMU_PLACE_TEMPLATES`/`CMAVO_GLOSS_OVERRIDES` consts, the
cross-crate-public `GISMU_TO_ALIAS` + `AliasEntry.gismu`), the `?`/`it`/`slot`→`ma`/
`ke'a`/`ce'u` output strings + da/de/di variable pool, `xorlo`/`goi` named-feature test
names, and the broader-cmavo (poi/fa/fio/giha/du) comments + test-fn names in the OTHER
crates (nibli-reason/render/host/formalize/engine/verify). The predicate-name VALUES (IR
strings, proof-trace output, the wire protocol, da/de/di, du, zo'e) are DONE (milestone below).
**DICTIONARY FOLD: LANDED (2026-07-13, 2 commits).** `nibli-kr-dictionary` folded
into `nibli-lexicon` and deleted. The merged `nibli-lexicon/build.rs` parses
`dictionary-en.json` ONCE, building `DICTIONARY` + an in-loop `arity_map`
(`word->Option<usize>`) in the forward-dict loop, then the moved alias-generation pass
consumes `arity_map.get(w).copied().flatten()` in place of the old cross-crate
`nibli_lexicon::get_arity` build-dep — so alias↔dictionary arity agreement now holds BY
CONSTRUCTION (the cross-crate drift class is gone). curated/label/reserved + the alias
API (`alias`/`canonical_alias`/`label_index`/`AliasEntry`/`ALIASES`/`GISMU_TO_ALIAS`)
moved into nibli-lexicon; the 18 unit tests came with them. Decided ALWAYS-ON (no
`alias-map` feature): the recorded feature-gate's rationale (keep the alias map out of
the web bundle) turned out MOOT — nibli-kr already ships it into wasm/pipeline — and a
feature would have added a silent test-coverage trap for near-zero benefit. Consumers
repointed `nibli_kr_dictionary::`→`nibli_lexicon::` (nibli-kr regular dep; nibli-ui's
`#[cfg(test)]` probe switched to `DICTIONARY.len()` and dropped its dep; nibli-verify
gate repointed, its now-vacuous mixed-mode check removed). Recipes renamed
`test-nibli-kr-dict`→`test-alias-map`, `verify-nibli-kr-dict`→`verify-alias-map`. Zero
shipped-behavior change — verify-alias-map + verify-nibli-kr-seam + full ci green in
BOTH dictionary modes.
**GRAMMAR+DICTIONARY-GROUNDED FORMALIZE PROMPTS: LANDED (2026-07-13).** The Formalize
system prompt now embeds the ACTUAL grammar + dictionary instead of nine few-shots:
`nibli-formalize/src/llm/system_prompt.rs` assembles it ONCE via `LazyLock` from the pest
`nibli_kr::GRAMMAR` (in-sync by construction) + a distilled §4/§6/§7 semantics block +
the FULL shipped `nibli_lexicon::ALIASES` map rendered `alias(places…) — predicate` +
the few-shots. `system_prompt()` keeps its `&'static str` signature (the map is
compile-time → source-independent), so all three nibli-ui LLM paths + the agentic loop
are untouched. Dual-mode automatically (full ~1,341-alias map / curated core in
fallback). User chose the FULL map (not a per-source subset). Two guards: few-shots
stay gate-valid + the assembled prompt embeds the grammar and ≥65 alias lines. The
empirical attempts-to-converge measurement (part (c) of the old note) is an EVALUATION
that belongs to the adoption / non-expert authoring study (Roadmap ceiling), not engine
code — done here is the grounding itself.
**PREDICATE-NAME DE-LOJBANIZATION: LANDED (2026-07-14, A→D commit series).** The canonical
predicate + variable namespace flipped from gismu to English, so **proof traces contain no
Lojban**. The seam: `nibli-kr/src/emit.rs` resolves each alias to its ENGLISH `canonical_alias`
(not `entry.gismu`) at compile time — content + arithmetic/comparison predicates flip together
(`gerku`→`dog`, `pilji/sumji/dilcu`→`product/sum/quotient`, `zmadu/mleca/dunli`→`greater/
less/num_equal`, `tenfa/dugri`→`exponential/logarithm`); nibli-semantics gains an English-keyed
arity fallback so event-decomposition survives; the reasoner + the two soundness oracles + the
compute wire (`python/nibli_backend.py`, a versioned break) re-key in lockstep. The hardcoded
markers went English too: `du`→`equals`, `zo'e`→`something`, the abstraction type names
`nu/duhu/ka/ni/siho`→`event/fact/property/amount/concept`, and the `$var` names pass through
verbatim (no da/de/di pool → the spec-O1 3-variable cap is GONE). Role predicates gained
ARGUMENT-name display (`goes_x2`→`goes.destination`) at the render layer (the IR keeps
`<rel>_x<N>`). Zero verdict change — only strings moved; the Vampire/clingo differential, the
determinism corpus, the seam gate, and the Lean proofs (all pin verdicts) stayed green in BOTH
dictionary modes (fallback needed one fix — `dugri` added to the curated fallback dictionary so
the `logarithm` alias resolves there too). Sub-item fates: (e) redb stores are gitignored (fresh
persists are already English — nothing in-repo to migrate); (g) verify-dict needed no bridge (the
lexicon FORWARD dict stays gismu-keyed; only emit OUTPUT flipped); (h) the lexicon is still BUILT
from the lensisku dump — accepted as an invisible build-time input.

- **Residual user-facing Lojban (cosmetic; proof-trace VALUES are already English)** — two
  narrow surfaces still show Lojban to the user, for a follow-up: (a) the **argument-pronoun
  cmavo** the emitter produces — `me`/`you`/`it`/`?`/`slot`/we-all/anaphora lower to
  `mi`/`do`/`ke'a`/`ma`/`ce'u`/`ma'a`/`ko'a` (`nibli-kr/src/emit.rs` KeyTerm + `Term::Witness`
  arms), surfacing in witnesses and `?`-finds; (b) the §12 **L4 alias-echo lint**
  (`nibli-kr/src/lint.rs`) still prints `dog ↦ gerku` — now stylistically stale (the IR relation
  is the English `dog`); its genuine value (a converted alias silently reroutes args) survives
  only for SWAPPED aliases, so rework to a Lojban-free converted-swap-only note (ripples into the
  acceptance-corpus L4 test + the §12 book catalog).
- **demo site migration (cross-repo, dhilipsiva.dev — SEPARATE Claude session)** —
  the copy-pastable prompt was handed to the user 2026-07-12. URGENCY UP since THE
  DROP landed (2026-07-13, user-accepted): the deployed /nibli demo is BROKEN —
  its Lojban-era KBs no longer compile against main. Site session scope: /nibli
  guided demo KBs+queries+copy → nibli KR. The engine side is DONE: nibli-wasm is
  KR-only; `set_language` is a deprecated NO-OP shim (any string accepted, so
  the prompt's `set_language("klaro")` instruction still works) and
  `back_translate` survives as a deprecated gloss shim. The "Klaro"→"nibli KR"
  rename milestone LANDED without deleting them (the deployed site still calls
  them); both DELETE here, in this session, once the site stops calling them. If the site needs the old
  engine meanwhile, pin the `v0.1-lojban-final` tag in `build_nibli.sh`.

Engine bullets (language-independent; the KR program above takes precedence):

- **Ontology-row import (brismu/zatske interchange)** — korvo proposed flat rows
  `[P, Q, mapping]` (predicate subrelation with place mapping: identity
  `["gerku","danlu",[1,2]]`; place deletion `["skari","ckaji",[1,2]]` — unmapped
  source places dropped; permutation `["lanzu","cmima",[2,1]]`) as the interchange
  format between brismu / zaha / zatske and downstream consumers (2026-07-05 Lojban
  Discord #proga thread; korvo confirmed rows are "a good compromise"). Build an
  importer beside `nibli-import/src/rdf.rs`/`owl.rs`: each row compiles to one
  monotone Horn rule at the IR level (event decomposition — mapping is a role
  renaming, deletion = roles absent from the head), arity/place validation against
  the lexicon (strict-mode rejection semantics), per-row source/provenance field
  surfaced in proof traces, curated Vampire differential cases for the three row
  shapes, plus mutual-row (equivalence) cases like dugri/tenfa — positive cycles
  legal, fuel-bounded. BLOCKED on korvo pinning the row schema + publishing a
  baseline export. Spec feedback already sent in-thread: the mapping-list direction
  is ambiguous (a 3-cycle case pins it), and rows want a source field for
  provenance. POST-PIVOT NOTE: rows arrive keyed on gismu (they come from the
  Lojban community's tools) — once the predicate-name flip lands, the importer maps
  them through the frozen gismu→canonical-name bridge (the same table the Predilex
  gate keeps); the importer itself is language-independent.
- **logji: upgrade the reversed material-conditional arm (`Or(Q, Not P)`)** — a
  negation on the RIGHT operand of an asserted disjunction (KR:
  `goes(me) | ~eats(me).`) registers a conditional whose condition templates carry
  the assertion's own event-Skolem CONSTANTS, so it can never unify with a later
  assertion's fresh event Skolem — the rule is inert (modus ponens never fires;
  completeness-only, never unsound; adversarial-review finding 2026-07-10, found
  via the Lojban `.i ja … na` spelling — the same IR shape is reachable from KR).
  The forward arm (Not-on-left) was upgraded to `compile_forall_to_rule` (ev__
  pattern vars) precisely for this; mirror it in the reversed arm
  (`register_ground_material_conditional`, logji kb.rs) and add the
  `Q→P + Q ⊢ P` engine test the adversarial review used to confirm the gap.
- **Determinism corpus: add a negative-conjunct line** — the corpus predates the
  shape: add an `A & ~B.` assert + contradiction-check sequence (KR spelling) so
  all three runtime surfaces pin it (requires re-pinning the corpus verdicts on
  native + Wasmtime + node, and regenerating the twin while the twins gate lives).
  The GIhA legs of the original bullet went to fanva's tracker with gerna.
