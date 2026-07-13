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
proof-trace output, redb keys) stay — that is the predicate-name de-Lojbanization
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
(`VAR_NAMES`) remains — a Lojban-shaped limit the predicate-name bullet lifts.

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

STILL DE-LOJBANIZING (predicate-name / dictionary bullet + a holistic pass): the
word-class vocabulary as identifiers (`gismu`/`cmavo`/`lujvo`/`cmevla` build locals, the
`GISMU_GLOSS_OVERRIDES`/`GISMU_PLACE_TEMPLATES`/`CMAVO_GLOSS_OVERRIDES` consts, the
cross-crate-public `GISMU_TO_ALIAS` + `AliasEntry.gismu`), the `?`/`it`/`slot`→`ma`/
`ke'a`/`ce'u` output strings + da/de/di variable pool, `xorlo`/`goi` named-feature test
names, and the broader-cmavo (poi/fa/fio/giha/du) comments + test-fn names in the OTHER
crates (nibli-reason/render/host/formalize/engine/verify). PredName VALUES stay for the
predicate-name bullet.
- **Fold nibli-kr-dictionary into nibli-lexicon (feature-gated)** — user chose to fold;
  deferred from the crate purge as its own isolated, revertable change (a ~500-line
  build.rs merge with dual-mode + alias<->arity-agreement risk, orthogonal to
  de-Lojbanization). Design: nibli-lexicon/build.rs already `#[path="src/arity.rs"]
  mod arity`s; accumulate a `word->Option<usize>` arity_map during the forward-dict
  loop (Some(n) for gismu/lujvo, None for cmavo — exactly what runtime `get_arity`
  returns), then port nibli-kr-dictionary/build.rs's alias generation feature-gated
  (`alias-map`), replacing every `nibli_lexicon::get_arity(w)` with
  `arity_map.get(w).copied().flatten()`. Move curated.rs/label.rs/reserved.rs + the
  alias API (alias/canonical_alias/AliasEntry/GISMU_TO_ALIAS) into nibli-lexicon under
  the feature; nibli-kr/nibli-ui/nibli-verify depend with `features=["alias-map"]`;
  delete the crate + workspace member; update verify-nibli-kr-dict/test-nibli-kr-dict.
- **Grammar+dictionary-grounded Formalize prompts (user decision 2026-07-12)** — the
  Transparency Triad's Formalize system prompt must contain the ACTUAL KR grammar and
  the dictionary, so the LLM formalizes against ground truth instead of nine
  few-shots; the agentic parse-error-feedback loop stays as-is. Design notes:
  (a) GRAMMAR: `include_str!` the pest file (`nibli-kr/src/nibli_kr.pest`, 181 lines /
  ~9 KB ≈ 2.5–3k tokens — affordable, and in-sync BY CONSTRUCTION since the file IS
  the parser); distill the semantics tables the grammar can't carry (determiner
  taxonomy §4, operator/prefix rules §6, `where`/`also` §7) into a compact prose
  block.
  (b) DICTIONARY: the full map is ~1,341 aliases (full mode) — three options,
  decide at implementation: (i) full compact listing (`alias/arity: label1, label2…`
  per line, ~15–20k tokens — BYO-key users pay per request), (ii) curated core +
  the existing fail-closed-retry guidance (today's behavior), (iii) RECOMMENDED
  source-relevant subset: extract content words from the English source, include
  only matching/near aliases + the curated core — best token/accuracy trade. Any
  dictionary embedding means the prompt stops being a `&'static str`: a
  `system_prompt_for(source)` builder assembled at request time from the shipped
  `nibli_kr_dictionary` map (no drift possible; dual-mode — the CI fallback build
  embeds the curated core only, loudly).
  (c) Optimize BOTH prompts (system + the per-request user turn) and measure:
  attempts-to-converge on a fixed English corpus is the metric (feeds the
  authoring-study track). Guard tests: few-shots stay gate-valid (existing twin
  guard), the embedded grammar is the shipped file by construction, the dictionary
  block is generated from the shipped map in the same build.
  Applies to all three nibli-ui LLM paths (agentic Formalize, single-shot query
  formalize, the modal key-test). Sequencing: written after the KR rename bullet so
  the prompt is born saying "nibli KR", but it is independent — pull it earlier if
  wanted.
- **Predicate-name de-Lojbanization (proof traces contain NO Lojban — the deep one)**
  — today every `LogicBuffer` relation is a gismu (`nibli-kr/src/emit.rs:379-387` maps
  alias→`entry.gismu`; smuni derives `gerku_x1`, `le_domain_gerku`; `=` mints `du`
  at emit.rs:192; `$vars` lower to the literal `da/de/di` pool at emit.rs:90-103,
  which smuni string-matches for quantifier closure). DECISION (recommended, and the
  only option satisfying "no Lojban anywhere"): **option A — flip the canonical
  predicate namespace to the English aliases at compile time** (emit
  `canonical_alias` instead of `entry.gismu`; keep the KR alias the user wrote where
  it IS canonical). Scope the obstacles honestly:
  (a) re-key `nibli-lexicon` lookups (arity/gloss/template — logji
  `rules.rs:848`, `nibli-render/src/frame.rs`) by the canonical English names;
  (b) `du` + the compute predicates are load-bearing string literals
  (`logji` union-find keys `"du"`; `default_compute_predicates()` =
  pilji/sumji/dilcu; `nibli-types/src/arithmetic.rs` match arms; `dunli/zmadu/mleca`
  comparisons) AND the backend JSON wire protocol sends them verbatim
  (`{"relation":"tenfa",…}`, `python/nibli_backend.py` HANDLERS) — rename = a
  versioned wire-protocol break (`equals`, `product`/`sum`/`quotient`,
  `power`/`log` …); update the reference backend in the same commit;
  (c) variable names: preserve the user's `$var` spellings through emit instead of
  the da/de/di pool (an AstBuffer-contract change — smuni's
  `matches!(name, "da"|"de"|"di")` closure checks generalize; this also naturally
  lifts the 3-variable cap, spec issue O1) so witnesses read `$x = adam`;
  (d) the `zo'e` display literals are two one-line fixes now
  (`nibli-types/src/logic.rs:50` trace_display, `nibli-render/src/logic.rs:128`) —
  do them early, plus `le {d}`/`lo {s}` display forms;
  (e) persisted redb stores/journals/`:export` hold gismu relations — migration or
  a compat read layer; regenerate `gdpr-auto.redb`/`drug-auto.redb`;
  (f) fallback-mode CI can only rename the curated core (no dictionary-en.json) —
  same dual-mode discipline as today;
  (g) verify-dict (Predilex) keys on Lojban lemmas — keep a frozen
  gismu→canonical-name bridge table so it stays an independent arity oracle;
  (h) DATA PROVENANCE: the lexicon is still BUILT from the lensisku Lojban dump —
  acceptable as an invisible build-time input, or superseded by committed KR schema
  declarations (the old clean-core §14.1 idea) — decide when this bullet starts.
  All pinned transcripts/goldens regenerate (smokes, README capture, seam goldens).
  Also the natural moment to fold in the **ontology-row import** bullet below (rows
  arrive keyed on gismu; the alias bridge from (g) is the same mapping).
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
- **book migration (separate repo — book/TODO.md carries the details)** — the book
  is Lojban-heavy by design ("Lojban as IR" framing, Part II Ch 3–6); the pivot
  replaces it with nibli KR. Key restructuring (user decision): MERGE Ch 3 ("Why
  Not English?") + Ch 4 ("Lojban — A Gift from Linguists, Logicians, and
  Mathematicians") into ONE chapter about the nibli KR language. THE DROP landed
  (2026-07-13): `verify-book` is EXPECTED RED and the capture harness cannot
  run against main until the book re-captures its transcripts in KR — or pins the
  `v0.1-lojban-final` engine tag meanwhile.

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
