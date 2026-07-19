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
proof-trace output, redb keys) were the predicate-name de-Lojbanization bullet — since
LANDED (milestone below). `nibli` survives.

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

**MECHANICAL IDENTIFIER REFACTOR: LANDED (2026-07-17, 3 commits — the last
de-Lojbanization pass; book/TODO.md timing gate 4(b) CLEARED, so the book migration is
unblocked).** Every remaining Lojban identifier in CODE went English: the `logji_logic`
alias (~78 sites) → `logic`, `fanva_translate` → `formalize_translate`, the du-named
source fns → equals (`flat_equals_pair`, `equals_substitution_note`, the
`ProofRule::EqualitySubstitution.equality_facts` field — same-build-safe serde key),
the write-only abstraction-key canon tags (pu/ca/ba/ei/ee → past/now/future/oblig/perm),
and **`le_domain_` → `the_domain_`** (user-approved emitted-IR string change; contained
to nibli-semantics — no corpus/golden/cross-crate pin). ~91 test-fn names + ~60
test-locals renamed per construct (du→equals, xorlo→existential-import as a set,
giha→conjoined_tails, ganai→implication, poi/noi→where/incidental, fio→via_modal,
se/te/xe→x2/x3/x5_conversion, content words→corpus names;
`kr_semantics_seam_conformance`, `load_corpus_like_host`). Comment sweep: the
logji/smuni/lasna/gasnu/gerna codenames → crate names across all crates (quote-aware —
string VALUES protected; `smuni`/`gerna` are ALSO corpus provenance values), stale
PHF/dual-mode/go'i-era comments rewritten, the `.nibli` corpus headers de-Lojbanized
(comment-only; `# =>` verdict annotations untouched), proofs/*.lean `logji/src` paths →
`nibli-reason/src`, the Formalize gate chip label "smuni" → "semantics"
(`GateError::gate()` + `GATE_ORDER` moved together), LOGIC_IR/NIBLI_KR/GUARANTEES
follow. DELIBERATE RESIDUALS: `source_gismu`/`by_provenance(gismu)` + lexigen
(sanctioned provenance API), `"gasnu-local"` store namespace (persisted-store
compatibility), the gismu STRING fixtures in nibli-reason's flat tests (arbitrary
relation names that must NOT resolve — an English spelling would flip
`SignatureSource`) and the formula-gloss comments that document those fixtures
(kept consistent with the strings), and explicit-history notes (THE DROP, xorlo-rule
provenance at canonical definition sites).
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

**RESIDUAL USER-FACING LOJBAN: LANDED (2026-07-17, 3 commits).** The last Lojban a user
could see is gone. (a) The pronoun constants flipped to their KR spellings — the emitter's
keyterm table now writes `me`/`you`/`we`/`this`/`it_a`… verbatim into the IR, and the
three consumed markers are `?` (witness, fresh var per occurrence), `it` (bound entity),
`slot` (open place); the recognition sites (nibli-semantics resolve_argument + the
explicit-`it` scan) and the render reverse map (now an identity whitelist) re-keyed in
lockstep. NEW fail-closed guard (user decision): a single-word capitalized Name that
lowercases onto a pronoun constant ({Me,You,We,This,That,Yonder}) is a compile error —
it would silently co-refer with the pronoun (compound names are safe: `We_All`→"we all").
The dead render `zo'e`→`_` arm deleted (was silently meaning-changing); the ce'u/ke'a
USER-FACING ERROR TEXTS went English ("`slot` outside a `property { }` abstraction",
"use an explicit `it`"). (b) The §12 L4 lint fires ONLY for converted aliases and speaks
English: `metabolized_by ↦ cuts⟨x1↔x2⟩` (the canonical base + permutation — the note's
real value, disclosing argument rerouting; plain aliases resolve to themselves and went
quiet). Witnesses/traces read `goes_x1(_ev0, me)`, `[Find]  = adam`. Zero verdict
change; full ci green in BOTH dictionary modes; book/TODO.md timing gate 4(a) is CLEARED
(4(b), the identifier refactor below, still pending).
**COMMITTED ENGLISH CORPUS: LANDED (2026-07-17, 6-commit series).** The dictionary IS
Rust source: nibli-lexicon's build-time lensisku parse replaced by the COMMITTED
strongly-typed corpus (`src/corpus/predicates.rs`, ~1,342 English-keyed
`PredicateEntry` rows — arity = places.len(), EVERY place named, zero positional;
`source_gismu` a provenance FIELD only; `Swap{with,base}` types the converted link) +
curated `CompoundEntry` seeds. build.rs, phf, the fallback tables, the cmavo layer, and
the FULL/FALLBACK dual-mode all DIED — ONE build mode forever (CI flipped to full
coverage with zero workflow edits; the site build needs no dictionary fetch). Const-eval
validation + `#[test]` twins guard the invariants fail-closed; machine-guessed places
carry `TODO(corpus)` markers with a count ratchet (baseline 1,278). Gismu spellings
STOPPED resolving (`klama(...)` = compile error; the Predilex/taxonomy gates re-key
through the permanent `by_provenance` bridge — 132/39 checked, floors 120/35). `a+b`
compounds resolve ONLY via committed entries and emit their relation ident
(`computer_user`); `Predicate::Compound` deleted (its silent last-part-only semantics
was a meaning trap); the L4 lint echoes the committed structure on first use.
`tools/lexigen` (`just regen-lexicon`) is the report-only regeneration path —
`fetch-dict` survives solely as its input. nibli-wasm's `back_translate` → echo no-op
(deletion rides the site-migration bullet). Zero verdict drift across the series: full
ci + ci-wasm green per commit (determinism corpus pinned identically on
native/Wasmtime/V8).

Engine bullets (language-independent; the KR program above takes precedence).
Pipeline-audit backlog (2026-07-17; three-agent audit of front-end / middle IRs /
back-end — effort tags S/M/L; ordered quick-wins → correctness → structure →
performance → future-facing):

- **Determinism corpus: add a negative-conjunct line** — the corpus predates the
  shape: add an `A & ~B.` assert + contradiction-check sequence (KR spelling) so
  all three runtime surfaces pin it (requires re-pinning the corpus verdicts on
  native + Wasmtime + node, and regenerating the twin while the twins gate lives).
  The GIhA legs of the original bullet went to fanva's tracker with gerna.
