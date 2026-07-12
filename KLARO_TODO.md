# KLARO TODO

The Klaro drop-in-replacement program tracker. Plain bullets, never numbered — work the
FIRST remaining bullet; cross-reference items by name. Delete a bullet entirely when it
fully lands; update it if only partially done. The language is specified in
`SURFACE_SYNTAX.md` (v0.1 compat profile §1–§13 = what this program implements; §14
clean-core v2 is the follow-on program that triggers gerna retirement). Program
decisions (2026-07-12): dual front-end until gerna retires — Klaro becomes the
primary/default language everywhere, gerna demoted to the equivalence battery + legacy
`.lojban` load; FULL alias-map generation (~1,338 gismu) from day one; every bullet
lands independently CI-green.

- **klaro parser completion + resolve** — rel clauses (`where`/`also`; bare-predicate
  sugar tries Claim branch first; mandatory-`it` static check: full-claim body with zero
  `it` = parse error), abstractions (`event/fact/property/amount/concept { }`),
  tanru + `[ ]` grouping + `a+b` compounds, `.label` place selectors, linked args on
  restrictors, `via` modal tags, block determiners (`every dog $d: …`), `all $x,$y:`
  prenex. `src/resolve.rs` static pass: ≤3 distinct `$vars` per scope (da/de/di lowering
  cap — reject the 4th with a clear error, never merge), place refill/overflow, `it`
  only in clause bodies / `slot` only in `property{}`, name resolution
  (klaro-dictionary alias → gismu+swap+labels; identity passthrough when
  `smuni_dictionary::get_arity(name).is_some()`; otherwise COMPILE ERROR — the
  deliberate tightening over gerna's arity-2 default).
- **klaro emitter + parse_checked** — `src/emit.rs` tree→`nibli_types::ast::AstBuffer`
  (mirror gerna's Flattener discipline, gerna/src/lib.rs:134-152: child indices from
  push-return values). Emission map per the design review: `$x`→ProSumti da/de/di,
  `?`→ma, `it`→ke'a, `slot`→ce'u, named args→`Tagged(Fa..Fu)`, aliases with
  swap→`Selbri::Converted`, linked args→`Selbri::WithArgs` with Unspecified gap-fill,
  operators at SENTENCE level (`Afterthought`/`GanaiGi`), block determiners via
  `Prenex + GanaiGi`/`GeGi` (gerna rejects description gi'e heads — shape pinned by the
  seam gate, spec O7). Public API mirrors gerna: `parse_text` + fail-closed
  `parse_checked(text) -> Result<AstBuffer, NibliError>`; NO goi step. Dev-dep `smuni`
  golden tests: every emitted buffer is accepted by `compile_from_gerna_ast` (its
  `validate_ast_buffer` is the designed-for hand-built-buffer path). Pin the spec-errata
  reject decisions with error-message tests: `~(compound)`, `~` over a prefixed claim
  (`~past P` — `Not(Past P)` is inexpressible, smuni emits `Attitudinal(Tense(Not(…)))`),
  prefixes over compound atoms (`past (A & B)`).
- **klaro renderer + parity guard** — NOTE (naming decision 2026-07-12, honest-generic
  only): reconcile the SURFACE_SYNTAX §16 acceptance spellings to the shipped alias set
  when `klaro/tests/acceptance.klaro` lands — domain-flavored names never enter the core
  map (`consents`→`approves`, `inhibits`→`prevents`, `breached`→flawed-family,
  `at_risk`→`dangerous`, `takes`→`uses`, `rises`→`increases`; also `obliged` is bilga's
  plain alias — `obligates` would invert x1's role — and `obligated` is the ⟨1↔2⟩
  converted form). `src/render.rs`: `render(&AstBuffer) ->
  Result<String, NibliError>` with ZERO wildcard arms over every `nibli_types::ast` enum
  (Sumti, Selbri, Sentence, SentenceConnective, Gadri, AbstractionKind, RelClauseKind,
  PlaceTag, BaiTag, ModalTag, Conversion, Connective, Tense, Attitudinal) — a new AST
  variant breaks klaro's build until covered: this is parity layer 1 of the 100%-sync
  guarantee. Plus `__ast_parity_guard` modeled on
  `nibli_types::logic::__exhaustiveness_guard` (nibli-types/src/logic.rs:381-425) with
  the new-variant obligation checklist in its doc comment. Fails closed (named error) on
  §10 out-of-scope constructs (`ri/ra/ru`, `ko`, unresolved go'i, non-Root la-selbri,
  f64s whose Display needs exponent/sign form). Render∘parse fixpoint tests over
  `klaro/tests/acceptance.klaro` (the SURFACE_SYNTAX §16 set, checked in — also the fuzz
  seed).
- **nibli-verify klaro gates (seam + battery)** — `klaro` becomes a regular nibli-verify
  dep; new `src/klaro_battery.rs` (round-trip helper + `CONSTRUCT_INVENTORY: one row per
  spec §3–§9 construct { spec_section, klaro, lojban: Option }` — parity layer 2, with
  per-section non-vacuity floors) + new test binary `tests/klaro_gate.rs` (oracle-free,
  never skips) holding BOTH gates. `klaro_seam_conformance`: golden FOL structure for
  klaro-only spellings — named args land in the right role predicates, `.label`
  selector ≡ se-shape, block determiners (pins spec O7), `no dog` ≡ exactly-0 CountNode,
  linked-arg Unspecified gap-fill, `a+b`, independent `?` witnesses, THE O3 PIN
  (`must past P` → `Obligatory(Past(…))` root — verified against
  smuni/src/semantic/compile.rs:358-383), precedence goldens; metamorphic pairs
  canonicalized (named≡positional≡alias-permuted≡direct-gismu); fail-closed negatives
  (unknown name, 4th `$var`, refill, label beyond arity, `it`-less clause body, `slot`
  outside property, the three reject decisions). `klaro_lojban_translation_battery`:
  corpora lines + `generator::random_case` seeds + `seam::conversion_pair` → gerna AST →
  `klaro::render` (failure = gate failure: render totality is parity layer 3) →
  `klaro::parse_checked` → smuni both sides → `seam::canonicalize` LogicBuffer equality
  (NOT AstBuffer equality — §11's deliberate collapses make that unachievable; emitter
  must match gerna's And/Or association order, battery failures there are emit.rs bugs).
  Vocabulary discipline: fallback-dictionary-safe so the gates never need
  dictionary-en.json. Justfile `verify-klaro` recipe; JOIN `ci` (Justfile:471).
- **alias-map differential gate** — new test binary
  `nibli-verify/tests/alias_differential.rs` (verify-dict's dual-mode contract: full
  local build checks all aliases, CI fallback checks the curated core with a FALLBACK
  banner; never skips): (1) every `AliasEntry.gismu` exists in smuni-dictionary with
  equal arity — the two independently-built phf maps cannot drift. KNOWN PRE-EXISTING
  FLAP this gate's CI (fallback) leg will hit: smuni's own `FALLBACK_GISMU_ENTRIES`
  says dilcu=3 and jmive=1 while its full lensisku build derives 4 and 2 (found
  2026-07-12 by klaro-dictionary's build-time drift guard; klaro's curated arities
  follow the FULL-mode values). Fix smuni's fallback table / CORE_GISMU_ARITIES pins
  as part of this bullet — that is a smuni-dictionary + verify-dict-adjacent change; (2) round-trips
  `GISMU_TO_ALIAS→ALIASES→gismu`, swap∈2..=arity, swap twice = identity; (3) no alias in
  `RESERVED_WORDS`, label validity re-asserted from the shipped map; (4) BEHAVIORAL leg:
  `alias(a, b)` via klaro+smuni ≡ direct-gismu Lojban via gerna+smuni at canonicalized
  LogicBuffer level; (5) full-mode coverage floor. Justfile `verify-klaro-dict`; JOIN
  `ci`.
- **fuzz_klaro target** — fuzz/Cargo.toml (workspace-excluded) gains `klaro` + `smuni`
  deps and `[[bin]] fuzz_klaro` → `fuzz_targets/fuzz_klaro.rs`: parse arbitrary UTF-8;
  when parse succeeds, `smuni::compile_from_gerna_ast` must NEVER report a corrupt AST
  buffer (klaro handing smuni a structurally invalid buffer is a klaro bug — assert on
  the error class). Extend `fuzz-seed` (Justfile:675) with `fuzz/corpus/fuzz_klaro/`
  from `klaro/tests/acceptance.klaro` + the `.klaro` corpus twins once they exist.
  Recipe `fuzz-klaro` cloned from `fuzz-parse`; join `fuzz-ci`.
- **Language enum + engine dispatch (default still Lojban)** — `nibli-types/src/lang.rs`:
  `Language { Klaro, Lojban }` + FromStr/Display (introduced defaulting to LOJBAN; the
  default flips in THE FLIP bullet). NibliEngine: `Cell<Language>` + `set_language`/
  `language` (the `set_strict` precedent, nibli-engine/src/lib.rs:99-111); two-arm match
  in `compile_text` (lib.rs:220); KLARO COMPILES SKIP GOI RESOLUTION AND CLEAR THE
  PRIOR-BRIDI SNAPSHOT (`last_relation = None` — a later Lojban `go'i` fails closed
  "no prior bridi", never silently repeats something older). `reset()` does NOT clear
  the language (configuration, like verbose). Unit tests both modes + the goi-clear.
  Zero behavior change for existing callers.
- **native REPL surfaces** — nibli REPL (nibli/src/main.rs): `:klaro`/`:lojban` commands
  → `engine.set_language`, `:load` picks language by file extension (`.lojban`→Lojban
  for the file, restore after; `.klaro`→Klaro; else current mode), `NIBLI_LANG` env at
  startup, `:help` text. `nibli-validate --lang lojban` flag + NIBLI_LANG (default
  follows engine default). `nibli-import --lang` for `--query`; DECIDE the English-RDF
  queryability escape hatch: (a) raw-identifier passthrough into the AstBuffer (smuni's
  unknown-word fallback applies — minimal, recommended for now) vs (b)
  `register_predicate_alias(name, arity)` (the v2 schema-registry seam pulled forward);
  without one, Klaro's unknown-name compile error makes the import query limitation
  STRICTER, not dissolved — rewrite the import.rs:13-15 doc note accordingly.
- **corpora twins + honesty gate** — `klaro/src/bin/lojban2klaro.rs` + `just
  migrate-corpora`: line-by-line, comments/blank lines/`# =>` verdict annotations/
  `?`/`??`/`:`-prefixes preserved byte-for-byte at identical line numbers, payload =
  `gerna::parse_checked` → `klaro::render`; RE-RUNNABLE (corpora still change while
  gerna lives). Generate the four twins: `gdpr.klaro`, `drug-interactions.klaro`
  (the source file is `drug-interactions.lojban`), `determinism-corpus.klaro`,
  `readme.klaro`. New gate `verify-klaro-twins` (nibli-verify test + recipe, JOIN `ci`):
  twin existence both directions, line-structure correspondence, per-payload-line
  canonicalized compiled-buffer equality — this IS the shipped-corpora leg of spec §13
  obligation 3 and makes the dual phase self-policing. MUST LAND BEFORE any further
  corpus edits (the pending TODO.md determinism-corpus GIhA bullet edits a twinned
  file). Also add `determinism_corpus_klaro_native` beside (not replacing) the Lojban
  native leg.
- **THE FLIP (native)** — `Language::default()` → Klaro. Mechanical sweep: grep
  `NibliEngine::new()` workspace-wide; nibli-engine tests (integration.rs ~159 Lojban
  call sites + verdict_corpus + known_failures*) switch to a `lojban_engine()` helper
  (`new()` + `set_language(Lojban)`) — do NOT translate their text, the twin gate makes
  Klaro duplicates redundant; new engine tests are written in Klaro. Corpus-pinned tests
  (gdpr/ddi integration, nibli-verify `corpora.rs` consts) re-point to `.klaro`. Native
  determinism leg re-points to `.klaro`; keep `determinism_corpus_lojban_twin` (deleted
  at retirement). `bench_book` pinned `set_language(Lojban)` explicitly (book-quoted
  timings stay Lojban until the book migrates). `verify-book` recipe passes
  `--lang lojban` to nibli-validate. `fuzz-seed` gains the `.klaro` sources for
  fuzz_assert/fuzz_query.
- **WIT + lasna + gasnu (ONE commit — bindings regen atomicity)** — wit/world.wit:
  `enum language { klaro, lojban }` + `set-language: func(lang: language)` on the
  session resource (the set-strict pattern; leave the `lojban:nibli@0.1.0` package id
  alone). lasna: `klaro` internal crate dep, `Cell<Language>` on Session, `NIBLI_LANG`
  read in `Session::new` beside NIBLI_QUIET/NIBLI_STRICT (lasna/src/lib.rs:484-491 — so
  post-trap rebuild restores the mode), dispatch + goi-clear in `compile_pipeline`
  (lib.rs:367). gasnu: `lang` field on Repl (NIBLI_LANG at startup),
  `instantiate_session` forwards `b.env("NIBLI_LANG", …)` (rebuild-safe),
  `:klaro`/`:lojban`/`:lang` commands, `:load`/`--script` extension rule, `:help`.
  Journal needs NO language entry (replay is buffer-level). Smokes: migrate the runtime-
  behavior smokes' printf payloads to Klaro (script, trap-recovery, persist-replay,
  split, naf, cwa-false, debug, collapse, backend-unavailable, non-finite, quiet,
  strict) — `smoke-gasnu-split` doubles as the pin that Klaro `.`-statement splitting ≡
  bare-`.i` `split_roots` granularity; keep the seven goi smokes Lojban by prepending
  `:lojban\n` to their payloads; add `smoke-gasnu-script-lojban` (current script smoke
  verbatim under `:lojban`) + one mixed-mode smoke (Klaro assert → `:lojban` →
  `? go'i` fails "no prior bridi"); `smoke-gasnu-determinism` → `.klaro`. COORDINATE
  FIRST (cross-repo risk): book capture harness pins `NIBLI_LANG=lojban` before this
  lands, or verify-book-capture silently rots.
- **nibli-wasm + V8 leg** — `set_language(&str)` wasm-bindgen export; dispatch in
  `Session::compile_text` + `compile_for_render` (nibli-wasm/src/lib.rs:104,140);
  determinism.rs + gdpr/ddi bounded-time tests → `.klaro`. LIVE-DEMO COORDINATION: ship
  the export first with default still Lojban here, flip the wasm default only in the
  same window as the dhilipsiva.dev site-repo JS/KB migration (redeploy-site.yml
  auto-triggers on push to main — an uncoordinated default flip breaks the deployed
  playground).
- **nibli-ui + nibli-fanva** — fanva gates take `Language` (gates.rs:59): Klaro arm =
  `klaro::parse_checked` (gate name "klaro") + smuni + a RENDER ROUND-TRIP gate
  (render∘parse must reproduce the AstBuffer — the drift-catcher replacing camxes, which
  is Lojban-only and stays for legacy mode); `feedback_for` arm; per-language
  `GATE_ORDER` (["klaro","smuni","round-trip"] vs ["gerna","smuni","camxes"]). New
  `KLARO_SYSTEM_PROMPT` (English→Klaro few-shots — far simpler prompt) + duplicate the
  `shipped_examples_are_gate_valid` guard test against the Klaro gates. verify.rs
  unchanged structurally (IR-level back-translation) — just the lang thread-through +
  neutral prose in VALIDATOR_SYSTEM_PROMPT. jbotci McpClient constructed ONLY in Lojban
  mode (fanva-proxy becomes legacy-only — strengthens the existing retire-fanva-proxy
  TODO bullet). nibli-ui: examples.rs `include_str!` → `.klaro` twins, `DEFAULT_LOJBAN`
  → Klaro syllogism, `ActiveTab::Lojban` → `ActiveTab::Kb` with language-driven label,
  legacy-Lojban input toggle in settings (default Klaro), Translate targets the KB
  language, camxes `<script>` tags stay (legacy mode). Keep examples.rs `source`/
  `queries` labels STABLE (book Ch 19 quotes them verbatim — two-repo desync has no
  gate).
- **docs sweep** — README leads with Klaro (readme.klaro transcripts; legacy-Lojban
  section), CLAUDE.md (crate table + command table + this program's status), GUARANTEES
  front-end section, WIT doc comments ("Assert Lojban text…"), gasnu/nibli `:help`
  strings audit, LOJBAN_COVERAGE.md marked legacy-scope, SURFACE_SYNTAX.md status line →
  implemented-v0.1.
- **lint catalog L1–L7** — non-blocking compile notes per SURFACE_SYNTAX §12; L4 (alias
  echo: resolved gismu + permutation on first use per file/session) and L5 (integrity-
  constraint registration echo) first; L1 the-trap, L2 tanru-vs-`&`, L3 multi-quantified-
  args scope warning, L6 tense×NAF advisory (`past ~P` only — `~past P` is rejected),
  L7 must/may-vs-obligated/permitted mixing.
- **gerna retirement (execute at clean-core v2 divergence — not before)** — ALL of:
  first v2 semantic decision landed (xorlo flag off or schema declarations in; see
  SURFACE_SYNTAX §14); book repo migrated or pinned (`NIBLI_LANG=lojban` /
  `--lang lojban` in capture+verify tools); live demo migrated; no active store relies
  on legacy TEXT replay (`assert-text-with-id` — buffer replay is language-free). Then
  delete in one milestone: gerna crate, verify-parser + parser_diff.rs + vendored camxes
  (nibli-ui/assets/js/vendor/camxes/), gerna::goi + both `last_relation` snapshots + the
  7 goi smokes + smoke-gasnu-script-lojban + determinism_corpus_lojban_twin, the
  `.lojban` twins + verify-klaro-twins, `Language::Lojban` + the WIT enum arm (one more
  bindings regen), jbotci MCP tools + fanva-proxy, python/lojban_classifier tooling,
  LOJBAN_COVERAGE.md. smuni-dictionary/lensisku retire separately per §14.1 (schema
  declarations). Clean-core v2 itself is the follow-on program — spec §14 is its
  requirements doc.
