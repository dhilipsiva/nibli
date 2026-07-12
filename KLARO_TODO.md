# KLARO TODO

The Klaro drop-in-replacement program tracker. Plain bullets, never numbered — work the
FIRST remaining bullet; cross-reference items by name. Delete a bullet entirely when it
fully lands; update it if only partially done. The language is specified in
`SURFACE_SYNTAX.md` (v0.1 compat profile §1–§13 = what this program implements; §14
clean-core v2 is the follow-on program that triggers gerna retirement). Program
decisions (2026-07-12): dual front-end until gerna retires — Klaro becomes the
primary/default language everywhere, gerna demoted to the equivalence battery + legacy
`.lojban` load; FULL alias-map generation (~1,338 gismu) from day one; parser tech =
**pest** (`klaro/src/klaro.pest` is the executable grammar — the normative §15; the
walker in `klaro/src/parser.rs` builds the tree AST and owns the §6-errata /
arg-ordering / count-integrality rejects with targeted positioned errors); DESIGN
THESIS: Klaro is a human-intuitive knowledge-representation language — maximally
intuitive SUBJECT TO semantic distinctions staying visible in the spelling (the
silent-mistranslation ceiling; LLM-generability is a tracked side goal, measured via
the fanva retarget); the **logji reasoning core stays untouched throughout this
program** — no hard freeze, though: the two contained §14 clean-core items that touch
logji (the xorlo presupposition-witness flag — an assert-time Lojban-fidelity
behavior, not inference — and the compute-set rename) remain LIVE v2 OPTIONS,
exercised only at clean-core after gerna retires; until then Klaro's `every` mints
xorlo witnesses identically to Lojban (compat requires it — the equivalence battery
checks verdict identity) and the behavior is disclosed spec semantics, not hidden
residue; every bullet lands independently CI-green.

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
  language AND IS RENAMED **Formalize** (user decision 2026-07-12: "compile" stays
  reserved for the deterministic KB→logic step; the LLM English→Klaro step is
  interpretive formalization behind gates — never label it "Compile", that would
  launder the one untrusted step with compiler connotations; book copy follows via
  book/TODO.md), camxes `<script>` tags stay (legacy mode). Keep examples.rs `source`/
  `queries` labels STABLE (book Ch 19 quotes them verbatim — two-repo desync has no
  gate).
- **docs sweep** — README leads with Klaro (readme.klaro transcripts; legacy-Lojban
  section), CLAUDE.md (crate table + command table + this program's status), GUARANTEES
  front-end section, WIT doc comments ("Assert Lojban text…"), gasnu/nibli `:help`
  strings audit, LOJBAN_COVERAGE.md marked legacy-scope, SURFACE_SYNTAX.md status line →
  implemented-v0.1.
- **lint catalog L1–L9** — non-blocking compile notes per SURFACE_SYNTAX §12; L4 (alias
  echo: resolved gismu + permutation on first use per file/session) and L5 (integrity-
  constraint registration echo) first; L1 the-trap, L2 tanru-vs-`&`, L3 multi-quantified-
  args scope warning, L6 tense×NAF advisory (`past ~P` only — `~past P` is rejected),
  L7 must/may-vs-obligated/permitted mixing; L8 (O9) echo the innermost-wins rel-clause
  attachment when a clause-body-final equality RHS carries a rel clause; L9 warn when a
  statement's terminating `.` is whitespace-separated from the claim AND the next
  statement starts with a digit (`X = 2 .5 = $y.` silently splits — 2026-07-12 grammar
  review, Finding 3).
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
