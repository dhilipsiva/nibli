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

- **site-window residual (cross-repo, /nibli demo)** — the nibli-wasm session DEFAULT
  flip (Lojban→Klaro) + `back_translate_ir`'s Klaro render path (`compile_for_render`
  is already language-parameterized — a one-arg flip) ride the dhilipsiva.dev
  site-repo JS/KB migration of the **/nibli guided demo** page (distinct from the
  /nibli-playground, which migrated to Klaro with the nibli-ui bullet 2026-07-12;
  redeploy-site.yml auto-triggers on push to main). Execute when that page's JS/KB
  goes Klaro; also unblocks the book's Formalize copy sweep (book/TODO.md).
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
