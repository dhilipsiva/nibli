# Triad + Proof-Trace readability, consolidated DRY

## Context

Two surfaces that humans read to *verify* the engine are currently low-quality, and the code behind them is duplicated:

1. **Transparency Triad back-translation** (`smuni-dictionary/src/lib.rs:21`) is a word-by-word **surface-token** gloss: `ro lo gerku cu danlu` → `"all the dog animal"`. It never touches the compiled IR, so it cannot reflect predicate-argument structure. The book's own product spec (`book/CLAUDE.md`, "Product Vision") already says this should be *"driven by the LogicalForm IR … reads like a logical specification."* This is a vision-vs-implementation gap, not a new feature.
2. **Proof-trace fact rendering** is fragmented: facts are stringified in **three** different formats (logji `to_display_string` → `gerku(adam)`; logji `repr::reconstruct_repr` → S-expr `(Pred …)`; nibli-protocol `humanize_fact` parses the S-expr form) and rendered by **two** independent walkers (nibli-protocol text path + nibli-ui Dioxus component path), with Neo-Davidsonian role-collapsing (`gerku_x1` → `gerku.x1`) duplicated.
3. **Conversion lattices** (logji ↔ wire/WIT) are hand-written in four places — nibli-engine `rule_to_json`/`term_to_json`, gasnu `rule_to_proto`/`term_to_proto`, lasna `convert_proof_rule`/`convert_logical_term_*`, plus a verbatim copy in nibli-wasm — so every new `ProofRule` variant is edited 4×.

**Goal:** the same readable rendering should drive *both* the triad and the proof trace, computed from the IR, with the rendering and conversion code consolidated.

**Decisions (locked):**
- **Scope = maximal DRY**, including deduping the conversion lattices (not just the rendering).
- **Back-translation computed client-side in the browser** (nibli-ui compiles Lojban→IR→English locally). Accepts the WASM-bundle growth / build-risk trade-off; matches the book's "data never leaves the device" vision.

**Risk carve-out:** we do **not** move `GroundTerm`/`GroundFact`/`StoredFact` into `nibli-types`, and we do **not** rewrite the canonical `ProofRule` into the serde wire shape. Both would touch the redb/postcard persistence format and the GraphQL JSON contract for marginal gain. The humanizer uses a single canonical **string** contract instead. This protects `smoke-gasnu-persist-replay` and the UI's JSON parsing.

## Architecture

**New crate `nibli-render`** = the single rendering layer.
- Deps: `nibli-types` (LogicBuffer/LogicNode/LogicalTerm), `smuni-dictionary` (glosses + new place templates), `nibli-protocol` (the wire `ProofRule`/`ProofTrace` it renders). Builds for **both** native and `wasm32`.
- **Key enabler:** lasna does **not** render — it emits canonical traces and the host/UI render them. So `nibli-render` may depend on `nibli-protocol` and key proof rendering on the **wire** `ProofRule`. This sidesteps any canonical-enum serde rewrite.
- Owns: (a) the IR→English back-translation, (b) the ONE fact humanizer, (c) the proof-tree renderer producing a structured `RenderedNode` consumed by both the text path and the Dioxus component path.

Spec register is the default (structure-exposing: quantifier scope stays visible — never reorder binders, never collapse proof steps into prose, never change a verdict). A `Fluent` register is an optional enhancement.

## Workstreams

### WS1 — Place-frame template data (`smuni-dictionary`)
- Extend `DictEntry` (`smuni-dictionary/src/lib.rs:1`) with `template: &'static str`; add `get_template(word)`.
- In `smuni-dictionary/build.rs`: add a curated `GISMU_PLACE_TEMPLATES` table (e.g. `gerku`→`"{x1} is a dog"`, `danlu`→`"{x1} is an animal"`, `klama`→`"{x1} goes to {x2} from {x3} via {x4} using {x5}"`) covering the gismu the corpora (`readme.lojban`, `gdpr.lojban`, `drug-interactions.lojban`) use; generic `{x1} <gloss> {x2}…` fallback for the rest. Emit the new field at the existing `DictEntry { … }` format sites (XML-present **and** fallback branches). Reuse `extract_arity`/definition machinery; XML place-text scraping deferred.
- Do **not** touch `smuni`'s separate arity-only `JBOVLASTE_ARITIES` (`smuni/src/dictionary.rs`).

### WS2 — `nibli-render` crate
Modules: `register` (`enum Register { Spec, Fluent }`), `frame` (place-template lookup over `DictEntry`), `term`, `fact`, `logic`, `proof`.

- **`fact::humanize_fact(display: &str) -> String`** — the single humanizer. Canonical input = logji's `StoredFact::to_display_string()` form (`rel(args)`, optional `Past(…)`/`Present`/`Future`/`Obligatory`/`Permitted` wrapper, args may be `sk_N(dep)`, `le foo`, `_`, numbers). Parse the flat `name(args)` string, collapse role predicates hiding the event Skolem (port `parse_role_predicate`/`is_event_skolem`/`humanize_term` from nibli-protocol), fill place template, generic `name(args)` fallback (no invented prose), passthrough guard if input starts with `(Pred`/`(`.
- **`logic::render_logic_buffer(&nibli_types::logic::LogicBuffer, Register) -> String`** — back-translation. Walk flat nodes (same recursion as `logji/src/repr.rs:26`); under each `ExistsNode`, regroup `rel(ev)` + `rel_xN(ev, arg)` (role naming from `smuni/src/semantic/selbri.rs:22`) into one frame; render `ForAllNode` as "Every dog is an animal" / "For every X: if X is a dog then X is an animal"; And/Or/Not/tense/Count as scope-exposing connectives.
- **`proof`** — `struct RenderedNode { icon, label, css_class, holds, is_leaf, children }`; `render_proof(&nibli_protocol::ProofTrace, Register) -> RenderedNode` and `render_proof_text(&ProofTrace, Register) -> String`. Move `icon`/`label`/`css_class`/`trace_display` here.

### WS3 — Consolidate conversion lattices + two proof renderers
- Delete nibli-protocol's `humanize_fact` + `tokenize_repr`/`parse_fact_node`/`format_fact_*`/`parse_role_predicate`/`is_event_skolem`/`humanize_term` and `ProofRule::{icon,label,css_class,trace_display}` + `ProofTrace::{to_pretty_text,to_pretty_text_with_indent}` + `format_proof_step`. nibli-protocol stays pure wire types.
- Add `nibli_protocol::from_canonical(&nibli_types::logic::ProofRule) -> ProofRule` (+ `…Term`/`…Trace`); add `nibli-types` dep to nibli-protocol. nibli-engine `rule_to_json`/`term_to_json`/`proof_trace_to_wire` and the verbatim nibli-wasm copy delete and call `from_canonical`. (2→1; JSON unchanged.)
- gasnu keeps its WIT→wire converter (distinct source) but renders via `nibli_render::render_proof_text`.
- lasna keeps `convert_proof_rule`/`convert_logical_term_*` (the one logji→WIT lattice). Net 4→3, plus rendering logic 2→1.
- Update `__exhaustiveness_guard` checklist (`nibli-types/src/logic.rs:228`).
- *Deferred:* canonical-`ProofRule`-as-wire-type (named-field rewrite) — higher risk.

### WS4 — Client-side back-translation in the Triad UI
- nibli-ui: add `gerna`, `smuni`, `nibli-render` deps. Replace the `back_translation` `use_memo` (`nibli-ui/src/main.rs:652`): parse → compile → `render_logic_buffer(&buf, Register::Spec)`. Keep `smuni_dictionary::back_translate` as a labeled "lexical gloss" fallback.
- nibli-wasm: add `back_translate_ir` client variant.
- **Verify the `wasm32-unknown-unknown` bundle builds early** (main build risk).

### WS5 — Single proof-tree walker
- nibli-ui `ProofNodeView`/`ProofTreeView` (`nibli-ui/src/main.rs:1260`) walk `nibli_render::RenderedNode`. gasnu + text consumers use `render_proof_text`.

## Critical files
- `smuni-dictionary/src/lib.rs`, `smuni-dictionary/build.rs` — place templates (WS1).
- `nibli-render/` (new) — renderer + humanizer + proof tree (WS2).
- `nibli-protocol/src/lib.rs` — delete rendering/humanizer; add `from_canonical`; add `nibli-types` dep (WS3).
- `nibli-engine/src/lib.rs`, `nibli-wasm/src/lib.rs`, `gasnu/src/main.rs` — call `from_canonical` / `render_proof_text` (WS3).
- `nibli-ui/src/main.rs` — client-side back-translation + `RenderedNode` view (WS4, WS5).
- `nibli-types/src/logic.rs` — exhaustiveness-guard checklist update (WS3).
- Untouched on purpose: `lasna/src/lib.rs` WIT converters, logji `GroundTerm`/`to_display_string`, `logji/src/repr.rs`.

## Reused utilities
- Role-collapse helpers `parse_role_predicate`/`is_event_skolem`/`humanize_term` (nibli-protocol) → `nibli-render::term`.
- `ProofRule::trace_display`/`icon`/`label`/`css_class` (nibli-protocol + nibli-ui) → `nibli-render::proof`.
- logji `StoredFact::to_display_string` (`logji/src/kb.rs:240`) = humanizer input contract.
- The curated `CORE_GISMU_ARITIES`/`FALLBACK_GISMU_ENTRIES`/`GISMU_GLOSS_OVERRIDES` pattern in build.rs = model for `GISMU_PLACE_TEMPLATES`.
- The flat-node recursion in `logji/src/repr.rs` = shape for `render_logic_buffer`.

## Verification
- `nibli-render` unit/golden tests: role-regroup, Skolem `#N`/`SkolemFn`/`DepPair`, tense/deontic, `le`/`lo`/zo'e/numbers, both registers, scope-preservation invariant. Port nibli-protocol's `humanize_*` tests.
- Back-translation golden: `ro lo gerku cu danlu` readable + scope-exposing. `test_back_translate_default_syllogism` stays green (lexical glosser unchanged).
- JSON contract: `from_canonical` output serializes byte-identically to pre-change wire JSON.
- Persistence: `smoke-gasnu-persist-replay` still green.
- End-to-end (WSL + Nix): `just check` → `just test` → `just test-engine` → `just test-server` → `just build-wasm` + gasnu smokes → `just ci`. Add `-p nibli-render` to `clippy-runtime`.
- Manual: `just ui` + `just server` — `ro lo gerku cu danlu` renders readable English + readable proof.
- `just verify-book-capture`: regenerate captured transcripts (humanizer changes text).

## Risks
- WASM bundle / build risk (WS4): build it first.
- Book-capture drift: regenerate.
- `from_canonical` JSON fidelity: byte-identical golden test.
- Soundness: rendering is pure; pin scope-preservation; unknown predicates fall back to `name(args)`.
- Partial template fills: keep templates 1-/2-place this pass; ≥3-place fall back to positional args.

---

# WS6 — Eliminate S-expressions completely (close the `repr.rs` carve-out)

**Supersedes** the "Untouched on purpose: `logji/src/repr.rs`" line above. WS1–WS5 removed
nibli-protocol's S-expr *parser* (`humanize_fact`/`tokenize_repr`) but deliberately left the only
S-expr *generator* in place. WS6 removes it. After WS6 there are **no S-expressions anywhere** in
code or book — the IR crosses boundaries as typed data, and humans read rendered English + a
structural tree.

## Problem

`logji/src/repr.rs` (`debug_logic`/`reconstruct_repr`/`write_repr`/`write_term`/`write_term_list`) is
the last S-expr emitter: it renders a `nibli_types::logic::LogicBuffer` as `(Pred "gerku" (Cons
(Const "adam") (Nil)))`, `(ForAll "_v0" …)`, etc. It is pure display (never parsed back, never a key).
Consumers: lasna WIT export `compile_debug` (`lasna/src/lib.rs:922-928` → `repr::debug_logic`),
native `nibli-engine::compile_debug` (`nibli-engine/src/lib.rs:323-325`), the `:debug` REPL command in
`gasnu` (`gasnu/src/main.rs:1101-1116`) and `nibli` (`nibli/src/main.rs:197-205`), the WIT signature
`wit/world.wit:517`, and three tests (`nibli-engine/tests/integration.rs:38`+`:711`,
`known_failures.rs:228`+`:244`). The book carries ~35 hand-written LISP snippets.

## Decision (locked)

**Typed IR across the WIT boundary; host renders for humans.** lasna emits the `logic-buffer` record
(not a pre-rendered string); the host (gasnu, nibli) renders a mechanical **English back-translation**
(`nibli_render::render_logic_buffer`) plus a non-S-expr **structural tree**
(`nibli_render::render_logic_tree`, new). This is the WS5 "lasna emits, host renders" philosophy
applied to `:debug`. The `:debug` display shows `[Logic]` (structure) + `[English]` (gloss) on both
host surfaces.

Rejected: keeping a rendered string across WIT (would re-introduce a guest-side renderer); JSON-only
(flat-buffer indices are less readable than a tree); English-only (hides role predicates / event
Skolems a compiler dev needs).

## Code steps

- **WIT (`wit/world.wit:517`):** `compile-debug: func(input) -> result<logic-buffer, nibli-error>`;
  add `logic-buffer` to the lasna interface `use logic-types.{…}` (line 496) — mirrors `smuni`
  (line 400) / `logji` (line 449). The `logic-buffer`/`logic-node`/`logical-term` WIT types
  (lines 228/243/273) already mirror `nibli_types::logic` 1:1. Regen via `cargo component build -p
  lasna` (gitignored `lasna/src/bindings.rs`; gasnu's `bindgen!` re-reads the WIT).
- **Delete `logji/src/repr.rs`** + `pub mod repr;` (`logji/src/lib.rs:40`). Removes all S-expr.
- **lasna (guest):** `compile_debug` returns the WIT `logic-buffer` (new 1:1 converter
  `nibli_types::logic::LogicBuffer → bindings WIT logic-buffer`, 13 nodes + 5 terms); buffer already
  in hand from `compile_pipeline` (`lasna/src/lib.rs:761`). No render in the guest.
- **nibli-render (host):** add `render_logic_tree(&LogicBuffer, Register) -> String` — indented,
  one-node-per-line, functional term notation (`gerku(_ev0)`, `sk_1(adam)`, `zo'e`, integer numbers),
  reusing the flat-node recursion shape from the deleted `repr.rs`. Keep `render_logic_buffer`.
- **gasnu (host):** `:debug` receives the WIT `logic-buffer`; add the reverse converter
  `WIT logic-buffer → nibli_types::logic::LogicBuffer` (mirrors gasnu's `rule_to_proto`/`term_to_proto`
  WIT→wire converters); print `[Logic]\n{render_logic_tree}` + `[English] {render_logic_buffer}`.
- **nibli-engine + nibli REPL:** `compile_debug` returns the typed `LogicBuffer`
  (`nibli-engine/src/lib.rs:323`); native path already holds it. `nibli/src/main.rs:203` renders
  `[Logic]` tree + `[English]` gloss (nibli-render already a transitive dep).
- **Tests → assert on typed IR:** rewrite the `role_segment` helper + `cll_place_counter_fi_then_untagged`
  (integration.rs:38/711) and the two `abstraction_body_*` (known_failures.rs:228/244) to inspect the
  returned `LogicBuffer` nodes directly (or `render_logic_tree` lines) instead of slicing S-expr.
- **Defensive guard kept:** `nibli-render/src/fact.rs`'s `starts_with('(')` passthrough +
  `stray_s_expr_passes_through` test stay (also guards bare `DepPair`; fed by the proof trace, not
  `repr`).
- Add both new converters to the `__exhaustiveness_guard` checklist (`nibli-types/src/logic.rs`).

## Book steps

Replace **LISP S-expr only**; KEEP Rust typed-term (`SkolemFn("sk_1", x)`, `Bare(GroundFact {…})`,
`typed_conclusions: […]`) and FOL (`∀x. gerku(x) → danlu(x)`) — those are the structured/IR target.
Convention: typed-term for IR shape (`SkolemFn("sk_1", adam)`, `DepPair(x, y)`), functional for
fact-store/REPL output (`sk_1(adam)`, `gerku_x1(_ev0, adam)`, `Past(klama(adam))`) — matching
`logji/src/kb.rs` `to_display_string`.

- **Prose/illustration (hand-edited, not capture-managed):** drop parens, switch to functional/typed
  across `book/P3_C07*`, `P3_C08*`, `P3_C09*`, `P3_C10*`, `Appendix_B*`. e.g.
  `(SkolemFn "sk_1" adam)` → `SkolemFn("sk_1", adam)`; `(nelci_x2 _ev0 (SkolemFn "sk_1" adam))` →
  `nelci_x2(_ev0, SkolemFn("sk_1", adam))`; `(Past (gerku adam))` → `Past(gerku(adam))`;
  `(gerku_x1 _ev0 adam)` → `gerku_x1(_ev0, adam)`. **Preserve** proof-trace rule labels
  `Rule (gerku → danlu): danlu(adam) -> TRUE` (parens = rule name, not a term).
- **`book/P5_C18*.md:301` (capture-managed `:debug` block):** do NOT hand-edit first; after the code
  lands, regenerate (`python3 book/tools/capture_book.py --write --chapter P5_C18_…md`) so it shows
  the new `[Logic]` tree + `[English]`; reword the `:304` prose naming `Pred`/`Cons`/`Num`/`Var`.
- **Forward enforcement:** add a notation rule to `book/CLAUDE.md` ("functional/typed-term + FOL,
  never LISP S-expr"); record in `book/revisions.md` (separate repo). Completion gate (neither
  `verify_book.py` nor `verify-book-capture` catches S-expr):
  `grep -rnE '\((SkolemFn|DepPair|Pred|Cons|Const|Num|Var|Nil|Compute|Past|Present|Future|And|Or|Not|Exists|ForAll|Count) ' book/`
  and `grep -rnE '\([a-z]+(_x[0-9])?[[:space:]]+[a-z_0-9.]+( [a-z_0-9.]+)*\)' book/ | grep -vE 'Rule \(|→'`
  — expect zero hits (excluding rule labels). Optionally wire the first into `verify_book.py`.

## Critical files (WS6)
- `wit/world.wit`, `logji/src/repr.rs` (delete) + `logji/src/lib.rs`, `lasna/src/lib.rs`,
  `nibli-render/src/{logic.rs,lib.rs}`, `gasnu/src/main.rs`, `nibli-engine/src/lib.rs`,
  `nibli/src/main.rs`, `nibli-engine/tests/{integration.rs,known_failures.rs}`,
  `nibli-types/src/logic.rs` (exhaustiveness guard).
- Book: `book/P3_C07*.md`, `P3_C08*.md`, `P3_C09*.md`, `P3_C10*.md`, `Appendix_B*.md`, `P5_C18*.md`,
  `book/CLAUDE.md`, `book/revisions.md`.

## Verification (WS6, additive to the WS1–WS5 list)
- `just check` → `just test` (add nibli-render `render_logic_tree` unit tests: syllogism tree + flat
  fact) → `just test-engine` (migrated placement + abstraction tests against the typed return) →
  `just verify-harness` → `just build-wasm` (regenerates lasna bindings for the new WIT signature) →
  gasnu smokes → `just ci`.
- Manual `:debug` smoke in gasnu and `nibli`: `[Logic]` tree + `[English]` gloss, no `(Pred`.
- `just verify-book` then `just verify-book-capture` (after regenerating P5_C18:301); then both grep
  gates return zero.

## Risks (WS6)
- Binding regen may stop on `io-extras` after generating bindings (pre-existing); the regenerated
  `bindings.rs` is what matters. WS6's WIT signature change is the one place this touches bindings.
- Two new mechanical 1:1 converters (logji↔WIT in lasna; WIT↔nibli_types in gasnu) — guarded by the
  `__exhaustiveness_guard`.
- Book-capture coupling: `P5_C18:301` must be regenerated, not hand-typed.
- Sequencing: WS6 depends on WS2/WS4 (nibli-render present and host-wired) — land WS1–WS5 first.
