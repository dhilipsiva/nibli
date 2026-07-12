# nibli KR TODO

The nibli KR program tracker (formerly KLARO_TODO.md — the v0.1 language program that
this file tracked is COMPLETE; what follows is the successor program). Plain bullets,
never numbered — work the FIRST remaining bullet; cross-reference items by name. Delete
a bullet entirely when it fully lands; update it if only partially done.

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
   and the repo name. That includes crate names (smuni/logji/lasna/gasnu/fanva…),
   the WIT package (`lojban:nibli`!), env/commands, internal vocabulary
   (selbri/sumti/bridi/tanru/xorlo/goi…), corpora, AND the canonical predicate
   names — **proof traces must contain no Lojban** (today they show
   `Asserted: gerku.x1(adam)`, `Exists: da = adam`, `zo'e` — because the IR
   predicate names ARE gismu and `$vars` lower to the da/de/di pool).

Program discipline unchanged: every bullet lands independently CI-green; the logji
reasoning core's soundness surface stays gate-protected throughout (see the oracle
warnings inline — never delete a verification oracle before its replacement lands).
The full de-Lojbanization inventory (leak surfaces, rename ripple, gate fates) was
mapped 2026-07-12; load-bearing anchors are quoted per bullet.

- **gerna extraction + donation repo (do FIRST — extract before anything is deleted)**
  — carve a standalone repo containing: the `gerna` crate (+ `goi.rs`), the
  gerna↔camxes parse-differential gate (`nibli-verify/src/parser_diff.rs` +
  `tests/parser_differential.rs` — it is gerna's conformance suite), the ilmentufa
  flake input + `NIBLI_CAMXES_DIR` wiring, `LOJBAN_COVERAGE.md`, `fuzz_parse`, the
  vendored camxes browser assets (`nibli-ui/assets/js/vendor/camxes/`), and the
  **agentic Lojban translation tool** (from nibli-fanva: `LOJBAN_SYSTEM_PROMPT`, the
  gerna+smuni+camxes gate chain, the jbotci MCP client + `fanva-proxy/`, the
  translate_agentic loop — a self-contained gift, per the user: "give them an agentic
  lojban translation tool (borrowed from transparency triad)"). Also take the
  `.lojban` corpora + `lojban2klaro` + the python Lojban flywheel
  (`lojban_classifier.py`, `generate_training_data.py`, `nibli_model.py`,
  `training_stats.py`) — they are Lojban assets. Decide: fresh repo with a pointer
  back, or `git filter-repo` history extraction. Nothing is deleted from nibli in
  this bullet — extraction only.
- **KR seam-conformance gate BEFORE the Lojban oracle dies** — the Klaro↔Lojban twin
  battery (`verify-klaro`/`verify-klaro-twins`) is currently the KR front-end's ONLY
  independent correctness oracle; deleting Lojban deletes it. FIRST build the direct
  KR→smuni seam gate on the `nibli-verify/src/seam.rs` pattern: compile KR source
  text end-to-end and check the FOL against hand-verified structural goldens +
  metamorphic pairs (the same construct inventory the twin battery sweeps today,
  re-anchored on hand-verified FOL instead of Lojban equality). Re-home
  `determinism_corpus_klaro_native` (lives in `tests/klaro_twins.rs`, which dies)
  into this gate or a standalone determinism gate.
- **THE DROP (single-surface milestone)** — with the donation repo extracted and the
  KR seam gate green, delete Lojban from nibli in one milestone: the `gerna` dep
  everywhere (9 dependents), `Language` enum + `NIBLI_LANG` + WIT
  `enum language`/`set-language` (component ABI break — version-bump the WIT
  package), `:lojban`/`:klaro`/`:lang` + `--lang` flags, the `.lojban` corpora +
  twins machinery (`migrate-corpora` runs once more, then dies with `lojban2klaro`),
  goi snapshots in lasna/nibli-engine + the 7 goi smokes +
  `smoke-gasnu-script-lojban` + mixed-mode smoke + `determinism_corpus_lojban_twin`,
  `verify-parser`, the camxes gate + `test-fanva-wasm`'s marshalling tests + jbotci
  MCP + tersmu view + `fanva-proxy` (tear down the deployed worker), python flywheel
  recipes, `LOJBAN_COVERAGE.md`. Corpus feeds re-point:
  `nibli-verify/src/corpora.rs` still `include_str!`s the `.lojban` sides for the
  Vampire/clingo legs — re-point to the KR corpora (the oracles are language-free).
  `verify-klaro-dict` keeps its behavioral battery + structural invariants, drops
  the gerna-twin compiles. CROSS-REPO GATES: the book harness pins
  `NIBLI_LANG=lojban` (`Justfile` verify-book + `book/tools/capture_book.py`) — the
  book repo must migrate its transcripts or pin a pre-drop engine tag BEFORE this
  lands; the deployed /nibli demo JS must migrate first (see the site bullet).
- **"Klaro" → "nibli KR" rename** — ~1,096 occurrences across 78 files. Display
  name: "nibli KR", first mention "nibli knowledge representation (KR) language".
  UI: both tab strips' label via `kb_tab_label()` → "nibli KR" + the "?" icon
  (`span { class: "tab__help", title: "nibli knowledge representation (KR)
  language", "?" }` as a sibling of the label inside each tab button —
  nibli-ui/src/main.rs, the two `button { class: "tab" … }` sites), "Load .klaro" /
  placeholder / hint strings / settings copy / examples.rs docs. Code: crate
  `klaro` → `nibli-kr`, `klaro-dictionary` → `nibli-kr-dictionary` (7 + 3
  dependents), `Language::Klaro` handling (moot if THE DROP lands first — then the
  enum is already gone), `KLARO_SYSTEM_PROMPT` → `KR_SYSTEM_PROMPT`, gate name
  "klaro" → "kr" (chips + GateError::gate + pinned tests), `klaro.pest` →
  `nibli_kr.pest`, `fuzz_klaro` → `fuzz_kr`, Justfile recipes `test-klaro`/
  `verify-klaro*` → `test-kr`/`verify-kr*`, `acceptance.klaro` + the corpus files'
  extension **`.klaro` → `.nkr` (PROPOSAL — decide before renaming; alternatives
  `.kr`, `.nibli`)**, `Language::FromStr`/`set_language` string "klaro" → "kr"
  (keep "klaro" as a deprecated parse alias through the site window — the deployed
  playground JS is a published consumer), SURFACE_SYNTAX.md retitled "The nibli KR
  language" (keep the filename — dozens of §-references in code comments — or
  sweep them all in the same commit). Tracker already renamed (this file).
- **Lojban identifier + crate purge (everything but the predicate names)** — rename
  the surviving Lojban-named crates and boundary names. PROPOSALS (decide per crate
  at implementation): `smuni` → `nibli-semantics`/`nibli-compile`, `logji` →
  `nibli-logic`/`nibli-reason`, `lasna` → `nibli-pipeline` (artifact `lasna.wasm` →
  `nibli.wasm`; WIT world `lasna-pipeline` → `nibli-pipeline`, interface `lasna` →
  `engine`), `gasnu` → `nibli-host`/`nibli-repl` (~25 smoke recipes rename),
  `nibli-fanva` → `nibli-formalize`, `smuni-dictionary` → `nibli-lexicon`
  (consider folding `nibli-kr-dictionary` in behind a feature — the two-crate split
  exists only to keep the reverse map out of the web bundle). WIT package
  `lojban:nibli@0.1.0` → `nibli:engine@0.2.0` (bindings regen, one commit with both
  sides). flake.nix description + shell banner ("Lojban NeSy Engine" →
  "nibli — Zero-Hallucination Symbolic Reasoning Engine"). Internal vocabulary
  sweep in surviving crates (selbri→predicate/relation, sumti→term/argument,
  bridi→claim/statement, tanru→compound, xorlo→presupposition-witness,
  gismu→root-word/lexeme, `fanva/PROMPT.md` archive → donation repo). The WIT doc
  comments' Lojban glosses (zo'e/le/la/pu/ca/ba/du/go'i) go with it.
- **Grammar+dictionary-grounded Formalize prompts (user decision 2026-07-12)** — the
  Transparency Triad's Formalize system prompt must contain the ACTUAL KR grammar and
  the dictionary, so the LLM formalizes against ground truth instead of nine
  few-shots; the agentic parse-error-feedback loop stays as-is. Design notes:
  (a) GRAMMAR: `include_str!` the pest file (`klaro/src/klaro.pest`, 181 lines /
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
  `klaro_dictionary` map (no drift possible; dual-mode — the CI fallback build
  embeds the curated core only, loudly).
  (c) Optimize BOTH prompts (system + the per-request user turn) and measure:
  attempts-to-converge on a fixed English corpus is the metric (feeds the
  authoring-study track). Guard tests: few-shots stay gate-valid (existing twin
  guard), the embedded grammar is the shipped file by construction, the dictionary
  block is generated from the shipped map in the same build.
  Applies to all three nibli-ui LLM paths (agentic Formalize, single-shot query
  formalize, the modal key-test). Sequencing: written here after the KR rename
  bullet so the prompt is born saying "nibli KR", but it is independent — pull it
  earlier as plain KLARO_SYSTEM_PROMPT work if wanted.
- **Predicate-name de-Lojbanization (proof traces contain NO Lojban — the deep one)**
  — today every `LogicBuffer` relation is a gismu (`klaro/src/emit.rs:379-387` maps
  alias→`entry.gismu`; smuni derives `gerku_x1`, `le_domain_gerku`; `=` mints `du`
  at emit.rs:192; `$vars` lower to the literal `da/de/di` pool at emit.rs:90-103,
  which smuni string-matches for quantifier closure). DECISION (recommended, and the
  only option satisfying "no Lojban anywhere"): **option A — flip the canonical
  predicate namespace to the English aliases at compile time** (emit
  `canonical_alias` instead of `entry.gismu`; keep the KR alias the user wrote where
  it IS canonical). Scope the obstacles honestly:
  (a) re-key `smuni-dictionary` lookups (arity/gloss/template — logji
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
- **demo site migration (cross-repo, dhilipsiva.dev — SEPARATE Claude session)** —
  the copy-pastable prompt was handed to the user 2026-07-12. Site session scope:
  /nibli guided demo KBs+queries+copy → nibli KR, worker calls
  `set_language("klaro")` explicitly against current main (survives until the
  string rename lands, then "kr"). NIBLI-SIDE residual that lands in the same
  window: flip `nibli-wasm`'s pinned-Lojban session default + `back_translate_ir`'s
  front-end (`compile_for_render` is language-parameterized — a one-arg flip),
  then THE DROP removes the pin entirely. Sequencing: site migrates first (works
  against current main), nibli flips after.
- **book migration (separate repo — book/TODO.md carries the details)** — the book
  is Lojban-heavy by design ("Lojban as IR" framing, Part II Ch 3–6); the pivot
  replaces it with nibli KR. Key restructuring (user decision): MERGE Ch 3 ("Why
  Not English?") + Ch 4 ("Lojban — A Gift from Linguists, Logicians, and
  Mathematicians") into ONE chapter about the nibli KR language. The capture
  harness's `NIBLI_LANG=lojban` pin breaks at THE DROP — the book must re-capture
  its transcripts in KR (or pin a pre-drop engine tag) before then.
