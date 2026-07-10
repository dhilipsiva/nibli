# TODO

Plain bullets, never numbered — work the FIRST remaining bullet; cross-reference items by
name. Delete a bullet entirely when it fully lands; update it if only partially done.
(The first item came out of the 2026-07-05 Lojban Discord #proga thread with korvo —
brismu/zaha/zatske — and feklat; the int19h items from his 2026-07-10 nibli-fanva feedback.)

- **Ontology-row import (brismu/zatske interchange)** — korvo proposed flat rows
  `[P, Q, mapping]` (selbri subrelation with terbri mapping: identity `["gerku","danlu",
  [1,2]]`; place deletion `["skari","ckaji",[1,2]]` — unmapped source places dropped;
  permutation `["lanzu","cmima",[2,1]]`) as the interchange format between brismu / zaha /
  zatske and downstream consumers; agreed in-thread, korvo confirmed rows are "a good
  compromise". Build an importer beside `nibli-import/src/rdf.rs`/`owl.rs`: each row
  compiles to one monotone Horn rule at the IR level (event decomposition — mapping is a
  role renaming, deletion = roles absent from the head), arity/place validation against
  smuni-dictionary (strict-mode rejection semantics), per-row source/provenance field
  surfaced in proof traces, curated Vampire differential cases for the three row shapes,
  plus mutual-row (equivalence) cases like dugri/tenfa — positive cycles legal, fuel-bounded.
  BLOCKED on korvo pinning the row schema + publishing a baseline export. Spec feedback
  already sent in-thread: the mapping-list direction is ambiguous (a 3-cycle case like
  dugri/tenfa pins it — the [2,1] swap and [1,2] identity examples can't distinguish the
  two readings), and rows want a source field (brismu / zaha / zatske) for provenance.

- **fanva-proxy: retire once jbotci CORS lands** — int19h is enabling direct browser→jbotci
  MCP calls on his end ("no reason it shouldn't be allowed from the browser"). When live:
  verify `initialize` + `tools/list` + `tersmu` from nibli-ui WITHOUT the proxy, then default
  the proxy URL to the direct endpoint and deprecate the Cloudflare Worker (keep the
  local-gates degradation path). Direct crate embedding was assessed 2026-07-10 and is OFF
  the table on licensing: jbotci is AGPL-3.0-or-later (nibli is MIT OR Apache-2.0 — linking
  it into the nibli-ui wasm bundle would relicense the distributed bundle AGPL), unless
  int19h ever dual-licenses a core crate. Calling his hosted server over HTTP is arm's-length
  and clean — the CORS'd-MCP route IS the integration. (Also: his parser intentionally
  diverges from camxes ~500/22k — SA erasure, ZOI preprocessing — so it could never replace
  the camxes-std gate regardless.)

- **verify-parser: GIhA in the random generators + solid `.ije` lexing** — `gi'e`/`gi'a`/
  `gi'o`/`gi'u` now parse (curated seam cases pin the desugar, and a curated GIhA list rides
  the parser-differential gate) but the seeded random case generators never emit bridi-tails,
  so the camxes differential doesn't fuzz them; add a GIhA production. Separately, the solid
  spelling `.ije` does not lex (only `.i je` parses) — corpus text from Lojbanists will use
  the solid form; teach the lexer/preprocessor the `.i`+JA compounds.

- **GIhA quantified/description heads: share the head witness across tails** — currently
  rejected fail-closed (gerna `giha_safe_head`): the repeated-head desugar would re-quantify
  a `da`/`lo`-head per tail, splitting one surface scope into independent ∃s (wrong TRUE on
  disjoint witnesses — adversarial-review finding, 2026-07-10). The real fix is compiling the
  head ONCE (one witness/variable) and distributing only the tails — needs a smuni-level GIhA
  construct instead of the parse-time desugar. Would un-block int19h's Genesis 1:2
  (`lo terdi cu na se tarmi gi'e kunti`), which today needs a name head or `.i je` restate.

- **logji: upgrade the reversed material-conditional arm (`Or(Q, Not P)`)** — a `na` on the
  RIGHT operand of an asserted disjunction (`mi klama .i ja mi na citka`, `… gi'a na citka`)
  registers a conditional whose condition templates carry the assertion's own event-Skolem
  CONSTANTS, so it can never unify with a later assertion's fresh event Skolem — the rule is
  inert (modus ponens never fires; completeness-only, never unsound). The forward arm
  (Not-on-left) was upgraded to `compile_forall_to_rule` (ev__ pattern vars) precisely for
  this; mirror it in the reversed arm (`register_ground_material_conditional`, kb.rs) and add
  the `Q→P + Q ⊢ P` engine test the adversarial review used to confirm the gap.

- **Determinism corpus: add GIhA + negative-conjunct lines** — `determinism-corpus.lojban`
  predates both; add a `gi'e` chain, a `gi'enai` line, and a `P .i je na Q` +
  contradiction-check sequence so all three runtime surfaces pin the new shapes (requires
  re-pinning the corpus verdicts on native + Wasmtime + node).
