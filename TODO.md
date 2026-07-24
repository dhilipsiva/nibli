# Engine TODO

Plain bullets — delete when fully landed. Docs & release track: **`DOCS_TODO.md`**.
Book manuscript: separate `book/` repo (`book/TODO.md`).

---

## Authorization (first-class multi-language auth)

**Goal:** Built-in authorization as a **native** nibli surface — committed policy KB +
stable WIT + thin Python/Rust framework adapters — with **low runtime overhead** and
**unchanged** zero-hallucination / CWA / CDA guarantees. Not an external Python package;
not Extism-primary (optional future PDK note only).

**Consumers (same policy, idiomatic wrappers):** FastAPI, DRF + django-spectacular,
Strawberry, Graphene, OpenAPI helpers; axum, tower, async-graphql, juniper; more later.

**Efficiency (non-negotiable):** long-lived engine; policy loaded once; ephemeral facts
per decision only; aggressive decision cache (key: policy version + relevant facts);
proofs **opt-in** (hot path = cheap `can` / `allowed-fields`).

**Constraints:** compose with existing engine (no forked reasoner); keep Auth WIT small
and versioned; fail-closed vocabulary; document every public surface; Nix/Just/tests
house style; no book manuscript content.

### Decisions of record (locked for this track)

| Decision | Choice |
|----------|--------|
| **Primary ABI** | WIT Component Model — e.g. package **`nibli:auth@0.1.0`** (or engine-world methods carefully versioned); Extism is **not** the primary path |
| **Policy home** | Committed **nibli KR** corpus (`include_str!` / shipped `.nibli`), versioned; load by default or one-shot enable |
| **Ontology (minimal target)** | Roles for subject / action / resource / field; relations `can(S,A,R)`, `visible_field(S,R,F)` (KR spellings TBD vs corpus `ident` rules — prefer snake_case if hyphens illegal) |
| **Standard rules** | Small built-in set: ownership, roles, tenants, basic temporal patterns — user rules compose on top |
| **Decision payload** | `allowed` (bool), engine `verdict` (TRUE/FALSE/UNKNOWN/…), optional proof, optional fields, reason |
| **Session model** | One warm engine; assert/retract only ephemeral context facts; never spawn engine per request |
| **Adapters** | Thin, idiomatic; **one Authorizer API** for object-, row-, and field-level checks |
| **Proofs** | Available via `explain` (or `can` flag); never paid on hot path by default |

### Sketch targets (refine in A0 before large code)

**WIT (illustrative — finalize in A0):**

```wit
package nibli:auth@0.1.0;

interface authorizer {
  record decision {
    allowed: bool,
    verdict: string,           // TRUE | FALSE | UNKNOWN | …
    reason: option<string>,
    fields: option<list<string>>,
    // proof omitted on hot path; present only for explain
  }
  can: func(subject: string, action: string, resource: string,
            context-facts: list<string>) -> result<decision, string>;
  allowed-fields: func(subject: string, action: string, resource: string,
                       context-facts: list<string>) -> result<list<string>, string>;
  explain: func(subject: string, action: string, resource: string,
                context-facts: list<string>) -> result<decision, string>;
  // optional later: batch-can, filter-resources
}
```

**KR ontology (illustrative — must compile fail-closed against lexicon):**

```nibli-kr
# Class / sort scaffolding + decision heads (exact names = corpus or auth-local predicates)
# can(subject, action, resource).
# visible_field(subject, resource, field).
# plus ownership / role / tenant rules in shipped auth.nibli
```

**Layout (proposal — confirm in A0):**

| Path | Role |
|------|------|
| `auth/auth.nibli` or `nibli-auth/policy/*.nibli` | Built-in policy KB (version pin) |
| `wit/auth.wit` (+ world wiring) | Auth package / export |
| `nibli-auth/` (lib) | Session: load policy once, ephemeral facts, cache, Decision type |
| `nibli-engine` / `nibli-pipeline` / `nibli-host` | Expose Auth surface native + WASM |
| `python/nibli_auth/` (+ framework extras) | Client + FastAPI / DRF / Strawberry / Graphene / spectacular |
| `nibli-auth-axum` / features or examples | axum, tower, async-graphql, juniper |
| `examples/auth-fastapi/` + `examples/auth-axum/` | **Same policy** E2E in both stacks |
| `mdbook/src/user/authorization.md` | Ontology, policies, APIs, caching, versioning (→ DOCS_TODO) |

### Phased delivery

#### A0 — Inspect & design (no large code)

- Inspect `wit/world.wit`, `nibli-engine`, `nibli-session`, `nibli-lexicon`, host, `python/`.
- Decide: **new WIT package** vs methods on `nibli:engine@…` (prefer small dedicated `nibli:auth@0.1.0` if it keeps engine world stable).
- Map ontology names to **lexicon reality** (new `PredicateEntry` rows vs existing; no silent arity invent).
- File layout + WIT sketch PR-ready; success criteria checklist.

#### A1 — Built-in policy KB + engine core

- Committed KR corpus + version string; standard ownership/role/tenant/temporal rules.
- Lexicon entries for all policy predicates (fail-closed).
- `nibli-auth` (or session helpers): load policy once; ephemeral assert/retract; `can` / `allowed-fields` / `explain`; decision cache key design.
- Tests: policy verdicts; **proofs only on explain**; CWA/CDA preserved; no per-call engine spawn.

#### A2 — WIT + pipeline / host wiring

- Land `nibli:auth@0.1.0` (or agreed surface); regenerate bindings as needed.
- Native (`nibli-engine`) + WASM component path both expose Auth.
- Host/REPL smoke optional (`:auth` or example binary).

#### A3 — Rust adapters + example

- Ergonomic wrappers; axum/tower middleware or extractors; async-graphql + juniper guards.
- `examples/auth-axum` (or under `examples/`) using the built-in policy.

#### A4 — Python adapters + example

- Core client (WIT/native bridge — document how: component host, pyo3, or subprocess only if unavoidable; prefer in-process if available).
- FastAPI dependency/decorator (`require("update", Document)` style).
- DRF: permission classes, object permissions, FilterBackend, serializer field masking.
- django-spectacular / OpenAPI helpers; Strawberry + Graphene object/field guards.
- `examples/auth-fastapi` — **same `.nibli` policy** as axum example.

#### A5 — Docs, efficiency write-up, CI

- mdBook (or README) chapter: ontology, writing policies, Python/Rust APIs, warm-engine + cache model, WIT versioning/migration (track under DOCS_TODO).
- Just/CI tests for auth core + at least one adapter smoke.
- Note optional future Extism PDK — not implemented.
- CHANGELOG / release note when public.

### Success criteria (delete track when all true)

- Load built-in auth KB; assert ownership/role facts; `can` / `allowed-fields` from **Python and Rust** with warm engine + cache.
- **One KR policy** drives FastAPI, DRF, Strawberry, Graphene, axum, async-graphql (and documented juniper).
- Field- and row-level permissions share the same Decision type.
- Proofs on demand only; hot path stays cheap.
- Reviewable merge into main nibli; zero-hallucination invariants green in CI.

### Explicit non-goals

- Extism as primary runtime.
- Per-request engine process spawn.
- Weakening CWA/CDA or inventing vocabulary outside fail-closed corpus.
- Framework-specific policy languages (policy stays nibli KR).

---

## Editor / Linguist / LSP (syntax tooling)

Policy: book and gates keep fence tags **`nibli` / `nibli-kr`** (never a foreign
language alias). Seed grammar lives in `grammars/` (`nibli.tmLanguage.json` +
injection sketch + `grammars/README.md`). Runtime lexer remains
`nibli-kr/src/highlight.rs` (REPL / UI) — keep token classes aligned when anything
here changes. Keywords must stay equal to `nibli_lexicon::RESERVED_WORDS`.

- **VS Code / Cursor extension (local):** package `grammars/nibli.tmLanguage.json`
  as language id `nibli` for `*.nibli`, plus markdown fence injection for
  `nibli` and `nibli-kr` via `grammars/nibli-markdown-injection.json`. Ship as
  `editors/vscode/` (or a small sibling repo) with `language-configuration.json`
  (`#` line / `/* */` block). Optional: publish to Open VSX / Marketplace.
- **GitHub Linguist PR:** submit `source.nibli` + samples from shipped corpora
  (`gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli`, …); language name
  **Nibli**, extensions `.nibli`, aliases `nibli-kr` / `nibli kr`. Until merge,
  github.com fences stay uncolored — do not retag book fences to `prolog` etc.
- **Tree-sitter grammar (`tree-sitter-nibli`):** new crate/repo tracking
  `nibli-kr.pest` by discipline (not codegen). Queries: `highlights.scm`,
  `locals.scm`, `injections.scm` for Markdown. Consumers: nvim-treesitter,
  Helix, Zed. Does **not** replace Linguist/TextMate for github.com.
- **`nibli-lsp` (thin LSP):** workspace bin on `tower-lsp` (or `lsp-server`) using
  `nibli_kr::parse_checked` diagnostics, lexicon hover/completion (gloss,
  places, templates), optional format via `nibli_kr::render`, optional semantic
  tokens from `nibli_kr::highlight::lex`. Single-file first; multi-file KB
  projects later.
- **Conformance guard (optional ratchet):** test or script that TextMate keyword
  alternation ≡ `RESERVED_WORDS` (and document Tree-sitter keyword list the same
  way when that grammar exists) so reserved-list edits cannot drift the editors.
- **Book fence rename (optional, coordinated):** if/when fences go plain
  `nibli` only, retarget `verify_book.py` + capture harness + injection regex in
  one PR; keep `nibli-kr` as Linguist/VS Code alias forever.

---

## Pointers

| Tracker | Scope |
|---------|--------|
| **`DOCS_TODO.md`** | mdBook docs, GH Pages / site primary, crates.io + GitHub Releases (R0–R3); auth chapter when A5 ships |
| **`book/TODO.md`** | Manuscript only (private checkout; Orange AVA) |
| **This file** | Engine runtime, **authorization track (A0–A5)**, editors |
