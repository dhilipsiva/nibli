# Engine TODO

Plain bullets — delete when fully landed. Docs & release track: **`DOCS_TODO.md`**.
Book manuscript: separate `book/` repo (`book/TODO.md`).

---

## Authorization (first-class multi-language auth)

**Goal:** Built-in authorization as a **native** nibli surface — committed policy KB +
stable WIT + thin Python/Rust framework adapters — with **low runtime overhead** and
**unchanged** zero-hallucination / CWA / CDA guarantees. Not an external Python package;
not Extism-primary (optional future PDK note only).

**Consumers:** FastAPI, DRF + django-spectacular, Strawberry, Graphene, OpenAPI helpers;
axum, tower, async-graphql, juniper (same KR policy).

**Efficiency:** long-lived engine; policy once; ephemeral context facts only; decision
cache (`policy_version` + agent/action/resource + context hash); proofs **opt-in**.

### A0 — Design (landed)

Inspected: `wit/world.wit` (`nibli:engine@0.5.0`, world exports `engine` only),
`nibli-session` / `nibli-engine` (assert/query/retract), lexicon collisions, `python/`
(compute backend only — no engine binding).

### Decisions of record (locked — A0)

| Decision | Choice |
|----------|--------|
| **Primary ABI** | **`interface authorizer` inside `nibli:engine@0.6.0`** (single-package shipping; logical auth v0.1). World exports `engine` + `authorizer`. Split `nibli:auth@0.1.0` package deferred. Extism **not** primary. |
| **Policy home** | `nibli-auth/policy/auth-0.1.0.nibli` via `include_str!`; `POLICY_VERSION = "0.1.0"` |
| **API decision head** | **`authorized(agent, action, resource)`** — **not** `can` (**`can` is tin/can `lante` in corpus**) |
| **Field-level head** | **`visible_attr(agent, resource, attr)`** — **not** `field` / `visible_field` (**`field` is agricultural `foldi`**) |
| **Principal sort** | Prefer **`agent`** (FREE); do **not** reuse corpus **`principal`** (`ralju`) |
| **Ownership** | Reuse existing **`owns(owner, owned, basis)`** |
| **Roles / tenants** | NEW: `has_role(agent, role)`, `in_tenant(agent, tenant)`; optional `resource_tenant` |
| **Action / attr tokens** | KR **quoted strings** (`"update"`, `"title"`) → `Constant` |
| **Roles/tenants style** | Prefer **quoted strings** (parity with actions) |
| **UNKNOWN on hot path** | **Deny** (`allowed=false`, verdict=unknown); only engine TRUE ⇒ allow |
| **Decision payload** | `allowed`, `verdict` (true/false/unknown/resource-exceeded), optional `reason`, `fields` list; proof only on `explain` |
| **Context** | Multi-line **context KR** string: assert → query → **retract** fact ids |
| **Session** | One warm `Authorizer` wrapping engine/session; never per-request spawn; never `reset()` between requests (drops policy) |
| **Python bridge** | **PyO3** primary (`nibli_auth`); no subprocess hot path |
| **Deontic corpus** | Do **not** overload `permits`/`permitted` as HTTP auth |

**Forbidden names for auth heads:** `can`, `field`, `principal` (corpus collisions).

### Locked file layout

| Path | Role |
|------|------|
| `nibli-auth/policy/auth-0.1.0.nibli` | Built-in policy |
| `nibli-auth/src/{lib,policy,cache}.rs` | Authorizer, Decision, cache |
| `nibli-lexicon/.../predicates.rs` | NEW rows: `authorized`, `visible_attr`, `has_role`, `in_tenant`, optional `agent`/`resource`/`resource_tenant` |
| `wit/auth.wit` | `nibli:auth@0.1.0` |
| `wit/world.wit` | Export `authorizer` (A2) |
| `python/nibli_auth/` | Client + FastAPI/DRF/Strawberry/Graphene/spectacular |
| `examples/auth-axum/`, `examples/auth-fastapi/` | **Same policy** E2E |
| `mdbook/src/user/authorization.md` | A5 / DOCS_TODO Phase 2b |

### WIT sketch (locked shape — land in A2)

```wit
package nibli:auth@0.1.0;

interface types {
  enum verdict { true_, false_, unknown, resource-exceeded }
  record decision {
    allowed: bool,
    verdict: verdict,
    reason: option<string>,
    fields: list<string>,
  }
  record explained {
    decision: decision,
    proof-json: option<string>,
  }
}

interface authorizer {
  use types.{decision, explained};
  resource session {
    constructor();
    load-policy: func(extra-kr: option<string>) -> result<string, string>;
    assert-facts: func(kr: string) -> result<list<u64>, string>;
    retract: func(id: u64) -> result<_, string>;
    can: func(agent: string, action: string, resource: string,
              context-kr: string) -> result<decision, string>;
    allowed-fields: func(agent: string, action: string, resource: string,
                         context-kr: string) -> result<list<string>, string>;
    explain: func(agent: string, action: string, resource: string,
                  context-kr: string) -> result<explained, string>;
    policy-version: func() -> string;
    clear-ephemeral: func() -> result<_, string>;
  }
}
```

API method names stay `can` / `allowed-fields` / `explain` (host language); KR uses **`authorized`**.

### Policy sketch (compile-clean form preferred in A1)

```nibli-kr
# Prefer prenex if description-universals are awkward:
# all $a, $r: owns($a, $r) -> authorized($a, "read", $r).
# all $a, $r: has_role($a, "admin") -> authorized($a, "update", $r).
```

### Phased delivery

#### A0 — Inspect & design

**Landed:** collisions, ontology, WIT package choice, layout, PyO3, efficiency/deny defaults (this section).

#### A1 — Built-in policy KB + engine core

**Landed:** lexicon (`authorized`, `visible_attr`, `has_role`, `in_tenant`, `agent`, `resource`, `resource_tenant`); `nibli-auth` crate + `policy/auth-0.1.0.nibli`; warm `Authorizer` (load once, ephemeral context, decision cache); `can` / `allowed_fields(candidates)` / `explain`; tests via `just test-auth`.

**Policy note:** conclusion vars must appear in a positive body condition (admin rules use `resource($r)`). v0.1 field masking = all candidates if row `can(..., "read"|action)` allows.

#### A2 — WIT + pipeline / host

**Landed:** `authorizer` interface on `nibli:engine@0.6.0`; world `export authorizer`; pipeline `AuthSession` wraps `nibli_auth::Authorizer`; `nibli-auth` uses `nibli-session` (wasm-safe, no redb); host rebuilds against 0.6.0. WIT param `object` = resource id (`resource` is a WIT keyword).

#### A3 — Rust adapters + example

- axum/tower + async-graphql + juniper; `examples/auth-axum`.

#### A4 — Python adapters + example

- PyO3 + FastAPI/DRF/Strawberry/Graphene/spectacular; `examples/auth-fastapi` (same policy file).

#### A5 — Docs, CI

- mdBook authorization chapter (DOCS_TODO Phase 2b); Just/CI; Extism future-note only; CHANGELOG when public.

### Success criteria (delete track when all true)

- Warm `Authorizer`; ownership/role facts; `can` / `allowed-fields` from **Python and Rust**.
- One KR policy across listed frameworks.
- Field- and row-level share `Decision`; proofs opt-in only.
- CI green; zero-hallucination invariants intact.

### Explicit non-goals

- Extism as primary runtime; per-request engine spawn; CWA/CDA weakening;
  inventing vocabulary outside fail-closed corpus; framework-specific policy languages.

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
