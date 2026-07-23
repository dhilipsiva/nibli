# Nibli KR syntax tooling

Book and tools keep the fence language as **`nibli`** / **`nibli-kr`** (never a fake
alias like `prolog`). This directory holds a **TextMate grammar** suitable as the
seed for GitHub Linguist, VS Code, and as a reference for Tree-sitter / LSP work.

| Artifact | Role |
|----------|------|
| `nibli.tmLanguage.json` | TextMate grammar (`scopeName: source.nibli`) |
| This README | Linguist path + editor injection + Tree-sitter + LSP map |
| Runtime lexer | `nibli-kr/src/highlight.rs` — already powers REPL + UI; keep scopes aligned |

Keywords must stay equal to `nibli_lexicon::RESERVED_WORDS` (and the pest
`kw_*` rules). When that list changes, update the TextMate `keyword` match and
any Tree-sitter keyword list in the same PR.

---

## 1. GitHub Linguist (github.com highlighting)

Linguist drives:

- `*.nibli` file language stats and syntax coloring on github.com
- Markdown fences: first word of the info string (` ```nibli ` or ` ```nibli-kr `)

**Repo-local overrides cannot invent a new language.** Only an upstream Linguist
merge (or a language already in Linguist) colors unknown fence tags.

### Upstream PR checklist

1. Fork [github-linguist/linguist](https://github.com/github-linguist/linguist).
2. Drop the grammar under their `vendor/grammars/` (or point a submodule at this file).
3. Add a language entry (YAML shape — IDs assigned by maintainers):

```yaml
Nibli:
  type: programming
  color: "#1B6B93"   # pick a stable brand color
  extensions:
  - ".nibli"
  tm_scope: source.nibli
  ace_mode: text
  codemirror_mode: null
  aliases:
  - nibli-kr
  - nibli kr
  - nibliKR
```

4. Ship samples (real corpus lines, not toy fragments) under their samples tree —
   e.g. excerpts from `gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli`.
5. Run their heuristic / sample tests; open a PR per
   [CONTRIBUTING](https://github.com/github-linguist/linguist/blob/main/CONTRIBUTING.md).

**Book fence policy:** keep `nibli-kr` (or migrate tools + book together to plain
`nibli`). Register **both** as Linguist aliases so either fence highlights after
merge.

Until Linguist merges: github.com shows plain monospaced text for those fences;
local editors can still highlight via the extension path below.

---

## 2. Editor injections (VS Code / Cursor / VSCodium)

### Full language extension (files)

Minimal `package.json` contributions:

```json
{
  "name": "nibli",
  "contributes": {
    "languages": [
      {
        "id": "nibli",
        "aliases": ["Nibli KR", "nibli-kr"],
        "extensions": [".nibli"],
        "configuration": "./language-configuration.json"
      }
    ],
    "grammars": [
      {
        "language": "nibli",
        "scopeName": "source.nibli",
        "path": "./syntaxes/nibli.tmLanguage.json"
      }
    ]
  }
}
```

Copy `nibli.tmLanguage.json` into the extension’s `syntaxes/` folder.

`language-configuration.json` (brackets, comments):

```json
{
  "comments": { "lineComment": "#", "blockComment": ["/*", "*/"] },
  "brackets": [["(", ")"], ["[", "]"], ["{", "}"]],
  "autoClosingPairs": [
    { "open": "(", "close": ")" },
    { "open": "[", "close": "]" },
    { "open": "{", "close": "}" },
    { "open": "\"", "close": "\"" }
  ]
}
```

### Markdown fence injection (book / docs)

GitHub does not use this. VS Code does: inject `source.nibli` into fenced blocks
whose info string is `nibli` or `nibli-kr`.

Second grammar contribution:

```json
{
  "scopeName": "markdown.nibli.codeblock",
  "path": "./syntaxes/nibli-markdown-injection.json",
  "injectTo": ["text.html.markdown"],
  "embeddedLanguages": {
    "meta.embedded.block.nibli": "nibli"
  }
}
```

`nibli-markdown-injection.json` (sketch):

```json
{
  "scopeName": "markdown.nibli.codeblock",
  "injectionSelector": "L:text.html.markdown",
  "patterns": [
    {
      "begin": "(^|\\G)(\\s*)(\\`{3,}|~{3,})\\s*(?i:(nibli(?:-kr)?)(\\s+[^`~]*)?$)",
      "end": "(^|\\G)(\\2|\\s{0,3})(\\3)\\s*$",
      "beginCaptures": {
        "3": { "name": "punctuation.definition.markdown" },
        "4": { "name": "fenced_code.block.language.markdown" }
      },
      "endCaptures": {
        "3": { "name": "punctuation.definition.markdown" }
      },
      "name": "markup.fenced_code.block.markdown",
      "contentName": "meta.embedded.block.nibli",
      "patterns": [{ "include": "source.nibli" }]
    }
  ]
}
```

Reference implementation pattern:
[vscode-fenced-code-block-grammar-injection-example](https://github.com/mjbvz/vscode-fenced-code-block-grammar-injection-example).

### Other editors

| Editor | Path |
|--------|------|
| **Neovim** | Tree-sitter parser + `nvim-treesitter` (preferred) or TextMate via `nvim-treesitter` fallback / `helix`-style grammars |
| **Helix** | Tree-sitter only — needs a `.scm` queries + grammar crate |
| **Zed** | Tree-sitter extension |
| **Sublime** | Drop the `.tmLanguage.json` in a package |
| **JetBrains** | TextMate bundle plugin or custom TextMate support |

---

## 3. Tree-sitter integrations

Tree-sitter is a **GLR-ish incremental parser** used by Neovim, Helix, Zed, GitHub
code search (partially), and some LSP semantic tokens backends. It is **not**
what github.com uses for Markdown fences (Linguist/TextMate is).

### Why add it

- Accurate folds, indents, locals, and injection into Markdown
- Better than regex TextMate for nested claims / parens
- Shared core for editor + optional LSP semantic tokens

### Scaffold (not shipped yet)

```
tree-sitter-nibli/
  grammar.js          # or grammar.json
  src/scanner.c       # only if external scanner needed
  queries/
    highlights.scm
    locals.scm
    injections.scm    # markdown → nibli fences
  package.json
  Cargo.toml          # if rust binding
```

`grammar.js` should track `nibli-kr/src/nibli_kr.pest` **by discipline**, not by
auto-generation (pest ≠ tree-sitter). Start with a lexer-faithful subset:

- comments `#` / `/* */`
- `statement` = claim + `.`
- keywords / `$var` / `Name` / numbers / strings
- operators `& | ^ -> <-> ~ =`
- predications `pred(args)` and `via tag(...)`

`highlights.scm` map nodes → standard capture names:

```scheme
(comment) @comment
(keyword) @keyword
(variable) @variable
(name) @constant
(predicate) @function
(number) @number
(string) @string
(operator) @operator
```

### Integration targets

| Consumer | Notes |
|----------|--------|
| **nvim-treesitter** | Register parser + queries; `filetype = nibli` for `*.nibli` |
| **Helix** | `languages.toml` + grammar source |
| **Zed** | Extension with tree-sitter grammar |
| **GitHub** | Linguist still wants TextMate for the classic highlighter path |

Keep TextMate **and** Tree-sitter until Linguist accepts the TextMate grammar;
do not block github.com on Tree-sitter alone.

---

## 4. LSP (Language Server Protocol)

An LSP does **not** replace highlighting by itself (clients still need a grammar
or semantic tokens), but it is the path to real tooling:

| Feature | Source |
|---------|--------|
| Diagnostics | `nibli_kr::parse_checked` + emit/resolve errors (positioned) |
| Hover | `nibli_lexicon` gloss / places / template for predicates |
| Completion | reserved keywords + corpus names + place labels after `label:` |
| Go-to / refs | optional later (KB-wide harder than single-file) |
| Format | `nibli_kr::render` round-trip (canonical respell) |
| Semantic tokens | map highlight lexer or Tree-sitter to LSP token types |

### Recommended shape

```
nibli-lsp/                 # workspace bin crate
  src/main.rs              # tower-lsp or lsp-server
  uses:
    nibli-kr               # parse_checked, render, highlight::lex
    nibli-lexicon          # gloss / arity / compounds
    nibli-semantics        # optional deeper diagnostics
```

**Start thin:** open document → `parse_checked` → publish diagnostics; complete
from lexicon; hover gloss. Defer multi-file KB projects.

**Semantic tokens alternative to TextMate:** implement
`textDocument/semanticTokens/full` using `nibli_kr::highlight::lex` (already
exists). Editors that prefer semantic tokens can skip the TextMate grammar for
`.nibli` files; Markdown fences still need injection or a dual path.

### Relationship to the three layers

```
                    ┌─────────────────────┐
  github.com        │ Linguist + TextMate │  ← grammars/nibli.tmLanguage.json
                    └─────────────────────┘
  VS Code / Cursor  │ TextMate + injection│  ← same grammar + md injection
                    │ optional nibli-lsp  │
                    └─────────────────────┘
  Neovim / Helix    │ Tree-sitter         │  ← tree-sitter-nibli (future)
                    │ optional nibli-lsp  │
                    └─────────────────────┘
  REPL / nibli-ui   │ highlight.rs lexer  │  ← already shipped
                    └─────────────────────┘
```

Canonical lexer for *runtime* surfaces stays `nibli-kr/src/highlight.rs`.
TextMate / Tree-sitter are editor/platform ports — keep token classes aligned
(`keyword`, `predicate`, `name`, `variable`, `number`, `comment`, `operator`).

---

## 5. Fence name policy

| Surface | Tag |
|---------|-----|
| Book + `verify_book.py` | `nibli-kr` (today) — keep `nibli*` identity, no foreign language alias |
| Linguist aliases | `nibli`, `nibli-kr`, `nibli kr` |
| File extension | `.nibli` |
| VS Code language id | `nibli` |

If the book ever renames fences to plain `nibli`, change the book tools and
injection begin-regex in one PR.
