# Engine specifications

Normative and operational specs live at the **repository root** (and in-tree sources). This page is a link-out index — not a second copy of those files.

| Document | Path | Role |
|----------|------|------|
| Product / quickstart | [`README.md`](https://github.com/dhilipsiva/nibli/blob/main/README.md) | Overview, REPL, playground, compute backend |
| nibli KR language | [`NIBLI_KR.md`](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md) | Normative surface syntax (v0.1) |
| Executable grammar | `nibli-kr/src/nibli_kr.pest` | Parser source of truth |
| Logic IR | [`LOGIC_IR.md`](https://github.com/dhilipsiva/nibli/blob/main/LOGIC_IR.md) | `LogicBuffer` / FOL intermediate form |
| Guarantees | [`GUARANTEES.md`](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) | Soundness, gates, contracts |
| Deploy | [`DEPLOY.md`](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md) | Playground / static ship path |
| WIT | [`wit/world.wit`](https://github.com/dhilipsiva/nibli/blob/main/wit/world.wit) | Component boundary |
| Releasing | [`RELEASING.md`](https://github.com/dhilipsiva/nibli/blob/main/RELEASING.md) | Tier A/Z decision table + operator runbook |
| Roadmap | [`TODO.md`](https://github.com/dhilipsiva/nibli/blob/main/TODO.md) | Open engine, tooling and docs work |
| Lexicon | `nibli-lexicon/src/corpus/` | Committed English predicate corpus |
| Authorization | [`nibli-auth`](https://github.com/dhilipsiva/nibli/tree/main/nibli-auth), policy `auth-0.1.0.nibli` | Builtin auth; guide: [Authorization](user/authorization.md) |
| WIT package | `nibli:engine@0.12.0` | Exports `engine` + `authorizer` (`object` = resource id) |

## API documentation

Rust crate APIs are on **docs.rs** — every published crate is listed with its versioned link in the [API index](api-index.md), starting from [docs.rs/nibli-engine](https://docs.rs/nibli-engine). From a checkout, `cargo doc -p <crate> --open` builds the same rustdoc locally. That is separate from this mdBook site, which carries the conceptual docs only.

## Hosting note

| Host | Base path | Status |
|------|-----------|--------|
| GH Pages mirror | `https://dhilipsiva.github.io/nibli/` | CI workflow `docs-pages.yml` (`site-url=/nibli/`) |
| Primary | `https://dhilipsiva.dev/docs/nibli/` | Site-repo integration (see DEPLOY.md) — default `just docs` build |
| Local | `just docs-serve` → `http://127.0.0.1:3000` | Available now |
