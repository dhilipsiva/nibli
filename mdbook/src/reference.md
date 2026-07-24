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
| Docs roadmap | [`DOCS_TODO.md`](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md) | This site’s build-out tracker |
| Lexicon | `nibli-lexicon/src/corpus/` | Committed English predicate corpus |

## API documentation

Rust crate APIs: `cargo doc -p <crate> --open` (for example `nibli-types`, `nibli-kr`, `nibli-reason`). **docs.rs** will host the same rustdoc when crates are published to crates.io — that is separate from this mdBook site.

## Hosting note

| Host | Base path | Status |
|------|-----------|--------|
| Primary | `https://dhilipsiva.dev/docs/nibli/` | Phase 1 deploy |
| GH Pages mirror | `https://dhilipsiva.github.io/nibli/` | Phase 1 deploy |
| Local | `just docs-serve` → `http://127.0.0.1:3000` | Available now |
