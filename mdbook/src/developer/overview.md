# Developer guide — overview

*Audience: contributors to the compiler, reasoner, host, and CI gates.*

This part will cover the crate map, pipeline/IR, WASM host, and soundness workflow. Until then:

| Topic | Where |
|-------|--------|
| Logic IR | [LOGIC_IR.md](https://github.com/dhilipsiva/nibli/blob/main/LOGIC_IR.md) |
| KR surface + pest grammar | [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md), `nibli-kr/src/nibli_kr.pest` |
| Soundness contracts | [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) |
| Architecture / crate roles | [CLAUDE.md](https://github.com/dhilipsiva/nibli/blob/main/CLAUDE.md) (engine map) |
| Native CI gate | `just ci` (and `just ci-wasm` / `just ci-all`) |
| Deploy / playground ship | [DEPLOY.md](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md) |
| WIT boundary | `wit/world.wit` |

Do not use the private `book/` manuscript as a contributor reference for shipped behavior — prefer tests, gates, and the files above.

Full chapters: [DOCS_TODO.md](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md) (Phase 3).
