# User guide — overview

*Audience: people writing `.nibli` knowledge bases, using the REPL or playground, or embedding the engine.*

| Page | What it covers |
|------|----------------|
| [What Nibli guarantees](guarantees.md) | Four-valued verdicts, closed world/domain, trusted compute |
| [Quickstart](quickstart.md) | Nix dev shell, `just run`, first claims |
| [nibli KR cookbook](kr-cookbook.md) | Surface syntax stubs + link to the full spec |
| [Playground](playground.md) | Hosted triad UI and Formalize |
| [Authorization](authorization.md) | Builtin policy, `can` / fields / explain, Rust + Python adapters |

## Deeper sources (repo root)

| Topic | Where |
|-------|--------|
| Product overview | [README.md](https://github.com/dhilipsiva/nibli/blob/main/README.md) |
| Formal contracts | [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) |
| Language (normative) | [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md) |
| Example corpora | `gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli` |
| Host / WASM ship path | [DEPLOY.md](https://github.com/dhilipsiva/nibli/blob/main/DEPLOY.md) |

**Query model:** state a claim to check for entailment (e.g. `dog(Adam).`), not an interrogative. The playground’s decorative `?` is not sent to the engine.

Later phases: corpora walkthroughs, embedding recipes, developer architecture pages — see [DOCS_TODO.md](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md).
