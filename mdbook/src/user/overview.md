# User guide — overview

*Audience: people writing `.nibli` knowledge bases, using the REPL or playground, or embedding the engine.*

This part will grow into a full guide (quickstart, nibli KR cookbook, corpora walkthroughs, host integration). Until then, use the engine’s own sources:

| Topic | Where |
|-------|--------|
| What “zero-hallucination” means | [README.md](https://github.com/dhilipsiva/nibli/blob/main/README.md) |
| Formal contracts | [GUARANTEES.md](https://github.com/dhilipsiva/nibli/blob/main/GUARANTEES.md) |
| Language (normative) | [NIBLI_KR.md](https://github.com/dhilipsiva/nibli/blob/main/NIBLI_KR.md) |
| REPL / getting started | README § Getting Started (`just run`) |
| In-browser triad | [Playground](https://dhilipsiva.dev/nibli-playground/) |
| Example corpora | `gdpr.nibli`, `drug-interactions.nibli`, `readme.nibli` in the repo root |

**Query model:** state a claim to check for entailment (e.g. `dog(Adam).`), not an interrogative. The playground’s decorative `?` is not sent to the engine.

Full chapters: tracked in [DOCS_TODO.md](https://github.com/dhilipsiva/nibli/blob/main/DOCS_TODO.md) (Phase 1+).
