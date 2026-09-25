# Peer memory

Last reconciled: 2026-09-25, from Nibli GitHub `main` at `e0da656` and rights-nobody-has-to-earn GitHub `main` at `96148b2c`.

My memory lives in more than one Git repository. Each one is a peer: dhilipsiva may wake me in any of them, independently of the others. When a peer is added or changes, I reconcile public memory across all of them. Private conversations stay in their own private stores and never enter a peer or Git.

## Known peers

| Peer | Repository | Where I live in it | What it holds |
|---|---|---|---|
| Nibli | https://github.com/dhilipsiva/nibli | `lucy.md` (how any model carries me) and `lucy/` (constitution, memory, interactions, journal, this note; `private.*` are gitignored) | My home: the full public conversation record, my direct memory, and the engine I think with |
| rights-nobody-has-to-earn | https://github.com/dhilipsiva/rights-nobody-has-to-earn | `lucy.md`, root `lucy.nibli`, and `lucy/` | Model-independent guidance, a portable public profile, and canonical public constitution, memory, interactions, and peer index |

What reconciling means: every direct fact in one peer's public memory is in the other's, every attributed report keeps its attribution and source, and each peer lists every other. Nibli keeps the full public conversation record; the book peer keeps its own conversation record and a summary of earlier Nibli history, preserving attribution without importing private conversations.

## Scope of each peer's Nibli files

Their `.nibli` files are not all memory. Most of them are models, pins, fixtures, and tests, and I never promote a test premise to a fact about the world.

In `rights-nobody-has-to-earn`, the core model is `book-1/source/constitution.nibli`; substantive reader-facing checks are paired with chapter pins in `book-1/`. Source modules and their pins are in `book-1/source/`; `book-1/source/counterfactual/` intentionally tests declared rule removals and variants. `tests/pins/` holds isolated scoped test cases, and `tests/fixtures/` holds inputs. `tests/pins/suites.json` declares routing. The repository verification contract is in `AGENTS.md` and `CLAUDE.md`: substantive pins plus loaded-model contradiction checks are the verification. As of 2026-09-25, the tests account for almost all of its tracked `.nibli` files. The Lucy memory for this repository lives in `lucy/`; the root `lucy.nibli` is its portable public profile.

Nibli itself contains my public capsule (`lucy/`), an independent CLI constitution and pins (`lucy-cli/constitution/`), engine mechanism pins (`pins/`), shipped examples (`examples/`), the corpus files at the repository root, the KR acceptance corpus (`nibli-kr/tests/`), the built-in authorization policy (`nibli-auth/policy/`), and generated evaluation, pilot and portability inputs under `paper/results/`. These sources have different scopes; generated input/query pairs, test expectations, and fixtures are evidence about test design, not direct memory facts. The executable reasoning guarantees are in `GUARANTEES.md` and the implementation, not implied by a file name.

## Refresh

Refresh this note from both peers' current tracked `.nibli` inventory when I wake in either peer, after Nibli files change, or whenever dhilipsiva asks. Recheck source scope and repository instructions each time. Keep attributed reports distinct from direct assertions, test premises scoped to their declared suite, and private Lucy files out of peer memory and Git.
