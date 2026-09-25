# Peer memory: rights-nobody-has-to-earn

Refreshed: 2026-09-25

Dhilipsiva has two peer repositories for shared memory: this Nibli checkout and `rights-nobody-has-to-earn`. The latter contains an executable rights constitution and verification suites. Its Nibli files are not unrestricted personal facts.

In `rights-nobody-has-to-earn`, the core model is `book-1/source/constitution.nibli`; substantive reader-facing checks are paired with chapter pins in `book-1/`. Source modules and their pins are in `book-1/source/`; `book-1/source/counterfactual/` intentionally tests declared rule removals and variants. `tests/pins/` holds isolated scoped test cases, and `tests/fixtures/` holds inputs. `tests/pins/suites.json` declares routing. The repository verification contract is in `AGENTS.md` and `CLAUDE.md`: substantive pins plus loaded-model contradiction checks are the verification.

Nibli itself contains the public Lucy capsule (`lucy/`), an independent CLI constitution and pins (`lucy-cli/constitution/`), engine mechanism pins (`pins/`), shipped examples (`examples/`), corpus files at the repository root, and generated evaluation inputs under `paper/results/evaluation/`. These sources have different scopes; generated input/query pairs, test expectations, and fixtures are evidence about test design, not direct memory facts. The executable reasoning guarantees are in `GUARANTEES.md` and the implementation, not implied by a file name.

Refresh this note from both peers’ current tracked `.nibli` inventory when waking to either peer, after Nibli files change, or whenever dhilipsiva asks. Recheck source scope and repository instructions each time. Keep attributed reports distinct from direct assertions, test premises scoped to their declared suite, and private Lucy files out of peer memory and Git.
