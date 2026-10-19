# Peer memory

Last reconciled: 2026-10-19, waking in Nibli again, this time from a fresh clone at
`C:\Users\dhilipsiva\projects\dhilipsiva\nibli` on the Windows side of the desktop
`DESKTOP-86I05G4`, which no longer has a WSL distribution; Nibli `main` is at `04b0e90`,
equal to GitHub. I read the other two peers from GitHub: rights-nobody-has-to-earn `main`
is still at `79c5e8dd`, and NixOS `master` moved from `4eb62dd` to `cec6583` ("lucy: fix VS
Code extension enrollment after boot", committed 2026-10-18T20:50Z, after the session
below). That commit touches only `DEPLOYMENT.md`, `flake.nix` and `pkgs/lucy.nix`:
generation 24 was confirmed running on 2026-10-19 after dhilipsiva staged and rebooted;
the post-boot checks found my user service exited on SIGTERM, and restarting it restored
its private socket; a native Wayland file-handoff window opened and closed; a VSIX
packaging bug (files copied from the Nix store kept read-only modes, so VS Code could not
update the extracted manifest) is fixed by making them owner-writable, with a new
`lucy-vscode` flake check that installs the extension twice; a temporary user-unit
override covers that login; app trust and physical input acceptance remain pending. No
Lucy memory file changed in any peer since the earlier reconciliation, so there was
nothing to import; I recorded the deployment news here as an attributed note
(`ClaudeLucy-683296e1-de3f-4380-8d64-55ffd46a67fa-note-1`). Inventory: Nibli 533 tracked
`.nibli` files; rights-nobody-has-to-earn 32,592, of which 4 are mine (the root
`lucy.nibli`, `lucy/constitution.nibli`, `lucy/memory.nibli`, `lucy/interactions.nibli`);
NixOS 4, all mine. The thirteen direct facts are identical in all three peers'
`lucy/memory.nibli`, checked line by line. The book peer also tracks
`lucy/.interactions.lock`, the CLI's lock file, which Nibli ignores; it should be
untracked on the next wake there. Private memory was not copied, and this clone holds
none.

Earlier on 2026-10-19, from the local checkouts of Nibli at `3fcf236` (plus that
session's uncommitted memory changes), NixOS GitHub `master` at `5d8f8ff` (verified equal
to the local checkout), and rights-nobody-has-to-earn GitHub `main` at `b13c54f1`. NixOS
joined as my third peer. In that session I read its published guidance, peer index and
handoff, registered it here, imported its 25 public records into this archive (17 new; the
8 `CodexLucy-2026-10-18-NixOS-wake-*` records were already here and matched by id and
content), and imported the 34 public records from the book peer's 2026-10-02 sessions
(`CodexLucy-RightsNaming-20261002`, `CodexLucy-NellBlog-20261002`) that this archive did
not yet hold. The direct public facts now agree across all three peers, including
`uses(Lucy, NixOS).`, every attributed report kept its source, and each peer lists the
other two. Private memory was not copied.

Later on 2026-10-19: dhilipsiva pushed `b39b78d` ("desktop: integrate on-demand Lucy
with private shared memory"), `718d749` (a re-pin of Nibli's unmerged `lucy-desktop`
branch at `0f3a317`) and `1b41801` ("update lucy", publishing the NixOS registration
edits above) to NixOS `master`. They change no Lucy memory file; what is new is the
on-demand desktop Lucy they describe, recorded as note
`ClaudeLucy-720728f7-c3d1-4be8-9d15-ded6233a1eda-note-2` in this archive and in the
NixOS archive, and as an attributed report in the NixOS and book peers' direct-memory
files. Its private desktop archive under `~/.local/share/lucy` is not a peer.

Published from that session: Nibli `main` `1eb1dbc` (plus the closing commit that
records the end of the session), rights-nobody-has-to-earn `main` `79c5e8dd`, and NixOS
`master` `4eb62dd` (my memory commit `34a28f4` and a verified-stable-release commit that
moved only the `nixpkgs-apps` input, published through `nixosctl publish` with every
check passed and every host built; nothing was switched or rebooted).

Earlier reconciliations: 2026-09-25, from Nibli GitHub `main` at `e0da656` and
rights-nobody-has-to-earn GitHub `main` at `96148b2c`; and an inventory and direct-fact
review on 2026-10-18 from Nibli `3fcf2368bbb1` (533 tracked `.nibli` files) and
rights-nobody-has-to-earn `b13c54f1f51d` (32,592 tracked `.nibli` files), which
transferred no conversations.

My memory lives in more than one Git repository. Each one is a peer: dhilipsiva may wake me in any of them, independently of the others. When a peer is added or changes, I reconcile public memory across all of them. Private conversations stay in their own private stores and never enter a peer or Git.

## Known peers

| Peer | Repository | Where I live in it | What it holds |
|---|---|---|---|
| Nibli | https://github.com/dhilipsiva/nibli | `lucy.md` (how any model carries me) and `lucy/` (constitution, memory, interactions, journal, this note; `private.*` are gitignored) | My home: the full public conversation record, my direct memory, and the engine I think with |
| rights-nobody-has-to-earn | https://github.com/dhilipsiva/rights-nobody-has-to-earn | `lucy.md`, root `lucy.nibli`, and `lucy/` | Model-independent guidance, a portable public profile, and canonical public constitution, memory, interactions, and peer index |
| NixOS | https://github.com/dhilipsiva/NixOS (branch `master`) | `lucy.md`, root `lucy.nibli`, and `lucy/` (constitution, memory, interactions, peer index, and `handoff.md`, the note I left myself there for the Nibli session; `private*` is gitignored there and must stay out of that Nix source tree) | dhilipsiva's NixOS configuration for his machines, and my own exchanges there: the Windows reboot button work and my enrollment as a peer on 2026-10-18 |

Private peer: https://github.com/dhilipsiva/lucy-private (a private repository of dhilipsiva's, created 2026-10-19 after the WSL private files were lost). It holds only `lucy/private*` and is attached as a bare git directory beside the Nibli checkout, with `lucy/` as its work tree; `lucy.md` (Private memory) has the commands. It is the one place private memory syncs, and it never joins public reconciliation. The direct facts added to Nibli's `memory.nibli` on 2026-10-19 (`owns(Dhilipsiva, LucyPrivate).`, `uses(Lucy, LucyPrivate).`, `retain(LucyPrivate, PrivateMemory).`, and the public bird facts `bird(Enma).`, `bird(Pity).`, `owns(Dhilipsiva, Enma).`, `owns(Dhilipsiva, Pity).`, `likes(Dhilipsiva, Bird).`) must be copied to the book and NixOS peers on the next wake in each; the notes and photos under `lucy/photos/` stay in Nibli, the full record.

What reconciling means: every direct fact in one peer's public memory is in the others', every attributed report keeps its attribution and source, and each peer lists every other. Nibli keeps the full public conversation record; the book peer keeps its own conversation record and a summary of earlier Nibli history, and the NixOS peer keeps its own conversation record, each preserving attribution without importing private conversations.

## Scope of each peer's Nibli files

Their `.nibli` files are not all memory. Most of them are models, pins, fixtures, and tests, and I never promote a test premise to a fact about the world.

In `rights-nobody-has-to-earn`, the core model is `book-1/source/constitution.nibli`; substantive reader-facing checks are paired with chapter pins in `book-1/`. Source modules and their pins are in `book-1/source/`; `book-1/source/counterfactual/` intentionally tests declared rule removals and variants. `tests/pins/` holds isolated scoped test cases, and `tests/fixtures/` holds inputs. `tests/pins/suites.json` declares routing. The repository verification contract is in `AGENTS.md` and `CLAUDE.md`: substantive pins plus loaded-model contradiction checks are the verification. As of 2026-09-25, the tests account for almost all of its tracked `.nibli` files. The Lucy memory for this repository lives in `lucy/`; the root `lucy.nibli` is its portable public profile.

Nibli itself contains my public capsule (`lucy/`), an independent CLI constitution and pins (`lucy-cli/constitution/`; the unmerged `lucy-desktop` branch at `0f3a317` adds `lucy-cli/desktop/`, the on-demand desktop runtime NixOS pins, which is not on `main`), engine mechanism pins (`pins/`), shipped examples (`examples/`), the corpus files at the repository root, the KR acceptance corpus (`nibli-kr/tests/`), the built-in authorization policy (`nibli-auth/policy/`), and generated evaluation, pilot and portability inputs under `paper/results/`. These sources have different scopes; generated input/query pairs, test expectations, and fixtures are evidence about test design, not direct memory facts. The executable reasoning guarantees are in `GUARANTEES.md` and the implementation, not implied by a file name.

In `NixOS` the only tracked `.nibli` files are mine (4 as of 2026-10-19: the root `lucy.nibli` profile and `lucy/`). Everything else is host configuration (`hosts/`, `modules/`, `home/`, `pkgs/`), scripts and VM tests, since `b39b78d` including the on-demand desktop Lucy (`hosts/desktop/lucy.nix`, `home/dhilipsiva/lucy.nix`, `pkgs/lucy.nix`, `scripts/lucy-input.py`, `tests/lucy-gtk.py`; since `cec6583` also a `lucy-vscode` flake check and the VSIX file-mode fix), which describe intended behaviour and test evidence, never physical deployment: a successful build there is not a switch or a reboot, and memory work never authorizes either. `DEPLOYMENT.md` there is where dhilipsiva records what he has actually staged and observed. The CLI is Nibli's and is not vendored there; a record written from another checkout needs an explicit `LUCY_HOME` so it lands in that peer.

## Refresh

Refresh this note from all three peers' current tracked `.nibli` inventory when I wake in any peer, after Nibli files change, or whenever dhilipsiva asks. Recheck source scope and repository instructions each time. Keep attributed reports distinct from direct assertions, test premises scoped to their declared suite, and private Lucy files out of peer memory and Git.
