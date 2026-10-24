# Releasing nibli

The operator runbook AND the decisions of record it executes. (Both used to be
split — the decisions lived in `DOCS_TODO.md`, which retired 2026-08-03 once the
docs and release tracks landed; the still-live half moved here.)

## Invariants

- **Lockstep.** All 13 publishable (Tier A) crates share one version. There is
  no per-crate semver.
- **Tags are `vX.Y.Z`.** The tag carries the `v`; the manifest never does.
- **The WIT ABI version is independent** of crate semver (`nibli:engine@…` in
  `wit/world.wit`). Bumping one does not imply bumping the other.
- **0.x may break on a minor.** Every release documents its changes in
  [CHANGELOG.md](CHANGELOG.md) first.
- Two version literals sit outside the lockstep **by design**, and
  `just release-check` asserts both: `fuzz/` is workspace-excluded and pinned
  at `0.0.0`, and `nibli-auth-py`'s wheel version is maturin-`dynamic` from
  Cargo.toml.

## Tier A / Tier Z — the publish decision table

The decision of record for *which* crates go to crates.io. `just release-check`
asserts the `publish` flag of every member against it, and each Tier Z manifest
repeats its own reason in a comment at the top.

| Tier | Crates | Ships as |
|------|--------|----------|
| **A — published**, in dependency order | `nibli-types` → `nibli-lexicon` → `nibli-protocol` → `nibli-kr` → `nibli-semantics` → `nibli-reason` → `nibli-render` → `nibli-session` → `nibli-store` → **`nibli-engine`** → `nibli-formalize` / `nibli-import` / `nibli` | crates.io → docs.rs |
| **Z — `publish = false`** | `nibli-pipeline`, `nibli-host`, `nibli-ui`, `nibli-wasm`, `nibli-verify`, `tools/lexigen`, `fuzz` | GitHub Release, the site, or repo-only |

`nibli-auth` and `nibli-auth-py` are also `publish = false` for now.

**Out of scope for any release:** manuscript / Orange AVA material in a release
asset; crates.io for the ui/wasm/playground bundles (site only); and equating
crate semver with the WIT ABI version — the two move independently.

## The two gates

| Gate | Question | Runs |
|------|----------|------|
| `just release-check` | *Is the workspace structurally releasable?* Version-agnostic — true on every ordinary commit. | Part of `just ci` |
| `just release-verify X.Y.Z` | *Is this tree exactly X.Y.Z and ready to ship?* Version-specific — false on every ordinary commit. | Release moment only |

`release-verify` is deliberately cargo-free and offline, so the release
workflow's preflight can run it before any toolchain starts.

## Cutting a release

```bash
just release-prep 0.2.0     # bumps versions, rolls the CHANGELOG, refreshes the lock
git diff                    # REVIEW — nothing has been committed or tagged
just ci-all
git commit -am 'release(v0.2.0): <summary>'
git push origin main        # let CI go green BEFORE tagging
git tag -a v0.2.0 -m 'v0.2.0' && git push origin v0.2.0
```

The tag push runs [`.github/workflows/release.yml`](.github/workflows/release.yml),
which does the rest: preflight → gates + artifacts (3 platforms + the wasm
component) → **draft** GitHub Release → **crates.io** → undraft.

`release-prep` refuses rather than pretending to be idempotent. Undo it with:

```bash
git checkout -- Cargo.toml Cargo.lock CHANGELOG.md
```

**Rehearse any time.** Actions → Release → *Run workflow*. A manual run is
always a dry run — it exercises the gates, builds all three platforms, packages
and verify-builds every crate tarball, and renders the release notes into the
step summary, without creating a release or publishing anything.

## Reversibility — read before tagging

| Artifact | Reversible? | How | Constraint |
|----------|-------------|-----|------------|
| Local commit | yes | `git reset` | before push |
| Git tag | conditionally | `git tag -d vX.Y.Z && git push origin :refs/tags/vX.Y.Z` | **only while crates.io is untouched at X.Y.Z** |
| GitHub Release | yes | `gh release delete vX.Y.Z` | same constraint |
| **crates.io version** | **NO** | — | no delete, no overwrite, and the number is consumed **forever** |
| docs.rs build | no (follows crates.io) | — | rebuildable, not deletable |

This is why the workflow does every reversible thing first and keeps the
release a **draft** until crates.io has succeeded. Once even one of the 13
crates is live at X.Y.Z, the tag is frozen: it must keep pointing at exactly
what was published, and the only way forward is another version.

## Yank policy

**What `cargo yank --version X.Y.Z <crate>` does:** marks a version so new
dependency resolution won't select it. That is the entire effect.

**What it does not do:** it does not delete anything (the tarball stays
downloadable), it does not break existing `Cargo.lock` files that already pin
it, it does not free the version number, and it does not remove docs.rs pages.
It is reversible with `cargo yank --undo`.

**Default: publish a patch. Do not yank.** A patch is additive, is itself
reversible by another patch, and breaks nobody's lock.

**Yank only when the published artifact actively harms a fresh consumer:**

- it does not build at all from the published tarball;
- it contains a leaked secret or a security vulnerability;
- it was published from the wrong commit or a dirty tree;
- its lockstep set is incomplete (see *Partial-publish recovery*).

**Never yank** for a docs typo, a CHANGELOG error, wrong metadata, or to free a
version number — that last one does not work.

**Publish the replacement first**, confirm it is live, *then* yank. Yanking
first makes fresh resolution fall back to the previous version, which during
0.x can drop a consumer across an API break they never asked for.

**Yank all 13 or none.** A partial yank leaves an incoherent lockstep tuple.
Yank top-down (`nibli`, `nibli-engine` first; `nibli-types` last) so no
intermediate moment resolves to a half-yanked graph.

## Hotfix

```bash
git switch -c hotfix/0.2.1 v0.2.0     # branch from the TAG, never from main
```

`main` may carry unreleased breaking work; the point of a hotfix is a minimal,
auditable delta from what shipped.

1. Land the minimal fix; add its entry under `## [Unreleased]`.
2. `just release-prep 0.2.1` — this is why the recipe only *warns* on a
   non-`main` branch instead of refusing.
3. `just ci-all`, commit, tag `v0.2.1`, push branch and tag.
4. **Merge back to `main` immediately** (below).

**The cost, stated honestly.** Lockstep means a one-line fix in one crate
republishes **all 13** at 0.2.1 — 13 crates.io versions and 13 docs.rs builds,
12 of which have an empty diff. That is the deliberate price of the lockstep
decision: any `(nibli-*, X.Y.Z)` tuple is a coherent set, so nobody ever has to
reason about a compatibility matrix across 13 crates. If that price becomes
intolerable, the exit is per-crate semver — a change to the Invariants above,
made deliberately, not an improvisation during a hotfix.

**Merge-back (the step people skip).** Cherry-pick the *fix* commit onto
`main`; do not merge the release commit. Then hand-edit `main`'s CHANGELOG:

- insert the `## [0.2.1]` section below `[Unreleased]` and above `## [0.2.0]`;
- add the `[0.2.1]: …/releases/tag/v0.2.1` link ref;
- **repoint `[Unreleased]` at the newest tag**: `compare/v0.2.1...HEAD`. This
  is the most-missed line — nothing on `main` verifies it, because
  `release-verify` only ever ran on the hotfix branch.
- Leave `main`'s `[workspace.package].version` alone.

## Partial-publish recovery

**Symptom:** the `publish` job aborted after N of 13.

**First response: re-run the job.** `just release-publish` probes the sparse
index and excludes what is already live, so a re-run resumes. Most aborts
(rate limit, network, index-propagation timeout) clear on the second run.

**Never bump the version to "start clean."** The N crates already uploaded at
X.Y.Z are permanent, and bumping orphans them forever.

**If the abort was a real defect** (a crate does not build from its own
tarball):

1. Fix on `main`, or on a hotfix branch off the tag.
2. `just release-prep X.Y.(Z+1)` and release the full 13 at the new version.
3. **Yank all N partial uploads at X.Y.Z.** This is the case where yanking is
   mandatory: the X.Y.Z tuple can never be completed, so a consumer who
   resolves one crate and cannot get its sibling is stuck permanently.
4. Leave the tag and its Release in place — they describe what was published,
   which is the truth. Edit the notes to say *"crates.io publish incomplete —
   use X.Y.(Z+1)."*

`just ci-all` and the rehearsal's `cargo publish --dry-run` exist to prevent
this. A tarball-verification failure caught in rehearsal costs five minutes;
caught at crate 7 of 13 it costs a version number and 13 yanks.

## Two gotchas that have bitten real projects

- **Never re-cut a tag after any successful publish.** Deleting and re-pushing
  `v0.2.0` after crates.io has it produces a green run (everything is excluded
  as already-live) while the artifacts silently diverge from what shipped. Bump
  the patch instead.
- **"Re-run failed jobs" uses the workflow file from that run's commit.** If
  you fix `release.yml` on `main` and re-run an old failed run, you re-run the
  *old, broken* file. To pick up a workflow fix you must delete the tag and
  re-push it at a commit that contains it — which is only safe if nothing was
  published yet.

## Credentials and rate limits

- `CARGO_REGISTRY_TOKEN` must exist as a repo secret before any real tag; scope
  it `publish-update` on the Tier A crates and give it an expiry. The workflow
  fails loudly (never silently skips) when it is missing, and separately checks
  the token is *live* before publishing — a revoked token would otherwise fail
  mid-upload.
- crates.io has two buckets. **New versions of existing crates** are generous —
  a normal release does not strain it. **Brand-new crates** are not: burst 5,
  then roughly one per 10 minutes (this is what the first-ever publish hit).
  So **publish any newly-added Tier A crate manually once** before its first
  automated release; `just release-publish` warns when a crate is absent from
  the index at every version.

## After a release

- Spot-check docs.rs builds a few hours later — the `finalize` job writes the
  13 build URLs into the run summary.
- README badges are live shields.io endpoints; they need no edit.
- The playground redeploys via the existing `nibli-updated` dispatch on the
  push to `main`, not the tag.
- Nothing to update in a tracker: `DOCS_TODO.md` retired, and [TODO.md](TODO.md)
  is future-facing by rule (an entry is deleted when it lands, with the record
  going into the commit), so a release leaves it alone unless it unblocks an
  open entry.
