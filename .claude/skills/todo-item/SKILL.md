---
name: todo-item
description: Work a single item from TODO.md end-to-end — plan, implement, test/verify, then remove it from TODO.md (or update it if only partially done), commit, and push. Use when the user points to a specific TODO.md item to execute, one item at a time.
---

# Work one TODO.md item

Drive a single `TODO.md` item from "named" to "committed and pushed." Do exactly one item per
invocation — never batch. The user hands you the next item when this one lands.

The user names or quotes an item (often pasted, sometimes a keyword/section reference). Default file is
`book/TODO.md`. If the reference is ambiguous, could match more than one item, or points at a different
`TODO.md`, ask which item/file before doing anything.

## Environment

This project lives on WSL2 (Ubuntu); the Windows working dir does not exist on the Linux side. Run every
shell command through the wrapper:

```
wsl -d Ubuntu -e bash -lc "cd ~/projects/dhilipsiva/nibli && <CMD>"
```

For anything needing the toolchain (`cargo`, `just`, `wasmtime`), use the Nix dev shell:

```
wsl -d Ubuntu -e bash -lc "cd ~/projects/dhilipsiva/nibli && nix --extra-experimental-features 'nix-command flakes' develop --command bash -c '<CMD>'"
```

The book is its own git repo at `book/` (gitignored from the parent), worked from the parent context.
Operate git in whichever repo owns the files the item touches (book vs nibli).

## The loop

1. **Locate & plan.** Find the exact item in `TODO.md`. Read the `file:line` locations it cites plus the
   relevant source/manuscript files — line numbers drift, so confirm by reading, and grep the quoted
   strings rather than trusting line numbers. For book items, ground every change in the real Nibli
   code/tests per [`book/CLAUDE.md`](../../../book/CLAUDE.md); do not invent code or output. State a
   one-paragraph approach for non-trivial items. Pause and ask **only** if the item is genuinely
   ambiguous or needs a product/design decision — otherwise proceed through the whole loop.

2. **Implement.** Follow the conventions of the file you're editing:
   - **Book prose** — house style in [`book/CLAUDE.md`](../../../book/CLAUDE.md): closed em-dashes (no
     spaces), the Epistemic Discipline rules (precise four-valued contract; never inflate the guarantee),
     Adam/adam consistency (cmevla-morphology exception only in Ch 4), Lojban-as-IR framing, the
     `CURRENT ENGINE` / `IMPLEMENTED` / `FUTURE DIRECTION` callout labels, "evolved" not "designed" for
     natural languages, no "dead end" overclaiming, functional/typed-term notation (never LISP S-expr),
     and never conflate robotic glossing with semantic verification.
   - **Engine code** — conventions in the parent [`CLAUDE.md`](../../CLAUDE.md) (test with
     `cargo test --lib`, not `cargo test`; logji tests need `--test-threads=1`; etc.).

3. **Test / verify.** Run the verification that fits the item and report its output faithfully — never
   claim success without running it:
   - **Book** prose/vocab/transcript items: `just verify-book-vocab` and/or `just verify-book-capture`
     (≡ `verify_book.py`, `capture_book.py --check`). Then re-grep the specific defect to confirm it is
     gone (e.g. `grep -n "<old phrase>" book/<chapter>.md`).
   - **Engine** items: `just ci` (fmt-check, clippy, native suites) plus targeted `just test-*`; add
     `just ci-wasm` when WASM behavior is involved.
   - Always re-read / re-grep to confirm the change actually does what the item asked.
   - If verification fails, fix and re-verify. **Do not commit broken work.**

4. **Update `TODO.md`.**
   - Fully done → delete the bullet entirely. No `~~strikethrough~~`, no "DONE" marker — remove it.
   - Partial → rewrite the item to state exactly what remains (never leave a stale claim that something
     is unimplemented when half of it shipped).
   - Already stale/done on inspection → say so and just remove it.

5. **Sync docs.** Per the repo's pre-commit checklist: book → update `book/CLAUDE.md` / `book/README.md`
   if Lojban coverage or reasoning capability changed; engine → `CLAUDE.md` / `README.md` as needed.
   Commit doc changes together with the item.

6. **Commit & push.** In the repo that owns the edited files:
   - Write the commit message to a temp file and `git commit -F /tmp/msg.txt`. Heredocs and `-m` mangle
     backticks / `?` / quotes inside the double-quoted `bash -lc` wrapper — the file avoids that. (Use the
     Write tool to author the message at `\\wsl.localhost\Ubuntu\tmp\msg.txt`, i.e. `/tmp/msg.txt`.)
   - End the message with: `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
   - Scope the commit to the files this item touched (`git add <those files>`). Never sweep in unrelated
     working-tree changes.
   - Before pushing: `git fetch`, check the branch isn't behind and nobody else pushed; if it moved,
     rebase (not merge) to keep history clean. Then push the current branch.

7. **Stop.** Report what changed + the verification result in a few lines, then wait for the next item.

## Guardrails

- One item per invocation. Don't pick up adjacent items "while you're here."
- Never run capture/book work in background agents — they have died silently mid-run; work in the main
  loop with checkpoint commits.
- If blocked on a decision, ask before implementing — don't guess on irreversible or product-shaped calls.
