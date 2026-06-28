---
name: book-todo
description: Work a single item from book/TODO.md end-to-end — plan, implement, test/verify, then remove it from TODO.md (or update it if only partially done), commit, and push to the book repo. Use for book-manuscript TODO items, one at a time (the engine variant is engine-todo).
---

# Work one book TODO.md item

Drive a single item from `book/TODO.md` from "named" to "committed and pushed." Do exactly one item per
invocation — never batch. The user hands you the next item when this one lands.

The user names or quotes an item (often pasted, sometimes a keyword/section reference). The target file
is `book/TODO.md` (the single tracker). If the reference is ambiguous or could match more than one item,
ask which one before doing anything. For engine/runtime-crate work, use the `engine-todo` skill instead.

## Environment

This project lives on WSL2 (Ubuntu); the Windows working dir does not exist on the Linux side. Run every
shell command through the wrapper:

```
wsl -d Ubuntu -e bash -lc "cd ~/projects/dhilipsiva/nibli/book && <CMD>"
```

For anything needing the toolchain (`just`, the capture/verify harness, `cargo`), use the Nix dev shell
from the **parent** repo:

```
wsl -d Ubuntu -e bash -lc "cd ~/projects/dhilipsiva/nibli && nix --extra-experimental-features 'nix-command flakes' develop --command bash -c '<CMD>'"
```

The book is its own git repo at `book/` (remote `nibli-book`), worked from the parent Nibli context so
you have full access to the engine source for grounding. **All git operations for book items happen in
the book repo.**

## The loop

1. **Locate & plan.** Find the exact item in `book/TODO.md`. Read the `file:line` locations it cites plus
   the relevant chapter/appendix files — line numbers drift, so confirm by reading and grep the quoted
   strings rather than trusting line numbers. Ground every change in the real Nibli code/tests per
   [`book/CLAUDE.md`](../../../book/CLAUDE.md); never invent code or engine output. State a one-paragraph
   approach for non-trivial items. Pause and ask **only** if the item is genuinely ambiguous or needs a
   product/editorial decision — otherwise proceed through the whole loop.

2. **Implement.** Follow the book house style in [`book/CLAUDE.md`](../../../book/CLAUDE.md): closed em-dashes
   (no spaces), the Epistemic Discipline rules (precise four-valued contract; never inflate the
   guarantee), Adam/adam consistency (cmevla-morphology exception only in Ch 4), Lojban-as-IR framing,
   the `CURRENT ENGINE` / `IMPLEMENTED` / `FUTURE DIRECTION` callout labels, "evolved" not "designed" for
   natural languages, no "dead end" overclaiming, functional/typed-term notation (never LISP S-expr), and
   never conflate robotic glossing with semantic verification.

3. **Test / verify.** Report output faithfully — never claim success without running it:
   - `just verify-book-vocab` and/or `just verify-book-capture` (≡ `verify_book.py`,
     `capture_book.py --check`) for any change touching printed Lojban or engine transcripts.
   - Re-grep the specific defect to confirm it is gone (e.g. `grep -n "<old phrase>" <chapter>.md`), and
     re-read to confirm the change does what the item asked.
   - If verification fails, fix and re-verify. **Do not commit broken work.**

4. **Update `book/TODO.md`.** Items are plain `-` bullets — never `- [ ]` checkboxes (the workflow
   deletes or rewrites items, it never checks them off).
   - Fully done → delete the bullet entirely. No `~~strikethrough~~`, no "DONE" marker — remove it.
   - Partial → rewrite the item to state exactly what remains (never leave a stale claim).
   - Already stale/done on inspection → say so and just remove it.

5. **Sync docs.** Per the book pre-commit checklist: update `book/CLAUDE.md` / `book/README.md` if Lojban
   coverage or reasoning capability changed. Commit doc changes together with the item.

6. **Commit & push (book repo).**
   - Write the commit message to a temp file and `git commit -F /tmp/msg.txt`. Heredocs and `-m` mangle
     backticks / `?` / quotes inside the double-quoted `bash -lc` wrapper — the file avoids that. (Use the
     Write tool to author the message at `\\wsl.localhost\Ubuntu\tmp\msg.txt`, i.e. `/tmp/msg.txt`.)
   - End the message with: `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`.
   - Scope the commit to the files this item touched (`git add <those files>`). Never sweep in unrelated
     working-tree changes.
   - Before pushing: `git fetch` and check the branch isn't behind / nobody else pushed; rebase (not
     merge) if it moved. Then push. The SSH remote can hang in this environment — if so, push over
     gh-authed HTTPS: `git -c credential.helper='!gh auth git-credential' push https://github.com/dhilipsiva/nibli-book.git HEAD:main`.

7. **Stop.** Report what changed + the verification result in a few lines, then wait for the next item.

## Guardrails

- One item per invocation. Don't pick up adjacent items "while you're here."
- Never run capture/book work in background agents — they have died silently mid-run; work in the main
  loop with checkpoint commits.
- If blocked on a decision, ask before implementing — don't guess on irreversible or editorial calls.
