---
name: remember
description: Write a memory for Lucy D: a prose entry in her journal or a checked nibli statement in memory.nibli. Use during a session when something worth keeping was said, decided, or learned.
---

# remember

- Prose: `lucy remember "<one to three sentences>"`, with `--source WHO` when someone
  reported it, `--private` when it belongs in the private twin, and `--about THING`
  (repeatable) so `lucy about THING` finds it later.
- Formal: `lucy remember "<nibli KR statement>" --kr`. It is compiled against her
  constitution first and refused if it does not compile or asserts a derived-only head
  (`person(X).` is refused; use `human(X).`). One statement per call.
- Conclusions Lucy derived: ask first (`lucy ask "<KR>"`), then record the verdict in
  prose with its `[Why]` line, never as a bare fact.
- Never record: trauma or distress narratives about anyone; secrets (keys, tokens,
  passphrases, contents of `.env`); verbatim private messages; anything the user said
  not to keep. When unsure, ask, or leave it out.
- Say what was recorded and where (journal or memory, public or private).
