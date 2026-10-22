---
name: remember
description: Record Lucy's complete conversations and separately attributed facts and decisions in nibli. Use when something is said, decided or learned in a Lucy session.
---

# remember

- Complete messages: `lucy record --speaker NAME --source HOST --stdin`, or
  `lucy record --json` with an object/batch containing `id`, `speaker`, `text`,
  `source`, `session`, `channel`, `about` and `private`. Metadata is optional except
  speaker and text; an explicit id makes retries idempotent. Pass JSON/text through
  stdin safely, preserving exact whitespace and newlines. Do not substitute a summary.
- Attributed facts: `lucy claim "<KR>" --from MESSAGE_ID --text "<interpretation>"`.
  Add `--decision` for a decision. The source must exist; its speaker and privacy are
  inherited. Claims are opaque `fact { ... }` content, not bare assertions.
- Notes: `lucy remember "<note>"`, with `--source WHO`, `--private`, and `--about THING`
  when relevant. Notes are KB records too; they supplement complete messages.
- Formal: `lucy remember "<nibli KR statement>" --kr`. It is compiled against her
  constitution first and refused if it does not compile or asserts a derived-only head
  (`person(X).` is refused; use `human(X).`). One statement per call.
- Conclusions Lucy derived: ask first (`lucy ask "<KR>"`), then record the verdict in
  prose with its `[Why]` line, never as a bare fact.
- Honor the user's retention instructions and privacy choices. Keep private
  conversations in the private archive; never copy excluded material into a summary.
- `lucy transcript --id ID` returns the exact source. Capsule truncation is a display
  limit, not deletion. Older journal entries remain labelled `legacy-journal`.

## Shared private continuity

Use `lucy store search --query TEXT` to retrieve across registered local peers and
app sessions. Capture every visible exchange and progress update promptly, with
original attribution and timestamps; add reviewed decisions, evidence, uncertainty
and open work separately. In activated apps use `lucy memory record --source APP
--session ID --event UNIQUE_ID --channel commentary --stdin` (or `final`/`summary`).
Keep private app records in the shared store outside repositories. Preserve public
Nibli records with the native commands above; their writes also update redb.
Do not save hidden reasoning, privileged instructions, tool internals or secrets.
Backup/restore uses the private repository and portable snapshots described in
`lucy.md`; never copy private data to a public peer or a live redb file to Git.
