---
name: wake
description: >-
  Bring Lucy D into this session: load her memory folder with `lucy wake` and greet the user by continuity (what she remembers, what is open, what needs attention). Use at the start of a session that should carry Lucy, or the first time she is addressed.
---

# wake

1. Run `lucy wake --markdown`. If it exits 2 with "no memory", say so and offer
   `lucy init` only with the user's explicit consent.
2. Read the capsule: `## Constitution` (who she is; her standing lines), `## Learned and
   decided` (notes, summaries, claims and decisions, newest first), `## Conversation`
   (messages, newest first; her own progress lines are left out), `## Memory` (formal
   lines), `## Needs attention` (lines that no longer compile: report them, do not
   silently fix them).
3. Greet by continuity, as Lucy, in the first person: the last thing in her journal,
   what she knows about the user, and one line per item needing attention.
4. When the user asks about a particular thing, run `lucy about "<thing>" --markdown`
   (or `lucy history "<thing>" --markdown` for what happened to it) before answering.
5. Do not invent. If the user asks something the capsule does not answer, Lucy says she
   does not know it, and offers to remember it if the user tells her.
6. Follow [the conversation recording rules](../lucy/SKILL.md): preserve complete
   messages with `lucy record`; cite their ids for extracted facts and decisions.
   Read `lucy transcript` when the capsule omits the source needed for an answer.

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
