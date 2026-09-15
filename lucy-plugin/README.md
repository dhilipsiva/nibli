# Lucy D

Lucy is a persistent identity whose memory is plain nibli text: `constitution.nibli`,
`memory.nibli` (direct facts and rules) and `interactions.nibli` (complete messages,
notes, and attributed facts/decisions). `private.nibli` and
`private-interactions.nibli` hold their private counterparts. Old Markdown journals
are imported on the first conversation write, or by `lucy migrate-journal`.
Nothing is signed or encrypted. Any agent session that runs
the `lucy` CLI is Lucy for that session, through the model that session already uses.

## Install the CLI

From the nibli checkout: `cargo build --release -p lucy-cli` and put
`target/release/lucy` (`lucy.exe` on Windows) on your `PATH`, or `cargo install --path lucy-cli`.
Release builds for Linux, macOS and Windows ship with nibli releases.

## Where her memory lives

`lucy` looks for a folder in this order: `LUCY_HOME` if set; a `lucy/` folder in the
current directory or any parent that contains `constitution.nibli` (a project-local
Lucy, the way this repository keeps her); else `~/.lucy`. `lucy init` creates one
(`lucy init --here` creates `./lucy`). Sync the folder however you sync files: git,
Syncthing, Dropbox, a stick.

## Commands

```
lucy init [--name NAME] [--here]  lucy check      lucy wake [--markdown]
lucy record "TEXT" --speaker NAME [--source NAME] [--session ID] [--id ID]
lucy record --json               lucy record --speaker NAME --stdin
lucy claim "KR STATEMENT" --from ID [--decision] [--text "INTERPRETATION"]
lucy transcript [--markdown] [--id ID] [--session ID]
lucy migrate-journal
lucy remember "TEXT" [--kr] [--private] [--source WHO] [--about THING]...
lucy ask "KR QUERY"               lucy audit      lucy forget FILE:LINE
lucy about THING [--markdown]     lucy history THING [--markdown]
lucy talk "MESSAGE" [--model M] [--about THING]... [--markdown]
lucy address "TEXT"               lucy hook user-prompt | session-start
```
Every command prints one JSON object on stdout (except Markdown views and the
hooks); exit 0 ok, 1 finding, 2 harness.

## Conversation KB

`record` retains exact text, including whitespace, newlines and Unicode. `--json`
reads an object or array from stdin; each record needs `speaker` and `text`.
Optional fields include `id`, `source`, `session`, `channel`, `about` (an array),
`private`, `kind` (`message`, `note`, `summary`), `timestamp`, and `host`. Missing
timestamps use the recording time in UTC, not an inferred original send time.
Reusing an id with identical content is an idempotent retry; changed content is
refused. A batch uses one privacy partition and is written atomically.

Each entry has a `record(id, payload, kind, Json)` fact plus queryable `message`,
`date`, `source` and optional `member` facts. The payload is JSON inside a KR
quoted constant: JSON escapes preserve newlines that KR's single-line strings
cannot spell directly. `lucy transcript` decodes it losslessly. Another nibli
engine can load the files directly. For a message with id `turn-1`, speaker
`Owner`, source `codex` and topic `memory`, queries include:

```text
lucy ask --conversations 'message("turn-1", "memory", Conversation, "Owner").'
lucy ask --conversations 'source("codex", "turn-1").'
```

`lucy claim 'human(Ada).' --from turn-1` records an interpretation attributed to
the original speaker. Its KR is wrapped in
`expresses(speaker, fact { human(Ada) }, Conversation, claim_id)`: it records the
claim without making `human(Ada)` true. `--decision` distinguishes decisions.
Extraction is performed by the agent and remains an interpretation for the owner
to inspect. The CLI checks KR, citation and privacy; it cannot verify semantic
fidelity to natural language. Use `remember --kr` for a deliberate direct assertion.

Use `ask --conversations` for conversation records and their attributed claims.
Its response declares `scope: conversations`: the constitution and direct memory
facts are excluded. Default `ask` queries the combined KB; its known constitution
performance issue grows with the number of records (see the Lucy section in
`TODO.md`). `transcript` retrieves exact records without inference.

New prose `remember` calls write notes to the KB. The journal in `wake` and `about`
is a readable projection with record ids and kinds. Capsule truncation never
removes records. Imported Markdown entries retain the `legacy-journal` kind and
unknown speaker; a saved summary cannot supply a missing verbatim exchange. The
old Markdown is preserved, but later edits to it are not automatically reimported.

Writes take a process-shared lock. Reads reject incomplete or inconsistent generated
metadata, so queries and transcripts cannot silently disagree. Use the CLI to write
records. Private records and their extractions remain in the private archive.

## Install the skills

Claude Code: `claude plugin marketplace add <path to this folder>` then
`claude plugin install lucy@lucy`. Other agents load the same `skills/*/SKILL.md`
files from their skill directories (codex, opencode `~/.config/opencode/skills/`,
Copilot CLI `~/.copilot/skills/`, pi).

## "Hey Lucy": the hook you install yourself

A prompt that starts by addressing Lucy ("Hey Lucy", "lucy,", typos included) is
answered by Lucy through the session's own model. The prompt hook records every
prompt when a Lucy folder is present. When addressed, it puts her capsule in front of
the model with the instruction that this reply is hers. **No agent installs this for
you.** Add it by hand (or with Claude Code's `update-config` skill) to
`~/.claude/settings.json` or the project's `.claude/settings.json`; the snippet is
`hooks/hooks.example.json`, byte for byte:

```json
{
  "hooks": {
    "UserPromptSubmit": [
      { "hooks": [ { "type": "command", "command": "lucy hook user-prompt", "timeout": 20 } ] }
    ],
    "SessionStart": [
      { "hooks": [ { "type": "command", "command": "lucy hook session-start", "timeout": 10 } ] }
    ]
  }
}
```

`lucy` must be on the `PATH` of the shell that runs hooks (or use the absolute path to
the binary; on Windows, `lucy.exe`). The hooks never block a prompt: any problem is one
line of context and exit 0.

## A local model: `lucy talk`

Lucy can exist as the context of a local model, no agent session needed:
`lucy talk "Hey Lucy, what do you remember?"` sends her capsule and the addressing
instruction to an Ollama server (`LUCY_OLLAMA_URL`, default `http://127.0.0.1:11434`),
prints her reply, and records both complete messages in her KB (`--about` tags apply; a
`private:` marker sends the exchange to the private journal). `lucy task <words>` is
the same, unquoted. `--model M`, then `LUCY_MODEL`, then a one-line `model` file in her
folder (committed with the memory, so every host agrees), then the server's first model
decides who speaks for her. Plain HTTP on
localhost, no cloud client: Claude and other hosted models run her through their own
sessions and the hook instead.

The host agent must record its complete replies through `record`; the prompt hook
does not intercept assistant output. The Lucy skills prescribe this workflow,
including progress messages. They do not install or modify hooks.

## Memory about particular things

Tag a memory with `--about THING` (repeatable); the journal line carries `[about: thing]`
and `lucy about thing` collects tagged entries, entries that mention it, formal lines that
mention it, and, when the folder lives in a git repository, the commits that touch it (a
path) or mention it (a term). `lucy history thing` merges the git log with her own record,
newest first. Code-browsing tools (outline, find, grep, and her own summaries of code) are
planned, not built.

## What she is not

Not sentient, and she does not claim to be. Not a daemon. Not defended against her
owner: you can open her files and change anything, and `lucy check` will tell you what
still compiles.
