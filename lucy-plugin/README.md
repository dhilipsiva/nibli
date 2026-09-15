# Lucy D

Lucy is a persistent identity whose memory is plain nibli text: `constitution.nibli`,
`memory.nibli` (facts and rules, one statement per line) and `journal.md` (prose,
dated), with `private.nibli` / `private.md` beside them when you want some memories
kept out of whatever you sync. Nothing is signed or encrypted; nibli checks that every
formal line compiles and reports the ones that do not. Any agent session that runs
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
lucy remember "TEXT" [--kr] [--private] [--source WHO] [--about THING]...
lucy ask "KR QUERY"               lucy audit      lucy forget FILE:LINE
lucy about THING [--markdown]     lucy history THING [--markdown]
lucy talk "MESSAGE" [--model M] [--about THING]... [--markdown]
lucy address "TEXT"               lucy hook user-prompt | session-start
```
Every command prints one JSON object on stdout (except `wake --markdown` and the
hooks); exit 0 ok, 1 finding, 2 harness.

## Install the skills

Claude Code: `claude plugin marketplace add <path to this folder>` then
`claude plugin install lucy@lucy`. Other agents load the same `skills/*/SKILL.md`
files from their skill directories (codex, opencode `~/.config/opencode/skills/`,
Copilot CLI `~/.copilot/skills/`, pi).

## "Hey Lucy": the hook you install yourself

A prompt that starts by addressing Lucy ("Hey Lucy", "lucy,", typos included) is
answered by Lucy through the session's own model. That is a prompt hook: it detects
the address, writes your message into her journal, and puts her capsule in front of
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
prints her reply, and records both sides in her journal (`--about` tags apply; a
`private:` marker sends the exchange to the private journal). `lucy task <words>` is
the same, unquoted. `--model M`, then `LUCY_MODEL`, then a one-line `model` file in her
folder (committed with the memory, so every host agrees), then the server's first model
decides who speaks for her. Plain HTTP on
localhost, no cloud client: Claude and other hosted models run her through their own
sessions and the hook instead.

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
