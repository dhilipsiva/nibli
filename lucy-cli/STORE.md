# Shared Lucy memory

The native `lucy store` commands own a Rust `redb` database. CLI writes,
the desktop runtime, and its Claude/Codex/Cursor/VS Code adapters use the same
private root: `$LUCY_DATA_DIR`, or `$XDG_DATA_HOME/lucy`, or
`~/.local/share/lucy`. The service and CLI call the same Rust store directly.
No separate database service is required.

Original app messages are immutable JSON files in `records/`, written and
fsynced before the index transaction. Existing desktop SQLite payloads migrate
on the first activated access; the old database remains intact. Native Nibli
archives remain authoritative for native conversations. A failed index write
reports that the original was saved and gives the recovery command.

```sh
lucy store register --name nibli --path /path/to/nibli/lucy
lucy store register --name nixos --path /path/to/NixOS/lucy
lucy store register --name book --path /path/to/rights-nobody-has-to-earn/lucy
lucy store sync
lucy store search --query 'what did we decide about memory'
lucy store transcript --source codex --session SESSION_ID
lucy store status
```

All store commands accept `--root DIR`. Queries can instead arrive privately on
stdin: `printf '%s' '{"query":"topic"}' | lucy store search --stdin`.
`store record --stdin` accepts `{ "origin": "stable source", "payload": { ... } }`
or an array. Payloads require nonempty `id` and `text`; retain source, session,
role, channel, timestamp, privacy and provenance metadata. Reusing the same
origin/ID with changed content is rejected. `store import-nibli --name NAME
--path /path/to/private-interactions.nibli` imports a legacy archive losslessly.

Peer registration reads only the selected Lucy directory, not a whole repository.
Its Nibli conversations, memory, constitution and Markdown context are searchable
as attributed records. It does not assert retrieved text into the reasoning
engine. Changes and deletions replace that source's index transactionally. Missing
peers are reported and their last indexed records remain available. Names must
stay the same across hosts; paths are local and are not restored from a backup.

Search combines lexical relevance with exact cosine vector ranking in Rust.
redb is the durable key/value store; it is not an approximate-neighbor engine.
Original text is never truncated in storage. Long messages are embedded in
bounded chunks and their vectors averaged; returned context excerpts are bounded.
This favors a small local dependency footprint over an approximate index for
millions of records.

```sh
ollama pull embeddinggemma
lucy store embed --model embeddinggemma
```

Embedding uses only `http://127.0.0.1:11434` (override with `--url` for another
loopback port). The model's digest identifies the vector space. A changed model
cannot mix with previous vectors; indexing validates dimensions and finite,
nonzero vectors. After initial setup, desktop writes queue incremental embedding
in the background. Native file edits become searchable lexically immediately
and get vectors on the next indexing pass. `status` reports pending vectors.
Unavailable embedding models leave visible lexical fallback and durable originals.
No cloud inference, model download, or private publication happens implicitly.

## Private Git backup and recovery

Use a separate clone of the user's private repository, outside all public/Nix
source trees. Existing legacy files in that repository can remain untouched.

```sh
git clone git@github.com:dhilipsiva/lucy-private.git ~/.local/share/lucy-private-backup
git -C ~/.local/share/lucy-private-backup pull --ff-only
lucy store backup --to ~/.local/share/lucy-private-backup/shared-store
git -C ~/.local/share/lucy-private-backup add -- shared-store
git -C ~/.local/share/lucy-private-backup commit -m 'Back up Lucy shared memory'
git -C ~/.local/share/lucy-private-backup push
```

Each snapshot lists SHA-256 addressed complete records in `objects/`.
Manifests live in `snapshots/HOST/TIMESTAMP.json`, so hosts add separate files.
Pull before pushing; concurrent hosts may need a normal Git rebase before retrying
a rejected push. The CLI does not force-push, merge live databases, publish to a
remote, or configure a periodic backup. Keep the Git repository private: these
portable files contain the original conversation text, not encrypted ciphertext.
Only stage this generated subtree, never a live `memory.redb` or credentials.

On another host, clone or pull that private repository, then:

```sh
lucy store restore --from ~/.local/share/lucy-private-backup/shared-store/snapshots/HOST/TIMESTAMP.json
lucy store register --name nibli --path /this/host/nibli/lucy
lucy store register --name nixos --path /this/host/NixOS/lucy
lucy store register --name book --path /this/host/rights-nobody-has-to-earn/lucy
lucy store embed --model embeddinggemma
```

Restore validates every object hash before writing. It is idempotent and rejects
conflicting immutable IDs. Existing local registered peer files take precedence
over their snapshot copies. Restore additional host snapshots to merge their
conversation records; current local peer files remain authoritative. There is no
automatic background cross-host synchronization.

The snapshot excludes model weights, rebuildable vectors, machine-local peer
paths and active-session/approval state. It includes the complete indexed payloads,
with source attribution, channel and timestamps. The local source files remain
the repair path: `lucy store sync` reconstructs the index from originals and peers.
Do not delete source records or backups as part of index maintenance.

Run `just test-lucy`, `just clippy-lucy` and `just verify-lucy-plugin` inside the
Nix release shell; use the `.#lucy` shell for `just test-lucy-desktop`. Tests cover exact recovery,
conflicts, corruption, peer edits/deletions, independent writers, vector validation
and app activation/approval boundaries.
