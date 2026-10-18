# Lucy on demand

This optional Linux runtime extends Nibli's Lucy CLI. The Rust binary delegates
its desktop commands to `LUCY_DESKTOP_EXECUTABLE` (or `lucy-desktop` on PATH).
NixOS supplies GTK4, command dependencies, the private user service and the public
Nibli identity. Existing `record`, `wake`, `ask`, `claim` and other public-peer
commands retain their original behavior; they are explicit publication workflows,
not the desktop archive.

`lucy ui` opens the named Ask Lucy window without inference. Sending there or in
`lucy chat` invokes Lucy. App hooks accept `Lucy,` (or another address punctuation), a greeting such
as `Hey Lucy`, `@lucy`, or `/lucy`. Bare subject mentions such as “Lucy said”
do not wake her. Activation is per source and conversation; ordinary prompts, quotations
and incidental mentions in inactive conversations do nothing. `Lucy, sleep`,
close and service shutdown end activation; Stop cancels the current task and
clears pending approvals. A subsequent message in the same open conversation can
continue. App startup/resume resets activation. No startup hook loads memory.

The service listens only on `$XDG_RUNTIME_DIR/lucy/service.sock`, mode 0600, and
checks peer UID. Active sessions and approval tokens live only in RAM. Its trust
boundary is the user's local OS account, not hostile programs already running as
that user. Adapters and user interfaces are trusted ingress; model tools cannot
activate a conversation or approve a proposal. MCP exposes only recall for a fixed
source/session supplied when the transport starts. Existing apps keep their own
permission systems and selected models.

The archive is `~/.local/share/lucy/conversations.sqlite3`, directory mode 0700,
file mode 0600. Complete visible messages, IDs, sources, channels and capture times
are retained; hidden reasoning and tool internals are not conversation records.
Imports may retain original timestamps. Use `lucy archive reindex` to rebuild FTS5 from the canonical message table.
`lucy archive import < messages.json` explicitly imports an array with string
`id`, `source`, `session`, `role` (user/assistant), `text`, and optional original
`timestamp`/`channel` metadata. These commands require explicit invocation and
never start inference. Recall is bounded and does not compile the historical
archive. Private memory is supplied to a cloud app only after invocation, as the
user selected. Nothing publishes private records into a public peer automatically.
Memory roots inside repositories, Nix sources, store paths or symlinks are refused.

Local requests use only 127.0.0.1:11434 and Qwen3.6 35B-A3B Q4_K_M, 16K context,
with keep_alive=0. The registry manifest SHA256 is
`07d35212591fc27746f0a317c975a6d68754fb38e9053d82e25f06057af28522`.
`lucy setup-model` is the explicit download step; inference refuses a missing or
changed model. No cloud fallback or automatic model pull exists. A second local
request reports busy. Stop closes the model connection and requests unload.
Physical fit, latency and VRAM release still need a real GPU acceptance test.

Workspace reading/search and diagnostics are available after invocation. Writes
show a diff and refuse a file changed since preview. Commands require approval and
run in a bubblewrap workspace sandbox without network or host credentials. GUI,
screenshots, app launches and privileged diagnostics require explicit approval;
privileged helpers additionally require polkit authentication. GUI actions check
an active unlocked Wayland login and stop on lock/cancel. This is polling, not a
hard real-time guarantee. Absolute mouse coordinates are physical pixels: use the
returned monitor data and validate scaling before unattended use. Screenshot files
stay in the private runtime directory and disappear at logout.

`lucy integrations install` adds hooks to existing JSON settings with backups,
refuses conflicts or invalid JSON, and does not touch model/provider settings.
It installs the explicit Cursor and Zed skills, VS Code extension and Firefox
native host registration. The shipped public extension key gives Chrome a stable ID, registered by the
installer. `--browser-id ID` supports a separately built extension. The browser extension requests only activeTab,
scripting and nativeMessaging; pages are read only when the user clicks an action.
Firefox persistent extension installation requires signing. Codex hook trust and
model access in VS Code must be accepted in their own applications.

Recording capabilities are deliberately narrower than complete app transcripts:
Claude/Codex hooks expose submitted prompts and final Stop messages; commentary
needs explicit `lucy memory record`. Cursor exposes afterAgentResponse text but its
submission hook cannot inject context, so use the explicit skill and recall tool.
Claude supplies no stable prompt event ID: repeated hook deliveries cannot be
distinguished from repeated intentional prompts. Other supplied native event IDs
are idempotent; changed content with the same ID is rejected. No historical
transcript is scraped. VS Code saves its participant's completed text. Zed and web
AI chats require explicit record/import; Zed has no reliable close callback, so
sleep explicitly. No automatic background scraping is implemented for utilities.

Sources: [Claude hooks](https://code.claude.com/docs/en/hooks),
[Codex hooks](https://learn.chatgpt.com/docs/hooks),
[Cursor hooks](https://cursor.com/docs/hooks),
[VS Code participants](https://code.visualstudio.com/api/extension-guides/ai/chat),
[Zed skills](https://zed.dev/docs/ai/skills),
[Chrome activeTab](https://developer.chrome.com/docs/extensions/develop/concepts/activeTab),
[model](https://ollama.com/library/qwen3.6:35b-a3b-q4_K_M),
[Ollama local-only mode](https://docs.ollama.com/faq).

Run `just test-lucy`, `just clippy-lucy`, `just verify-lucy-plugin` and the Lucy
constitution checks in Nibli's Nix shell. The desktop tests use a fake model;
build/test success does not establish app trust or physical acceptance.
