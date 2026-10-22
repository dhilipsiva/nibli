# Lucy on demand

The service, agent engine, GTK window, HTTP client, memory store and protocol
adapters are Rust modules in `lucy-cli/src/desktop/`. Build the window with
`nix develop .#lucy --command just build-lucy-desktop`; the default CLI build
also includes the service and terminal agent, without GTK. No Lucy application
Python runtime is required. Browser and VS Code extension entry points remain
JavaScript because those hosts require it.
NixOS supplies GTK4, command dependencies, the private user service and the public
Nibli identity. Existing `record`, `wake`, `ask`, `claim` and other public-peer
commands retain their source files and also refresh the shared local Rust index.
See [shared memory and backups](../STORE.md) for registration and recovery.

`lucy ui` opens the named Ask Lucy window without inference. Sending there or in
`lucy chat` invokes Lucy. `lucy agent 'inspect this project' --workspace DIR`
runs a task through the same service and tools; `lucy agent` starts an interactive
terminal conversation. Start `lucy serve` if the user service is unavailable.
Ctrl+C cancels the terminal's service session and its running actions.
App hooks accept `Lucy,` (or another address punctuation), a greeting such
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

The shared store is `~/.local/share/lucy/memory.redb`, with complete immutable
original records in `records/`. The Rust CLI owns both writes and retrieval;
`LUCY_DATA_DIR` overrides the root for every client. The first activated access
imports the existing `conversations.sqlite3` payloads exactly and retains that
old database. Complete visible text, IDs, sources, channels and source/capture
timestamps are preserved. Hidden reasoning, privileged instructions and tool
internals are excluded. Private records never enter public source repositories.

`lucy archive reindex` repairs the shared index from originals and registered local
peers. `lucy archive import < messages.json` imports complete attributed messages.
App access still requires an activated session; controlled import and action
approval gates remain in force. The same user's direct `lucy store` commands can
inspect, record, search, back up and restore private memory. Private excerpts reach
a cloud app only when the user invokes that app's Lucy integration.

After `lucy store embed --model embeddinggemma`, desktop writes queue incremental
local embeddings without delaying durable recording. Peer and native CLI changes
are searchable lexically immediately and receive vectors on an indexing pass.
If Ollama is unavailable, records remain saved and recall reports lexical fallback.
Private backups contain portable records and per-host manifests, not a live redb
file; see [STORE.md](../STORE.md). Source paths and activation tokens are local.

The default local provider uses 127.0.0.1:11434 and Qwen3.6 35B-A3B Q4_K_M, 16K context,
with keep_alive=0. The registry manifest SHA256 is
`07d35212591fc27746f0a317c975a6d68754fb38e9053d82e25f06057af28522`.
`lucy setup-model` is the explicit download step; inference refuses a missing or
changed model. No cloud fallback or automatic model pull exists. A second local
request reports busy. Stop closes the model connection and requests unload.
Physical fit, latency and VRAM release still need a real GPU acceptance test.

Workspace listing, reading/search, Git status/diff/log and diagnostics are available
after invocation in both UI and terminal. HTTP requests show the method, URL and
JSON body for approval, limit response size and support cancellation. Service tools
show status or propose start/stop/restart; system services retain host authorization.
Writes
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
submission hook cannot inject context. Its explicit skill runs a harmless status
command; the documented postToolUse hook then supplies bounded context and the
native conversation ID, only for the already activated conversation.
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

## Local and hosted models

The desktop's **Model and provider settings** and `lucy providers` share the same
configuration. Ollama is the default. Explicitly choosing a hosted provider sends
prompts, retrieved context and tool results to that provider. Choose a model that
supports function calling from its catalog; vision additionally requires a vision
model. Availability, free eligibility and quotas depend on the model and account.

| Provider | Key variable | Verified offer documentation |
| --- | --- | --- |
| NVIDIA | `NVIDIA_API_KEY` | [Development access](https://build.nvidia.com/) |
| Groq | `GROQ_API_KEY` | [Free-plan limits](https://console.groq.com/docs/rate-limits) |
| Gemini | `GEMINI_API_KEY` | [Eligible free tier and data-use terms](https://ai.google.dev/gemini-api/docs/billing/) |
| OpenRouter | `OPENROUTER_API_KEY` | [Free models and limits](https://openrouter.ai/pricing/) |

Offers were checked on 2026-10-20. Catalogs are fetched on demand, rather than
assuming a model list is permanent. OpenRouter's `openrouter/free` selects from
free models. Lucy never silently falls back to another provider or paid model.
HTTP errors include status and Retry-After, without provider error bodies or keys.

```sh
# In Bash, read a key without echoing it or putting it in command history.
read -rs -p 'NVIDIA API key: ' lucy_provider_key
printf '%s' "$lucy_provider_key" | lucy providers key --name nvidia --stdin
unset lucy_provider_key
lucy providers models --name nvidia
lucy providers configure --name nvidia --model MODEL_ID_FROM_CATALOG
lucy providers use --name nvidia
lucy agent 'List this project and explain its structure'
lucy providers use --name ollama
```

Keys are separate mode-0600 files under `$XDG_CONFIG_HOME/lucy/keys` (normally
`~/.config/lucy/keys`). They never enter memory, backups or Nix sources. Environment
variables are also supported; a systemd service must actually inherit them.
Local key files work for terminal and desktop without changing service environment.
Configuration is in `~/.config/lucy/providers.json`. There is no automatic
provider selection, paid fallback or key discovery outside these explicit locations.

Run `just test-lucy`, `just clippy-lucy`, `just verify-lucy-plugin` and the Lucy
constitution checks in Nibli's release shell. Use `nix develop .#lucy` for
`just test-lucy-desktop clippy-lucy-desktop build-lucy-desktop`. Desktop tests use
scripted model replies and real local HTTP fixtures; hosted inference still needs
an account key and a compatible model. Build/test success does not establish app
trust or physical acceptance.
