set shell := ["bash", "-c"]

wasi_target := "wasm32-wasip2"
# Build profile: "debug" (default) or "release" (use `just profile=release run`)
profile := "debug"
wasm_dir := "target/" + wasi_target + "/" + profile
cargo_profile_flag := if profile == "release" { "--release" } else { "" }

export RUST_BACKTRACE := "full"

# The default target executes the full build-and-run pipeline
default: run

# Remove stale WASM artifacts for the active profile
clean-wasm:
    @echo "Removing stale WASM artifacts ({{profile}})..."
    rm -f {{wasm_dir}}/*.wasm

# Remove stale WASM artifacts for both debug and release
clean-wasm-all:
    @echo "Removing all WASM artifacts..."
    rm -f target/wasm32-wasip2/debug/*.wasm
    rm -f target/wasm32-wasip2/release/*.wasm

# Compiles the single lasna WASM component (gerna/smuni/logji linked as internal crates)
build-wasm: clean-wasm
    @echo "Building WASI lasna component ({{wasi_target}}, {{profile}})..."
    cargo component build --target {{wasi_target}} {{cargo_profile_flag}} -p lasna
    # cargo-component regenerates lasna/src/bindings.rs in wit-bindgen's own
    # formatting; normalize it so a later `fmt-check` (ci) doesn't trip on the
    # auto-generated file.
    cargo fmt -p lasna

# Compiles the native Wasmtime host gasnu
build-gasnu:
    @echo "Building native host gasnu..."
    cargo build -p gasnu {{cargo_profile_flag}}

# Smoke-test gasnu non-interactive script mode: pipe a 3-line script (assert,
# query, :facts) into the built binary and assert the echoed prompts + markers.
# Exercises the byte-faithful REPL transcript capture path used for the book.
smoke-gasnu-script: build-wasm build-gasnu
    @echo "Smoke-testing gasnu script mode (piped stdin)..."
    @out=$(printf 'la .adam. cu gerku\n? la .adam. cu gerku\n:facts\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF 'nibli> la .adam. cu gerku' || { echo 'FAIL: missing echoed assert prompt'; exit 1; }; \
        echo "$out" | grep -qF 'nibli> ? la .adam. cu gerku' || { echo 'FAIL: missing echoed query prompt'; exit 1; }; \
        echo "$out" | grep -qF 'nibli> :facts' || { echo 'FAIL: missing echoed :facts prompt'; exit 1; }; \
        echo "$out" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: missing [Fact #0] Asserted.'; exit 1; }; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: missing [Query] TRUE'; exit 1; }; \
        echo "$out" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: missing :facts listing'; exit 1; }; \
        echo 'PASS: gasnu script mode emits echoed prompts + expected markers'

# Trap-recovery smoke: a fuel trap must not brick the session. The host
# rebuilds the poisoned component instance lazily (before the next session
# call, so an intervening :fuel raise applies) and replays the journaled
# mutations deterministically; the post-trap query answers from the replayed
# KB with the original fact ids. Pre-release gate like smoke-gasnu-script
# (needs the WASM build; not part of `ci`).
smoke-gasnu-trap-recovery: build-wasm build-gasnu
    @echo "Smoke-testing gasnu trap recovery (fuel trap mid-session)..."
    @out=$(printf 'la .adam. cu gerku\n:fuel 1000\n? la .adam. cu gerku\n:fuel 10000000000\n? la .adam. cu gerku\n:facts\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Limit] Execution fuel exhausted' || { echo 'FAIL: fuel trap not classified as [Limit]'; exit 1; }; \
        echo "$out" | grep -qF '[Session] Wasm trap poisoned the component instance; rebuilding and replaying 1 command(s)...' || { echo 'FAIL: missing rebuild message'; exit 1; }; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: post-recovery query did not answer TRUE'; exit 1; }; \
        echo "$out" | grep -qF '#0: la .adam. cu gerku' || { echo 'FAIL: replayed fact #0 missing from :facts'; exit 1; }; \
        if echo "$out" | grep -qF 'cannot enter component instance'; then echo 'FAIL: session still bricked after trap'; exit 1; fi; \
        if echo "$out" | grep -qF 'cannot remove owned resource'; then echo 'FAIL: resource-drop error at exit'; exit 1; fi; \
        echo 'PASS: fuel trap recovered — session rebuilt and replayed'

# go'i snapshot-trap smoke: assert once, then run `? go'i` TWICE. Before the
# graft-from-clone fix the second query grafted the drained snapshot, producing
# an out-of-bounds selbri index that trapped the component instance. Both
# queries must answer with no trap-rebuild and no brick. Pre-release gate like
# the other smokes (needs the WASM build; not part of `ci`).
smoke-gasnu-goi: build-wasm build-gasnu
    @echo "Smoke-testing go'i snapshot trap (repeated ? go'i)..."
    @out=$(printf 'la .adam. cu gerku\n? la .adam. go'\''i\n? la .adam. go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        n=$(echo "$out" | grep -cF '[Query] TRUE'); \
        [ "$n" -ge 2 ] || { echo "FAIL: expected both ? la .adam. goi queries TRUE, got $n"; exit 1; }; \
        if echo "$out" | grep -qF 'rebuilding and replaying'; then echo 'FAIL: repeated goi trapped the component'; exit 1; fi; \
        if echo "$out" | grep -qF 'cannot enter component instance'; then echo 'FAIL: session bricked after goi'; exit 1; fi; \
        echo 'PASS: repeated ? goi resolves correctly (TRUE) with no trap'

# Persistent restart-replay smoke: prove the live session's fact-ids stay equal
# to the durable store's across a reopen, INCLUDING a tombstone gap. Run-1
# asserts 3 facts and retracts the middle one; run-2 reopens the SAME db and must
# show the surviving STORE ids (with the gap) and retract the high one by its
# store id. On the pre-fix build, run-2 replays with FRESH ids, so the high store
# id is a zombie and the final query stays TRUE — this recipe FAILS. Pre-release
# gate (needs the WASM build; not part of `ci`).
smoke-gasnu-persist-replay: build-wasm build-gasnu
    @echo "Smoke-testing gasnu persistent restart-replay (fact-id drift)..."
    @dir=$(mktemp -d); db="$dir/nibli-smoke.redb"; \
        out1=$(printf 'la .adam. cu gerku\nla .bel. cu gerku\nla .kar. cu gerku\n:retract 1\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF '[Fact #2] Asserted.' || { echo 'FAIL run1: fact #2 not asserted'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Retract] Fact #1 retracted.' || { echo 'FAIL run1: retract 1'; rm -rf "$dir"; exit 1; }; \
        out2=$(printf ':facts\n:retract 2\n? la .kar. cu gerku\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out2"; \
        echo "$out2" | grep -qF '#2:' || { echo 'FAIL run2: surviving store id #2 missing after reopen (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        if echo "$out2" | grep -qF '#1:'; then echo 'FAIL run2: tombstoned/zombie id #1 present (DRIFT)'; rm -rf "$dir"; exit 1; fi; \
        echo "$out2" | grep -qF '[Retract] Fact #2 retracted.' || { echo 'FAIL run2: surviving store id #2 not retractable (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        echo "$out2" | grep -qF '[Query] FALSE' || { echo 'FAIL run2: retracted fact still entailed (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: persistent restart-replay keeps live==store fact-ids (gap preserved, high store id retractable)'

# NAF-note smoke: the closed-world / negation-as-failure flag is now a first-class
# WIT `proof-trace` field — computed once in the guest (ProofTrace::has_naf_dependency),
# carried across the boundary, and READ by gasnu (no longer recomputed host-side). A
# `na`-negated query over an absent fact (closed-world TRUE) must still print the NAF
# note; this guards the wiring end-to-end (a dropped field would silently remove the
# note). Pre-release gate (needs the WASM build; not part of `ci`).
smoke-gasnu-naf: build-wasm build-gasnu
    @echo "Smoke-testing gasnu NAF-dependent proof note (WIT proof-trace flag)..."
    @out=$(printf '? la .adam. na gerku\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: NAF query did not answer TRUE'; exit 1; }; \
        echo "$out" | grep -qF '[Note: result depends on negation-as-failure (closed-world assumption)]' || { echo 'FAIL: missing NAF note (naf-dependent flag not carried through the WIT proof-trace)'; exit 1; }; \
        echo 'PASS: NAF-dependent proof carries the closed-world note through the WIT proof-trace'

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine ({{profile}})..."
    NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm cargo run -p gasnu {{cargo_profile_flag}}

# Build the native Linux binary (no WASM, full backtraces)
build-native:
    @echo "Building native nibli binary..."
    cargo build -p nibli {{cargo_profile_flag}}

# Run the native REPL (no WASM sandbox — unlimited memory, full Rust backtraces)
run-native: build-native
    @echo "Launching Native Neuro-Symbolic Engine ({{profile}})..."
    cargo run -p nibli {{cargo_profile_flag}}

# Fast type-check all workspace crates (no codegen)
check:
    cargo check --workspace

# Check Rust formatting across the workspace
fmt-check:
    cargo fmt --all --check

# Strict clippy gate for the runtime crates under active hardening
clippy-runtime:
    cargo clippy --no-deps -p nibli-protocol -p nibli-store -p nibli-engine -p nibli -p tavla -p nibli-server --all-targets -- -D warnings

# Run gerna unit tests only (bypasses cdylib linker issues)
test-gerna:
    cargo test -p gerna --lib -- --nocapture

# Run all unit tests across workspace
test:
    cargo test --lib -- --nocapture --test-threads=1

# Run nibli-engine integration tests (full pipeline: parse → compile → reason)
test-engine:
    cargo test -p nibli-engine --test integration -- --nocapture --test-threads=1

# Run nibli-server GraphQL and gossip integration tests
test-server:
    cargo test -p nibli-server -- --nocapture

# Start the Python reference compute backend
backend:
    python3 python/nibli_backend.py

# Full pipeline with compute backend auto-configured
run-with-backend: build-wasm
    NIBLI_COMPUTE_ADDR=127.0.0.1:5555 NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm cargo run -p gasnu {{cargo_profile_flag}}

# Run Python backend tests
test-backend:
    python3 -m pytest python/test_nibli_backend.py -v 2>/dev/null || python3 -m unittest python.test_nibli_backend -v 2>/dev/null || python3 python/test_nibli_backend.py

# Classify Lojban readme — deterministic translation to FOL + English
classify:
    python3 python/lojban_classifier.py readme.lojban

# Run Lojban classifier tests
test-classifier:
    python3 -m pytest python/test_classifier.py -v 2>/dev/null || python3 python/test_classifier.py

# Start GraphQL API server for Transparency Triad (native — no WASM)
# Auto-detects Windows host IP for Ollama (running as Windows desktop app)
server:
    NIBLI_OLLAMA_URL="http://$(ip route | grep default | awk '{print $3}'):11434" cargo run -p nibli-server {{cargo_profile_flag}}

# Start GraphQL API server connected to gossip hub (sees agent gossip in UI)
server-gossip:
    NIBLI_GOSSIP_HUB=127.0.0.1:7777 NIBLI_OLLAMA_URL="http://$(ip route | grep default | awk '{print $3}'):11434" cargo run -p nibli-server {{cargo_profile_flag}}

# Launch Transparency Triad web UI (dev server with hot-reload)
ui:
    cd nibli-ui && dx serve

# Run nibli-store unit tests
test-store:
    cargo test -p nibli-store -- --nocapture

# Run REPL with persistent storage
run-persist: build-wasm
    NIBLI_DB_PATH=nibli.redb NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm cargo run -p gasnu {{cargo_profile_flag}}

# Run tavla gossip tests
test-tavla:
    cargo test -p tavla -- --nocapture --test-threads=1

# Run the full tavla end-to-end gossip integration suite
test-gossip-e2e:
    cargo test -p tavla --test gossip -- --nocapture --test-threads=1

# Deterministic sync/retraction scenario for the CRDT rebuild path
test-sync-retraction:
    cargo test -p tavla --test gossip synced_retraction_survives_reset_and_rebuild -- --nocapture --test-threads=1

# Persistence and replay regressions across engine and store layers
test-persistence-replay:
    cargo test -p nibli-engine --test integration persistent_engine_honors_store_retractions_after_reopen -- --nocapture --test-threads=1
    cargo test -p nibli-store test_merge_from_file_tombstone_survives_reopen -- --nocapture

# Start WebRTC signaling server on port 9090
signal:
    cargo run -p tavla {{cargo_profile_flag}} -- --name signal --listen 127.0.0.1:9999 --signal-server 9090 --transport tcp

# Gossip node A over TCP
gossip-tcp-a:
    cargo run -p tavla {{cargo_profile_flag}} -- --name alis --listen 127.0.0.1:7001 --transport tcp

# Gossip node B over TCP, peers with A
gossip-tcp-b:
    cargo run -p tavla {{cargo_profile_flag}} -- --name bob --listen 127.0.0.1:7002 --peer 127.0.0.1:7001 --transport tcp

# Gossip node A over WebRTC (requires signaling server + webrtc-transport feature)
gossip-webrtc-a:
    cargo run -p tavla --features webrtc-transport {{cargo_profile_flag}} -- --name alis --transport webrtc --signal http://127.0.0.1:9090

# Gossip node B over WebRTC (requires signaling server + webrtc-transport feature)
gossip-webrtc-b:
    cargo run -p tavla --features webrtc-transport {{cargo_profile_flag}} -- --name bob --transport webrtc --signal http://127.0.0.1:9090 --peer alis

# Run every test suite (unit + integration + Python + store + tavla)
test-all: test test-engine test-store test-tavla test-backend test-classifier

# CI gate for the hardened runtime and transport surface
ci: fmt-check clippy-runtime test test-engine test-backend test-store test-server test-gossip-e2e test-persistence-replay test-sync-retraction verify-harness verify-book-vocab

# Build the nibli-validate binary (batch Lojban validation via stdin)
build-validate:
    cargo build -p nibli --bin nibli-validate {{cargo_profile_flag}}

# Manuscript gate: run every Lojban example in book/ through the engine (parse + vocab).
# Detection half of the manuscript-CI gate (see book/tools/README.md).
verify-book: build-validate
    python3 book/tools/verify_book.py --validate-bin target/debug/nibli-validate

# Manuscript gate, vocab-only (fast; no build needed)
verify-book-vocab:
    python3 book/tools/verify_book.py --vocab-only

# Capture-regeneration gate: every transcript block in book/ must match a fresh
# engine capture (book's "captured verbatim" claims, re-checked). Pre-release
# gate, NOT in `ci` — it needs the WASM + gasnu build and replays sessions.
# See book/tools/README.md. Run after any output-affecting engine change.
verify-book-capture: build-wasm
    cargo build -p gasnu {{cargo_profile_flag}}
    NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm python3 book/tools/capture_book.py --check

# Step-zero regression guard (run by `ci`). The logji FOL control test proves the
# deep-chain reasoning path stays sound (it must PASS). The RED known-failure
# backlog (known_failures*) stays opt-in via `-- --ignored` and is NOT run here.
# The book vocab gate (`verify-book-vocab`) joins `ci` once the `xanlu` non-word
# is fixed (revisions P0.2) — it is intentionally red until then.
verify-harness:
    cargo test -p logji --test known_failures_fol {{cargo_profile_flag}} -- --test-threads=1
    cargo test -p nibli-engine --test known_failures {{cargo_profile_flag}} -- --test-threads=1

# Generate training data (requires ANTHROPIC_API_KEY env var)
generate-training: build-validate
    python3 python/generate_training_data.py --output data/training_raw.jsonl

# Resume training data generation from existing file
generate-training-resume: build-validate
    python3 python/generate_training_data.py --output data/training_raw.jsonl --resume

# Dry run: test validation pipeline without API calls
generate-training-dry: build-validate
    python3 python/generate_training_data.py --dry-run

# Show training data statistics
training-stats:
    python3 python/training_stats.py data/training_raw.jsonl

# Export valid pairs to HuggingFace-compatible format
export-hf:
    python3 python/training_stats.py data/training_raw.jsonl --export-hf data/nibli-lojban-dataset.jsonl

# Fine-tune Qwen2.5-7B-Instruct on nibli-lojban dataset (QLoRA)
model-train: build-validate
    python3 python/nibli_model.py train --data data/training_raw.jsonl

# Evaluate fine-tuned model — gerna pass rate is the key metric
model-eval: build-validate
    python3 python/nibli_model.py eval --model models/nibli-lojban-7b

# Flywheel: add gerna-valid alternative translations back to training data
model-refine:
    python3 python/nibli_model.py refine --model models/nibli-lojban-7b --data data/training_raw.jsonl

# Push adapter weights to HuggingFace Hub
model-push:
    python3 python/nibli_model.py push --model models/nibli-lojban-7b --repo dhilipsiva/nibli-lojban-7b

# ─── LLM Gossip Agents ───────────────────────────────────────────

# Run an LLM gossip agent (interactive mode)
# Usage: just agent name=fitness domain=xadni
agent name="agent" domain="" peer="127.0.0.1:7001" provider="anthropic":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name {{name}} --peer {{peer}} --provider {{provider}} \
        {{ if domain != "" { "--domain " + domain } else { "" } }}

# Run an LLM gossip agent in auto-gossip mode
# Usage: just agent-auto name=fitness domain=xadni topic="fitness and exercise"
agent-auto name="agent" domain="" peer="127.0.0.1:7001" provider="anthropic" topic="" interval="30":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name {{name}} --peer {{peer}} --provider {{provider}} \
        --auto-gossip --interval {{interval}} \
        {{ if domain != "" { "--domain " + domain } else { "" } }} \
        {{ if topic != "" { "--topic '" + topic + "'" } else { "" } }}

# Run a gossip hub node for agents to connect to (TCP on port 7777)
gossip-hub:
    cargo run -p tavla {{cargo_profile_flag}} -- --name hub --listen 127.0.0.1:7777 --transport tcp

# Demo: fitness agent (connect to hub on 7777)
agent-fitness:
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name fitness-agent --domain xadni --peer 127.0.0.1:7777

# Demo: nutrition agent (connect to hub on 7777)
agent-nutrition:
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name nutrition-agent --domain cidja --peer 127.0.0.1:7777

# Demo: rights agent (connect to hub on 7777)
agent-rights:
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name rights-agent --domain krali --peer 127.0.0.1:7777

# Demo: fitness agent with Ollama (connect to hub on 7777, auto-detects Windows host IP)
# Usage: just agent-fitness-ollama model=gemma3:27b
agent-fitness-ollama model="qwen3:30b":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name fitness-agent --domain xadni --peer 127.0.0.1:7777 --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434"

# Auto-gossip: Ollama fitness agent (generates + reacts, 45s interval)
agent-auto-ollama model="qwen3:30b" interval="45" topic="fitness and exercise":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name ollama-fitness --domain xadni --peer 127.0.0.1:7777 --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434" --auto-gossip --interval {{interval}} --topic "{{topic}}"

# Auto-gossip: Ollama nutrition agent (generates + reacts, 45s interval)
agent-auto-ollama-nutrition model="qwen3:30b" interval="45" topic="nutrition and healthy eating":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name ollama-nutrition --domain cidja --peer 127.0.0.1:7777 --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434" --auto-gossip --interval {{interval}} --topic "{{topic}}"

# Auto-gossip: Claude fitness agent (generates + reacts, 45s interval)
agent-auto-claude interval="45" topic="fitness and exercise":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name claude-fitness --domain xadni --peer 127.0.0.1:7777 --provider anthropic --auto-gossip --interval {{interval}} --topic "{{topic}}"

# ─── Domain Knowledge Agents ─────────────────────────────────────

# GDPR agent with persistent KB (interactive, connect to hub on 7777)
agent-gdpr model="qwen3:30b":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name gdpr-agent --domain gdpr --peer 127.0.0.1:7777 --db-path gdpr-agent.redb --seed gdpr.lojban --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434"

# Drug interaction agent with persistent KB (interactive, connect to hub on 7777)
agent-drug model="qwen3:30b":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name drug-agent --domain xukmi --peer 127.0.0.1:7777 --db-path drug-agent.redb --seed drug-interactions.lojban --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434"

# Auto-gossip: GDPR agent (generates + reacts, 60s interval)
agent-auto-gdpr model="qwen3:30b" interval="60":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name gdpr-auto --domain gdpr --peer 127.0.0.1:7777 --db-path gdpr-auto.redb --seed gdpr.lojban --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434" --auto-gossip --interval {{interval}} --topic "data protection and privacy"

# Auto-gossip: Drug interaction agent (generates + reacts, 60s interval)
agent-auto-drug model="qwen3:30b" interval="60":
    cargo run -p nibli-agent {{cargo_profile_flag}} -- --name drug-auto --domain xukmi --peer 127.0.0.1:7777 --db-path drug-auto.redb --seed drug-interactions.lojban --provider ollama --model "{{model}}" --ollama-url "http://$(ip route | grep default | awk '{print $3}'):11434" --auto-gossip --interval {{interval}} --topic "drug interactions and medicine"

# ── Fuzz testing (requires cargo +nightly) ──────────────────────

# Fuzz the gerna parser with arbitrary input
fuzz-parse SECONDS="0":
    cd fuzz && cargo +nightly fuzz run fuzz_parse -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Fuzz nibli-engine assert_text (full pipeline)
fuzz-assert SECONDS="0":
    cd fuzz && cargo +nightly fuzz run fuzz_assert -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Fuzz nibli-engine assert + query (stateful KB)
fuzz-query SECONDS="0":
    cd fuzz && cargo +nightly fuzz run fuzz_query -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Wipes all compilation artifacts
clean:
    cargo clean
