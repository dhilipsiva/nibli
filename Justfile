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

# Compiles the discrete WebAssembly components and fuses them
build-wasm: clean-wasm
    @echo "Building WASI components ({{wasi_target}}, {{profile}})..."
    cargo component build --target {{wasi_target}} {{cargo_profile_flag}} -p gerna -p smuni -p logji -p lasna
    @echo "Fusing components with WAC..."
    wac plug {{wasm_dir}}/lasna.wasm \
        --plug {{wasm_dir}}/gerna.wasm \
        --plug {{wasm_dir}}/smuni.wasm \
        --plug {{wasm_dir}}/logji.wasm \
        -o {{wasm_dir}}/lasna-pipeline.wasm

# Compiles the native Wasmtime host gasnu
build-gasnu:
    @echo "Building native host gasnu..."
    cargo build -p gasnu {{cargo_profile_flag}}

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine ({{profile}})..."
    NIBLI_WASM_PATH={{wasm_dir}}/lasna-pipeline.wasm cargo run -p gasnu {{cargo_profile_flag}}

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

# Run gerna unit tests only (bypasses cdylib linker issues)
test-gerna:
    cargo test -p gerna --lib -- --nocapture

# Run all unit tests across workspace
test:
    cargo test --lib -- --nocapture --test-threads=1

# Run nibli-engine integration tests (full pipeline: parse → compile → reason)
test-engine:
    cargo test -p nibli-engine --test integration -- --nocapture --test-threads=1

# Start the Python reference compute backend
backend:
    python3 python/nibli_backend.py

# Full pipeline with compute backend auto-configured
run-with-backend: build-wasm
    NIBLI_COMPUTE_ADDR=127.0.0.1:5555 NIBLI_WASM_PATH={{wasm_dir}}/lasna-pipeline.wasm cargo run -p gasnu {{cargo_profile_flag}}

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

# Launch Transparency Triad web UI (dev server with hot-reload)
ui:
    cd nibli-ui && dx serve

# Run nibli-store unit tests
test-store:
    cargo test -p nibli-store -- --nocapture

# Run REPL with persistent storage
run-persist: build-wasm
    NIBLI_DB_PATH=nibli.redb NIBLI_WASM_PATH={{wasm_dir}}/lasna-pipeline.wasm cargo run -p gasnu {{cargo_profile_flag}}

# Run tavla gossip tests
test-tavla:
    cargo test -p tavla -- --nocapture --test-threads=1

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

# Build the nibli-validate binary (batch Lojban validation via stdin)
build-validate:
    cargo build -p nibli --bin nibli-validate {{cargo_profile_flag}}

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

# Wipes all compilation artifacts
clean:
    cargo clean
