set shell := ["bash", "-c"]

# The default target executes the full build-and-run pipeline
default: run

# Remove stale WASM artifacts to guarantee fresh compilation
clean-wasm:
    @echo "Removing stale WASM artifacts..."
    rm -f target/wasm32-wasip1/release/*.wasm

# Compiles the discrete WebAssembly components and fuses them
build-wasm: clean-wasm
    @echo "Building WASI Preview 2 components..."
    cargo component build --release -p parser -p semantics -p reasoning -p orchestrator
    @echo "Fusing components with WAC..."
    wac plug target/wasm32-wasip1/release/orchestrator.wasm \
        --plug target/wasm32-wasip1/release/parser.wasm \
        --plug target/wasm32-wasip1/release/semantics.wasm \
        --plug target/wasm32-wasip1/release/reasoning.wasm \
        -o target/wasm32-wasip1/release/engine-pipeline.wasm

# Compiles the native Wasmtime host runner
build-runner:
    @echo "Building native host runner..."
    cargo build --release -p runner

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine..."
    cargo run --release -p runner

# Run parser unit tests only (bypasses cdylib linker issues)
test-parser:
    cargo test -p parser --lib -- --nocapture

# Run all unit tests across workspace
# --test-threads=1 required: reasoning tests share global state (EGRAPH, KNOWN_ENTITIES)
test:
    cargo test --lib -- --nocapture --test-threads=1

# Wipes all compilation artifacts
clean:
    cargo clean
