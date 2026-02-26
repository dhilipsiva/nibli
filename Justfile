set shell := ["bash", "-c"]

wasi_target := "wasm32-wasip2"
wasm_dir := "target/" + wasi_target + "/release"

# The default target executes the full build-and-run pipeline
default: run

# Remove stale WASM artifacts to guarantee fresh compilation
clean-wasm:
    @echo "Removing stale WASM artifacts..."
    rm -f {{wasm_dir}}/*.wasm

# Compiles the discrete WebAssembly components and fuses them
build-wasm: clean-wasm
    @echo "Building WASI components ({{wasi_target}})..."
    cargo component build --release --target {{wasi_target}} -p parser -p semantics -p reasoning -p orchestrator
    @echo "Fusing components with WAC..."
    wac plug {{wasm_dir}}/orchestrator.wasm \
        --plug {{wasm_dir}}/parser.wasm \
        --plug {{wasm_dir}}/semantics.wasm \
        --plug {{wasm_dir}}/reasoning.wasm \
        -o {{wasm_dir}}/engine-pipeline.wasm

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
