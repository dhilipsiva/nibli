set shell := ["bash", "-c"]

# The default target executes the full build-and-run pipeline
default: run

# Compiles the discrete WebAssembly components to wasm32-wasip2
build-wasm:
    @echo "Building WASI Preview 2 components..."
    cargo component build --release --target wasm32-wasip2 -p parser -p semantics -p reasoning

# Compiles the native Wasmtime host runner
build-runner:
    @echo "Building native host runner..."
    cargo build --release -p runner

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine..."
    cargo run --release -p runner

# Wipes all compilation artifacts
clean:
    cargo clean
