set shell := ["bash", "-c"]

wasi_target := "wasm32-wasip2"
wasm_dir := "target/" + wasi_target + "/debug"

export RUST_BACKTRACE := "full"

# The default target executes the full build-and-run pipeline
default: run

# Remove stale WASM artifacts (both debug and release) to guarantee fresh compilation
clean-wasm:
    @echo "Removing stale WASM artifacts..."
    rm -f target/wasm32-wasip2/debug/*.wasm
    rm -f target/wasm32-wasip2/release/*.wasm

# Compiles the discrete WebAssembly components and fuses them
build-wasm: clean-wasm
    @echo "Building WASI components ({{wasi_target}})..."
    cargo component build --target {{wasi_target}} -p gerna -p smuni -p logji -p lasna
    @echo "Fusing components with WAC..."
    wac plug {{wasm_dir}}/lasna.wasm \
        --plug {{wasm_dir}}/gerna.wasm \
        --plug {{wasm_dir}}/smuni.wasm \
        --plug {{wasm_dir}}/logji.wasm \
        -o {{wasm_dir}}/lasna-pipeline.wasm

# Compiles the native Wasmtime host gasnu
build-gasnu:
    @echo "Building native host gasnu..."
    cargo build -p gasnu

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine..."
    NIBLI_WASM_PATH={{wasm_dir}}/lasna-pipeline.wasm cargo run -p gasnu

# Build the native Linux binary (no WASM, full backtraces)
build-native:
    @echo "Building native nibli binary..."
    cargo build -p nibli

# Run the native REPL (no WASM sandbox — unlimited memory, full Rust backtraces)
run-native: build-native
    @echo "Launching Native Neuro-Symbolic Engine..."
    cargo run -p nibli

# Run gerna unit tests only (bypasses cdylib linker issues)
test-gerna:
    cargo test -p gerna --lib -- --nocapture

# Run all unit tests across workspace
test:
    cargo test --lib -- --nocapture --test-threads=1

# Start the Python reference compute backend
backend:
    python3 python/nibli_backend.py

# Full pipeline with compute backend auto-configured
run-with-backend: build-wasm
    NIBLI_COMPUTE_ADDR=127.0.0.1:5555 NIBLI_WASM_PATH={{wasm_dir}}/lasna-pipeline.wasm cargo run -p gasnu

# Run Python backend tests
test-backend:
    python3 -m pytest python/test_nibli_backend.py -v 2>/dev/null || python3 -m unittest python.test_nibli_backend -v 2>/dev/null || python3 python/test_nibli_backend.py

# Classify Lojban readme — deterministic translation to FOL + English
classify:
    python3 python/lojban_classifier.py readme.lojban

# Run Lojban classifier tests
test-classifier:
    python3 -m pytest python/test_classifier.py -v 2>/dev/null || python3 python/test_classifier.py

# Wipes all compilation artifacts
clean:
    cargo clean
