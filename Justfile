set shell := ["bash", "-c"]

wasi_target := "wasm32-wasip2"

# Build profile: "debug" (default) or "release"
profile := env("NIBLI_PROFILE", "debug")

# Cargo flags derived from profile
cargo_profile_flag := if profile == "release" { "--release" } else { "" }

# WASM output directory matches profile
wasm_dir := "target/" + wasi_target + "/" + profile

# The default target executes the full build-and-run pipeline (debug)
default: run

# Remove stale WASM artifacts to guarantee fresh compilation
clean-wasm:
    @echo "Removing stale WASM artifacts ({{profile}})..."
    rm -f {{wasm_dir}}/*.wasm

# Compiles the discrete WebAssembly components and fuses them
build-wasm: clean-wasm
    @echo "Building WASI components ({{wasi_target}}, {{profile}})..."
    cargo component build {{cargo_profile_flag}} --target {{wasi_target}} -p gerna -p smuni -p logji -p lasna
    @echo "Fusing components with WAC..."
    wac plug {{wasm_dir}}/lasna.wasm \
        --plug {{wasm_dir}}/gerna.wasm \
        --plug {{wasm_dir}}/smuni.wasm \
        --plug {{wasm_dir}}/logji.wasm \
        -o {{wasm_dir}}/lasna-pipeline.wasm

# Compiles the native Wasmtime host gasnu
build-gasnu:
    @echo "Building native host gasnu ({{profile}})..."
    cargo build {{cargo_profile_flag}} -p gasnu

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine ({{profile}})..."
    RUST_BACKTRACE=full cargo run {{cargo_profile_flag}} -p gasnu

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
    NIBLI_COMPUTE_ADDR=127.0.0.1:5555 cargo run {{cargo_profile_flag}} -p gasnu

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
