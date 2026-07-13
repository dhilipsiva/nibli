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

# Download the maintained lensisku English dictionary (the nibli-lexicon build reads
# ../dictionary-en.json). lensisku's cached dumps are public — no login needed. The
# nightly-regenerated cached export lives at /api/export/cached/{lang}/{format} (GET only;
# HEAD 401s). Gitignored; without it the build falls back to the in-tree dictionary
# (same as CI).
fetch-dict:
    curl -fsSL "https://lensisku.lojban.org/api/export/cached/en/json" \
      -o dictionary-en.json
    @echo "Wrote dictionary-en.json ($(wc -c < dictionary-en.json) bytes)"

# Compiles the single lasna WASM component (nibli-kr/nibli-semantics/logji linked as internal crates)
build-wasm: clean-wasm
    @echo "Building WASI lasna component ({{wasi_target}}, {{profile}})..."
    cargo component build --target {{wasi_target}} {{cargo_profile_flag}} -p nibli-pipeline
    # cargo-component regenerates nibli-pipeline/src/bindings.rs in wit-bindgen's own
    # formatting; normalize it so a later `fmt-check` (ci) doesn't trip on the
    # auto-generated file.
    cargo fmt -p nibli-pipeline

# Compiles the native Wasmtime host gasnu
build-host:
    @echo "Building native host gasnu..."
    cargo build -p nibli-host {{cargo_profile_flag}}

# Smoke-test gasnu non-interactive script mode: pipe a 3-line script (assert,
# query, :facts) into the built binary and assert the echoed prompts + markers.
# Exercises the byte-faithful REPL transcript capture path used for the book.
smoke-host-script: build-wasm build-host
    @echo "Smoke-testing gasnu script mode (piped stdin)..."
    @out=$(printf 'dog(Adam).\n? dog(Adam).\n:facts\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF 'nibli> dog(Adam).' || { echo 'FAIL: missing echoed assert prompt'; exit 1; }; \
        echo "$out" | grep -qF 'nibli> ? dog(Adam).' || { echo 'FAIL: missing echoed query prompt'; exit 1; }; \
        echo "$out" | grep -qF 'nibli> :facts' || { echo 'FAIL: missing echoed :facts prompt'; exit 1; }; \
        echo "$out" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: missing [Fact #0] Asserted.'; exit 1; }; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: missing [Query] TRUE'; exit 1; }; \
        echo "$out" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: missing :facts listing'; exit 1; }; \
        echo 'PASS: gasnu script mode emits echoed prompts + expected markers'

# Trap-recovery smoke: a fuel trap must not brick the session. The host
# rebuilds the poisoned component instance lazily (before the next session
# call, so an intervening :fuel raise applies) and replays the journaled
# mutations deterministically; the post-trap query answers from the replayed
# KB with the original fact ids. Pre-release gate like smoke-host-script
# (needs the WASM build; not part of `ci`).
smoke-host-trap-recovery: build-wasm build-host
    @echo "Smoke-testing gasnu trap recovery (fuel trap mid-session)..."
    @out=$(printf 'dog(Adam).\n:fuel 1000\n? dog(Adam).\n:fuel 10000000000\n? dog(Adam).\n:facts\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] RESOURCE_EXCEEDED (fuel)' || { echo 'FAIL: query fuel trap not translated into a RESOURCE_EXCEEDED (fuel) verdict'; exit 1; }; \
        echo "$out" | grep -qF '[Session] Wasm trap poisoned the component instance; rebuilding and replaying 1 command(s)...' || { echo 'FAIL: missing rebuild message'; exit 1; }; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: post-recovery query did not answer TRUE'; exit 1; }; \
        echo "$out" | grep -qF '#0: dog(Adam).' || { echo 'FAIL: replayed fact #0 missing from :facts'; exit 1; }; \
        if echo "$out" | grep -qF 'cannot enter component instance'; then echo 'FAIL: session still bricked after trap'; exit 1; fi; \
        if echo "$out" | grep -qF 'cannot remove owned resource'; then echo 'FAIL: resource-drop error at exit'; exit 1; fi; \
        echo 'PASS: fuel trap recovered — session rebuilt and replayed'

# Persistent restart-replay smoke: prove the live session's fact-ids stay equal
# to the durable store's across a reopen, INCLUDING a tombstone gap. Run-1
# asserts 3 facts and retracts the middle one; run-2 reopens the SAME db and must
# show the surviving STORE ids (with the gap) and retract the high one by its
# store id. On the pre-fix build, run-2 replays with FRESH ids, so the high store
# id is a zombie and the final query stays TRUE — this recipe FAILS. Pre-release
# gate (needs the WASM build; not part of `ci`).
smoke-host-persist-replay: build-wasm build-host
    @echo "Smoke-testing gasnu persistent restart-replay (fact-id drift)..."
    @dir=$(mktemp -d); db="$dir/nibli-smoke.redb"; \
        out1=$(printf 'dog(Adam).\ndog(Bel).\ndog(Kar).\n:retract 1\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF '[Fact #2] Asserted.' || { echo 'FAIL run1: fact #2 not asserted'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Retract] Fact #1 retracted.' || { echo 'FAIL run1: retract 1'; rm -rf "$dir"; exit 1; }; \
        out2=$(printf ':facts\n:retract 2\n? dog(Kar).\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out2"; \
        echo "$out2" | grep -qF '#2:' || { echo 'FAIL run2: surviving store id #2 missing after reopen (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        if echo "$out2" | grep -qF '#1:'; then echo 'FAIL run2: tombstoned/zombie id #1 present (DRIFT)'; rm -rf "$dir"; exit 1; fi; \
        echo "$out2" | grep -qF '[Retract] Fact #2 retracted.' || { echo 'FAIL run2: surviving store id #2 not retractable (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        echo "$out2" | grep -qF '[Query] FALSE' || { echo 'FAIL run2: retracted fact still entailed (DRIFT)'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: persistent restart-replay keeps live==store fact-ids (gap preserved, high store id retractable)'

# Statement-split smoke: a two-STATEMENT nibli KR input line becomes TWO independent
# facts (ids 0 and 1) — independently listed, retractable, and each persisted as its
# own BUFFER record (recompile-free replay); nibli KR `.`-statement splitting has the
# SAME granularity as Lojban's bare-`.i` split_roots. A conjunction (`&`, the
# `.i je` analog) stays ONE compound fact. Reopen proves per-statement retraction
# survives a restart.
smoke-host-split: build-wasm build-host
    @echo "Smoke-testing gasnu statement split (N independent facts + buffer replay)..."
    @dir=$(mktemp -d); db="$dir/nibli-smoke.redb"; \
        out1=$(printf 'dog(Adam). cat(Betis).\n:facts\n:retract 0\n? dog(Adam).\n? cat(Betis).\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL run1: fact #0 missing'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Fact #1] Asserted.' || { echo 'FAIL run1: fact #1 missing (line not split)'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Facts] 2 active fact(s):' || { echo 'FAIL run1: expected 2 active facts'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '(1 root)' || { echo 'FAIL run1: split facts must be single-root'; rm -rf "$dir"; exit 1; }; \
        verdicts=$(echo "$out1" | grep -F '[Query]' | tr '\n' ' '); \
        [ "$verdicts" = '[Query] FALSE [Query] TRUE ' ] || { echo "FAIL run1: expected FALSE (retracted) then TRUE (surviving), got: $verdicts"; rm -rf "$dir"; exit 1; }; \
        out2=$(printf ':facts\n? cat(Betis).\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out2"; \
        echo "$out2" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL run2: expected exactly the surviving fact after reopen'; rm -rf "$dir"; exit 1; }; \
        echo "$out2" | grep -qF '[Query] TRUE' || { echo 'FAIL run2: surviving statement not replayed from buffer'; rm -rf "$dir"; exit 1; }; \
        out3=$(printf 'dog(Adam) & cat(Adam).\n:facts\n' \
            | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out3"; \
        echo "$out3" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL run3: conjunction must stay ONE compound fact'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: nibli KR statements split into independent, per-statement-retractable, buffer-replayed facts; conjunctions stay whole'

# NAF-note smoke: the closed-world / negation-as-failure flag is now a first-class
# WIT `proof-trace` field — computed once in the guest (ProofTrace::has_naf_dependency),
# carried across the boundary, and READ by gasnu (no longer recomputed host-side). A
# `na`-negated query over an absent fact (closed-world TRUE) must still print the NAF
# note; this guards the wiring end-to-end (a dropped field would silently remove the
# note). Pre-release gate (needs the WASM build; not part of `ci`).
smoke-host-naf: build-wasm build-host
    @echo "Smoke-testing gasnu NAF-dependent proof note (WIT proof-trace flag)..."
    @out=$(printf '? ~dog(Adam).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: NAF query did not answer TRUE'; exit 1; }; \
        echo "$out" | grep -qF '[Note: result depends on negation-as-failure (closed-world assumption)]' || { echo 'FAIL: missing NAF note (naf-dependent flag not carried through the WIT proof-trace)'; exit 1; }; \
        echo 'PASS: NAF-dependent proof carries the closed-world note through the WIT proof-trace'

# CWA-FALSE-note smoke (dual of the NAF note): a positive FALSE that rests on the closed-world
# assumption (a missing fact, not derivable) must print the closed-world caveat, carried as the
# first-class `cwa-false` WIT proof-trace field. A numeric-decided FALSE (`5 = 3`) must NOT — it
# is genuinely false, not closed-world. Guards both directions end-to-end across the WIT boundary.
smoke-host-cwa-false: build-wasm build-host
    @echo "Smoke-testing gasnu closed-world FALSE note (WIT proof-trace cwa-false flag)..."
    @out=$(printf '? dog(Adam).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] FALSE' || { echo 'FAIL: missing-fact query did not answer FALSE'; exit 1; }; \
        echo "$out" | grep -qF '[Note: FALSE is closed-world' || { echo 'FAIL: missing closed-world FALSE note (cwa-false flag not carried through the WIT proof-trace)'; exit 1; }; \
        num=$(printf '? num_equal(5, 3).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$num"; \
        if echo "$num" | grep -qF '[Note: FALSE is closed-world'; then echo 'FAIL: a numeric-decided FALSE wrongly carried the closed-world note'; exit 1; fi; \
        echo 'PASS: closed-world FALSE carries the caveat; numeric-decided FALSE does not'

# Pre-release smoke: exercises the full WASM `:debug` round-trip — lasna guest
# converter (logji -> WIT logic-buffer) -> WIT boundary -> gasnu reverse converter
# (WIT -> nibli_types) -> nibli-render tree + English gloss. An ASYMMETRIC converter
# field-swap (e.g. one side maps And -> Or) is type-valid, so `just check`/`ci` miss
# it, but it corrupts the rendered structure here. NOT in `ci` (needs the WASM build).
smoke-host-debug: build-wasm build-host
    @echo "Smoke-testing gasnu :debug WASM round-trip (typed buffer -> host render)..."
    @out=$(printf ':debug animal(every dog).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Logic]' || { echo 'FAIL: missing [Logic] block'; exit 1; }; \
        echo "$out" | grep -qF '∀ _v0:' || { echo 'FAIL: ForAll node not rendered (converter regression?)'; exit 1; }; \
        echo "$out" | grep -qF 'Or:' || { echo 'FAIL: material-conditional Or node not rendered'; exit 1; }; \
        echo "$out" | grep -qF 'dog_x1(' || { echo 'FAIL: role predicate not rendered functionally'; exit 1; }; \
        echo "$out" | grep -qF '[English] For every X, if X is a dog, then X is an animal.' || { echo 'FAIL: English back-translation wrong (round-trip corrupted)'; exit 1; }; \
        if echo "$out" | grep -qF '(Pred'; then echo 'FAIL: S-expression leaked into :debug output'; exit 1; fi; \
        echo 'PASS: :debug renders the typed buffer host-side (tree + English), no S-expr'

# Pre-release smoke: the collapsed macro-logical-DAG proof view. `?` shows the
# compressed surface-level steps (no role/event scaffolding); `:proof-verbose`
# keeps the full role-level trace. NOT in `ci` (needs the WASM build).
smoke-host-collapse: build-wasm build-host
    @echo "Smoke-testing gasnu collapsed proof (? default) + :proof-verbose escape hatch..."
    @collapsed=$(printf 'dog(Rex).\nanimal(every dog).\n? animal(Rex).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$collapsed"; \
        echo "$collapsed" | grep -qF '[Query] TRUE' || { echo 'FAIL: collapsed query did not answer TRUE'; exit 1; }; \
        echo "$collapsed" | grep -qF 'by the rule' || { echo 'FAIL: collapsed proof missing the macro rule step'; exit 1; }; \
        if echo "$collapsed" | grep -qF 'Conjunction'; then echo 'FAIL: verbose scaffolding leaked into the collapsed ? view'; exit 1; fi; \
        if echo "$collapsed" | grep -qF 'role-level detail'; then echo 'FAIL: role-level detail cluster shown in collapsed text'; exit 1; fi; \
        echo 'PASS: ? shows the clean collapsed macro-logical DAG'
    @verbose=$(printf 'dog(Rex).\nanimal(every dog).\n:proof-verbose animal(Rex).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$verbose"; \
        echo "$verbose" | grep -qF '[Query] TRUE' || { echo 'FAIL: :proof-verbose query did not answer TRUE'; exit 1; }; \
        echo "$verbose" | grep -qF 'Conjunction' || { echo 'FAIL: :proof-verbose did not show the full role-level trace'; exit 1; }; \
        echo 'PASS: :proof-verbose shows the full role-level trace'

# Backend-unavailable smoke: an external compute predicate (exponential) with NO
# backend configured must yield UNKNOWN (backend-unavailable), NEVER a definitive
# FALSE — a backend outage is not a derived falsehood. Exercises the four-valued
# reason end-to-end across the WIT boundary. The `exponential` alias is curated
# (pinned in nibli-lexicon's fallback tables, so the CI fallback build resolves it
# too), mapping to the external `tenfa` gismu. NOT in `ci` (needs the WASM build).
smoke-host-backend-unavailable: build-wasm build-host
    @echo "Smoke-testing gasnu backend-unavailable verdict (no compute backend configured)..."
    @out=$(printf ':compute exponential\n? exponential(8, 2, 3).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] UNKNOWN (backend-unavailable)' || { echo 'FAIL: an unreachable backend did not surface UNKNOWN (backend-unavailable)'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] FALSE'; then echo 'FAIL: backend outage degraded to a definitive FALSE'; exit 1; fi; \
        echo 'PASS: an unreachable compute backend yields UNKNOWN (backend-unavailable), not FALSE'

# Quiet-mode smoke: NIBLI_QUIET=1 suppresses the per-assertion bookkeeping the book
# strips — `[Fact #N]` on the host, `[Skolem]`/`[Rule]` in the guest (the latter reached
# only via the host->guest WASI env hop) — while the verdict + proof trace stay. The
# default (unset) still prints the diagnostics, so a live REPL is unchanged. Guards the
# host gate AND the env forwarding end-to-end. Pre-release gate (needs the WASM build).
smoke-host-quiet: build-wasm build-host
    @echo "Smoke-testing gasnu NIBLI_QUIET mode (suppress [Fact]/[Skolem]/[Rule], keep proof)..."
    @q=$(printf 'dog(Adam).\nanimal(every dog).\n? animal(Adam).\n' \
        | NIBLI_QUIET=1 NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$q"; \
        echo "$q" | grep -qF '[Query] TRUE' || { echo 'FAIL: quiet-mode query lost its verdict'; exit 1; }; \
        echo "$q" | grep -qF 'adam is an animal' || { echo 'FAIL: quiet-mode query lost its proof trace'; exit 1; }; \
        if echo "$q" | grep -qE '\[(Fact|Skolem|Rule)'; then echo 'FAIL: NIBLI_QUIET=1 did not suppress the per-assertion bookkeeping'; exit 1; fi; \
        v=$(printf 'dog(Adam).\nanimal(every dog).\n? animal(Adam).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$v"; \
        echo "$v" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: default (verbose) mode dropped the [Fact] echo'; exit 1; }; \
        echo "$v" | grep -qE '\[(Skolem|Rule)' || { echo 'FAIL: default (verbose) mode dropped the guest [Skolem]/[Rule] diagnostics'; exit 1; }; \
        echo 'PASS: NIBLI_QUIET=1 suppresses [Fact]/[Skolem]/[Rule] but keeps the verdict + proof; default stays verbose'

# Strict-mode plumbing smoke: NIBLI_STRICT=1 reaches the guest at startup, the
# `:strict` toggle round-trips through the component's set-strict function
# without trapping, and normal asserts still work under strict. (The REJECTION
# behavior itself is pinned at the logji level — the event-decomposed surface
# pipeline produces arity-consistent predicates by construction, so a mismatch
# is only constructible programmatically.)
smoke-host-strict: build-wasm build-host
    @echo "Smoke-testing gasnu strict mode (env + :strict toggle plumbing)..."
    @s=$(printf ':strict\ndog(Adam).\n? dog(Adam).\n' \
        | NIBLI_STRICT=1 NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$s"; \
        echo "$s" | grep -qF 'Strict mode: ON' || { echo 'FAIL: NIBLI_STRICT=1 startup banner missing'; exit 1; }; \
        echo "$s" | grep -qF '[Strict] ON' || { echo 'FAIL: :strict status did not report ON'; exit 1; }; \
        echo "$s" | grep -qF '[Query] TRUE' || { echo 'FAIL: a clean assert+query must still work under strict'; exit 1; }; \
        t=$(printf ':strict on\n:strict\n:strict off\n:strict\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$t"; \
        echo "$t" | grep -qF '[Strict] ON' || { echo 'FAIL: :strict on did not take'; exit 1; }; \
        echo "$t" | grep -qF '[Strict] OFF' || { echo 'FAIL: :strict off did not take'; exit 1; }; \
        echo 'PASS: NIBLI_STRICT=1 + :strict toggle plumbing works end to end'

# Executes the full pipeline: Builds WASM modules, then boots the native REPL
run: build-wasm
    @echo "Launching Neuro-Symbolic Engine ({{profile}})..."
    NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm cargo run -p nibli-host {{cargo_profile_flag}}

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
    cargo clippy --no-deps -p nibli-protocol -p nibli-render -p nibli-store -p nibli-engine -p nibli --all-targets -- -D warnings

# Run nibli-lexicon unit tests only — the folded alias-map tests (alias/label/
# reserved) plus the forward-dict tests, one crate now (dev loop; the workspace
# `test` recipe already sweeps them into `ci`)
test-alias-map:
    cargo test -p nibli-lexicon --lib -- --nocapture

# Run nibli-kr (surface-syntax front-end) unit tests only (dev loop; the
# workspace `test` recipe already sweeps them into `ci`)
test-nibli-kr:
    cargo test -p nibli-kr --lib -- --nocapture

# Run all unit tests across workspace
test:
    cargo test --lib -- --nocapture --test-threads=1

# Run nibli-engine integration tests (full pipeline: parse → compile → reason)
test-engine:
    cargo test -p nibli-engine --test integration -- --nocapture --test-threads=1

# Run gasnu host unit tests (pure functions: trap classification, error/verdict
# formatting, arithmetic). gasnu is a normal bin with no lib target, so the
# workspace `test` recipe (`cargo test --lib`) skips it — this gates it in `ci`.
# WASM-independent: does not need the lasna build.
test-host:
    cargo test -p nibli-host

# Run nibli-ui's native tests (the shipped-examples guard: every example KB line
# + preset query compiles through the nibli KR front-end; dual-mode with fallback
# vocab-skips, queries never skip). nibli-ui is a bin-only crate, so the
# workspace `test` recipe (`cargo test --lib`) skips it — this gates it in `ci`.
test-ui:
    cargo test -p nibli-ui --bins

# Start the Python reference compute backend
backend:
    python3 python/nibli_backend.py

# Full pipeline with compute backend auto-configured
run-with-backend: build-wasm
    NIBLI_COMPUTE_ADDR=127.0.0.1:5555 NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm cargo run -p nibli-host {{cargo_profile_flag}}

# Run Python backend tests
test-backend:
    python3 -m pytest python/test_nibli_backend.py -v 2>/dev/null || python3 -m unittest python.test_nibli_backend -v 2>/dev/null || python3 python/test_nibli_backend.py

# Launch the standalone Transparency Triad web UI (dev server with hot-reload) on
# a fixed port (default 8080; override e.g. `just ui 9000`). Reasoning runs fully
# in-browser; the only optional network call is the client-side Translate.
ui PORT="8080":
    cd nibli-ui && dx serve --port {{PORT}}

# Build the nibli-ui web bundle for release — a local preview / pre-merge sanity
# check that the exact shipping bundle compiles. Output:
# target/dx/nibli-ui/release/web/public/ (serve with any static server). NOTE: the
# PRODUCTION build runs in the external dhilipsiva.dev site repo (see DEPLOY.md);
# this recipe is not the production path.
build-ui:
    cd nibli-ui && dx build --release

# Run nibli-store unit tests
test-store:
    cargo test -p nibli-store -- --nocapture

# Run REPL with persistent storage
run-persist: build-wasm
    NIBLI_DB_PATH=nibli.redb NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm cargo run -p nibli-host {{cargo_profile_flag}}

# Persistence and replay regressions across engine and store layers
test-persistence-replay:
    cargo test -p nibli-engine --test integration persistent_engine_honors_store_retractions_after_reopen -- --nocapture --test-threads=1

# Run every test suite (unit + integration + Python + store)
test-all: test test-engine test-store test-backend

# CI gate for the hardened runtime surface (fast; native only — no WASM build).
# For the WASM behavioral smokes too, run `just ci-all`.
ci: fmt-check clippy-runtime test test-engine test-host test-ui test-formalize test-backend test-store test-persistence-replay verify-harness verify-soundness verify-alias-map verify-nibli-kr-seam verify-dict verify-proofs verify-book-vocab

# WASM behavioral gate (pre-push, NOT part of `ci` — needs the WASM build, like
# verify-book-capture). Bundles the gasnu smokes; each depends on
# `build-wasm build-host`, so `just` builds the component + host once, then runs
# them all: fuel exhaustion + post-trap recovery + journal replay
# (trap-recovery), plus the script transcript, persist-replay, NAF-note,
# :debug round-trip, and the determinism corpus.
ci-wasm: smoke-host-script smoke-host-trap-recovery smoke-host-persist-replay smoke-host-split smoke-host-naf smoke-host-cwa-false smoke-host-debug smoke-host-collapse smoke-host-backend-unavailable smoke-host-quiet smoke-host-strict smoke-host-determinism verify-wasm-node

# Three-way determinism, WASMTIME leg: the shared determinism-corpus.nibli must produce
# exactly its pinned annotations through the lasna component under gasnu. The
# native leg is determinism_corpus_nibli_kr_native (verify-nibli-kr-seam); the V8 leg is
# verify-wasm-node.
smoke-host-determinism: build-wasm build-host
    @echo "Smoke-testing gasnu three-way determinism corpus..."
    @expected=$(grep '^# =>' determinism-corpus.nibli | sed 's/^# => //'); \
        actual=$(NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host --script determinism-corpus.nibli 2>&1 | sed -n 's/^\[Query\] //p'); \
        if [ "$expected" = "$actual" ]; then \
            echo 'PASS: gasnu verdicts match every pinned determinism annotation'; \
        else \
            echo 'FAIL: determinism corpus verdict mismatch (wasmtime vs pinned)'; \
            echo '--- expected ---'; echo "$expected"; \
            echo '--- actual ---'; echo "$actual"; exit 1; \
        fi

# Three-way determinism, V8 leg: run the nibli-wasm pipeline (wasm32-unknown-unknown)
# under node via wasm-bindgen-test — the browser-class runtime of the live playground.
# Skips cleanly when wasm-pack is unavailable.
verify-wasm-node:
    @if ! command -v wasm-pack >/dev/null 2>&1; then \
        echo 'verify-wasm-node SKIPPED: wasm-pack unavailable (cargo install wasm-pack)'; \
    else \
        wasm-pack test --node nibli-wasm; \
    fi

# Run nibli-formalize native tests (agentic loop + history trim, local gates incl.
# the render round-trip gate, the shipped-prompt guard, the semantic
# verification turn, LLM request/response shapes).
test-formalize:
    cargo test -p nibli-formalize --lib -- --nocapture

# Comprehensive pre-push / pre-release gate: the fast native `ci` plus the WASM
# behavioral smokes. `ci` alone does not exercise the WASM component.
ci-all: ci ci-wasm

# Build the nibli-validate binary (batch Lojban validation via stdin)
build-validate:
    cargo build -p nibli --bin nibli-validate {{cargo_profile_flag}}

# Manuscript gate: run every book/ example through the engine (parse + vocab).
# Detection half of the manuscript-CI gate (see book/tools/README.md).
# EXPECTED RED until the book migrates to KR (or pins the v0.1-lojban-final
# engine tag): the Lojban front-end retired at THE DROP, so the book's Lojban
# examples no longer compile. Not part of `ci`.
verify-book: build-validate
    python3 book/tools/verify_book.py --validate-bin target/debug/nibli-validate

# Manuscript gate, vocab-only (fast; no build needed). book/ is a SEPARATE repo
# (gitignored here), so it is absent on a fresh checkout / in CI — skip gracefully
# then, mirroring verify_book.py's own dictionary-absent skip (the vocab check
# reads dictionary-en.json, `just fetch-dict`). Runs the gate when present.
verify-book-vocab:
    @if [ -f book/tools/verify_book.py ]; then \
        python3 book/tools/verify_book.py --vocab-only; \
    else \
        echo "verify-book-vocab: book/ not checked out (separate repo) — skipping"; \
    fi

# Book-reference conformance gate (detection only): every WIT name, REPL
# command, Rust struct field, and notation form the book quotes must match the
# repo (book/tools/verify_book_refs.py — the structural fix for the audit's
# WIT/struct/REPL-drift finding, which no other gate catches). EXPECTED to fail
# until the book-repo reconciliation pass lands; wiring it into `ci` is a
# book-repo decision after that. Skips gracefully when book/ is absent.
verify-book-refs:
    @if [ -f book/tools/verify_book_refs.py ]; then \
        python3 book/tools/verify_book_refs.py; \
    else \
        echo "verify-book-refs: book/ not checked out (separate repo) — skipping"; \
    fi

# Capture-regeneration gate: every transcript block in book/ must match a fresh
# engine capture (book's "captured verbatim" claims, re-checked). Pre-release
# gate, NOT in `ci` — it needs the WASM + gasnu build and replays sessions.
# See book/tools/README.md. Run after any output-affecting engine change.
verify-book-capture: build-wasm
    cargo build -p nibli-host {{cargo_profile_flag}}
    NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm python3 book/tools/capture_book.py --check

# Step-zero regression guard (run by `ci`). The logji FOL control test proves the
# deep-chain reasoning path stays sound (it must PASS). The RED known-failure
# backlog (known_failures*) stays opt-in via `-- --ignored` and is NOT run here.
# The book vocab gate (`verify-book-vocab`) joins `ci` once the `xanlu` non-word
# is fixed (revisions P0.2) — it is intentionally red until then.
verify-harness:
    cargo test -p nibli-reason --test known_failures_fol {{cargo_profile_flag}} -- --test-threads=1
    cargo test -p nibli-engine --test known_failures {{cargo_profile_flag}} -- --test-threads=1

# Differential SOUNDNESS gate (Track A), two oracles: nibli's verdict must agree with
# (1) the Vampire FOL prover over the Horn/NAF-free fragment, and (2) the clingo ASP solver
# over the stratified-NAF + closed-world fragment (curated + random NAF programs). The Nix
# dev shell provides `vampire` + `clingo`; each side skips cleanly if its solver is absent.
verify-soundness:
    cargo test -p nibli-verify --lib --test differential_gate {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Alias-map differential gate: the SHIPPED nibli-lexicon alias map's intra-crate
# invariants (per-alias arity self-consistency, GISMU_TO_ALIAS round-trips, swap
# validity, reserved/label integrity from the shipped map) plus a behavioral leg:
# alias(A, B, ...) must compile canonically EQUAL to the raw-gismu spelling with
# explicit permuted xN labels, for EVERY shipped alias. Dual-mode and never skips: a full
# local build checks all ~1,341 aliases; the CI fallback build checks the curated core
# with a loud FALLBACK MODE banner. Since the fold, alias↔dictionary arity agreement
# holds by construction (one crate, one parse).
verify-alias-map:
    cargo test -p nibli-verify --test alias_differential {{cargo_profile_flag}} -- --nocapture --test-threads=1

# The KR→smuni seam-conformance gate — the KR front-end's LOJBAN-FREE
# independent oracle, built to outlive THE DROP (TODO.md): hand-verified
# FOL structural goldens for the core construct classes (event decomposition,
# rule vs ∃-conjunction shapes, converted-alias/named-arg routing, tense/
# deontic order incl. the O3 pin, flat `du`, prenex implication, abstraction
# opacity, exact-count-0, `?`-independence), the CONSTRUCT_INVENTORY
# acceptance sweep (every §3–§9 KR spelling compiles), KR-internal
# metamorphic relations (the O7 block-every ≡ prenex pin re-anchored KR≡KR,
# named≡positional, converted≡label-permuted, + a 60-seed batch over three
# families), and the re-homed `determinism_corpus_nibli_kr_native` leg.
# Curated-core vocabulary only: full-strength in BOTH dictionary modes,
# never skips. Part of `ci`.
verify-nibli-kr-seam:
    cargo test -p nibli-verify --test nibli_kr_seam_gate {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Dictionary-arity differential gate: the shipped nibli-lexicon arities must COVER the
# independent Predilex bounds (vendored CC0 thesaurus, nibli-verify/vendor/predilex/) —
# an undercount means the dictionary truncates places the word supports. Dual-mode and
# never skips: a full local build (`just fetch-dict`) checks ~198 words; the CI fallback
# build checks the curated core set with a loud FALLBACK MODE banner.
verify-dict:
    cargo test -p nibli-verify --test predilex_differential {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Mechanized-proof gate (Track B): check the Lean 4 soundness proofs in `proofs/`. The Nix
# dev shell provides `lean`; `lean` exits non-zero on any unproved/false theorem. Skips
# cleanly if `lean` is absent (the proofs are still conformance-checked from Rust via the
# `exhaustive_soundness_matches_lean_model` test in `cargo test -p nibli-reason`).
verify-proofs:
    @if command -v lean >/dev/null 2>&1; then \
        for f in proofs/*.lean; do echo "checking $f"; lean "$f" || exit 1; done; \
        echo "verify-proofs: all proofs/*.lean check (mechanized soundness)"; \
    else \
        echo "verify-proofs: lean not found (the Nix dev shell provides it) — skipping"; \
    fi

# ── Fuzz testing (libFuzzer via the Nix shell's pinned nightly) ──
#
# The Nix shell exports NIBLI_NIGHTLY_BIN (flake.nix) — a pinned nightly
# toolchain used ONLY by these recipes via a PATH prefix (libFuzzer needs
# nightly sanitizer-coverage flags); the shell default stays stable.
#
# Leak detection is ON (libFuzzer default): the AST arena is leak-free by
# invariant (see gerna/src/ast.rs — no owned String/Vec in arena-moved nodes),
# and LSan is the gate that keeps it that way.

# Fuzz nibli-engine assert_text (full pipeline)
fuzz-assert SECONDS="0":
    @test -n "${NIBLI_NIGHTLY_BIN:-}" || { echo "NIBLI_NIGHTLY_BIN is not set — run inside the Nix dev shell"; exit 1; }
    cd fuzz && PATH="$NIBLI_NIGHTLY_BIN:$PATH" cargo fuzz run fuzz_assert -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Fuzz nibli-engine assert + query (stateful KB)
fuzz-query SECONDS="0":
    @test -n "${NIBLI_NIGHTLY_BIN:-}" || { echo "NIBLI_NIGHTLY_BIN is not set — run inside the Nix dev shell"; exit 1; }
    cd fuzz && PATH="$NIBLI_NIGHTLY_BIN:$PATH" cargo fuzz run fuzz_query -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Fuzz the nibli KR front-end (parse -> resolve -> emit), asserting any accepted
# input compiles through smuni WITHOUT a "corrupt AST buffer" rejection — a
# structurally invalid emitted buffer is a nibli-kr bug, surfaced as a panic.
fuzz-nibli-kr SECONDS="0":
    @test -n "${NIBLI_NIGHTLY_BIN:-}" || { echo "NIBLI_NIGHTLY_BIN is not set — run inside the Nix dev shell"; exit 1; }
    cd fuzz && PATH="$NIBLI_NIGHTLY_BIN:$PATH" cargo fuzz run fuzz_nibli_kr -- -max_len=4096 {{ if SECONDS != "0" { "-max_total_time=" + SECONDS } else { "" } }}

# Seed the fuzz corpora. Each non-comment line of the shipped .nibli corpus
# files (+ the nibli KR acceptance corpus) becomes a seed for fuzz_assert and
# fuzz_nibli_kr; fuzz_query seeds are the line DOUBLED, matching its split-half
# input encoding (first half asserted, second half queried).
fuzz-seed:
    #!/usr/bin/env python3
    import pathlib
    nibli_kr_lines = []
    for src in ("nibli-kr/tests/acceptance.nibli", "gdpr.nibli", "drug-interactions.nibli", "readme.nibli", "determinism-corpus.nibli"):
        for ln in pathlib.Path(src).read_text(encoding="utf-8").splitlines():
            ln = ln.strip()
            if ln and not ln.startswith("#") and not ln.startswith(":"):
                nibli_kr_lines.append(ln)
    for target, encode in (("fuzz_assert", str), ("fuzz_query", lambda s: s + s), ("fuzz_nibli_kr", str)):
        d = pathlib.Path("fuzz/corpus") / target
        d.mkdir(parents=True, exist_ok=True)
        for i, ln in enumerate(nibli_kr_lines):
            (d / f"seed_{i:04}").write_text(encode(ln), encoding="utf-8")
    print(f"seeded {len(nibli_kr_lines)} .nibli entries x 3 targets under fuzz/corpus/")

# Time-boxed unattended fuzz gate (CI): seed corpora, then run every target for
# SECONDS each. libFuzzer exits non-zero on crash/OOM, zero when the time box
# expires clean — a pass/fail gate, not an open-ended campaign.
fuzz-ci SECONDS="120": fuzz-seed (fuzz-assert SECONDS) (fuzz-query SECONDS) (fuzz-nibli-kr SECONDS)

# ── Mutation testing (soundness paths) ──────────────────────────

# Mutation-testing gate over the soundness-critical paths (scope lives in
# .cargo/mutants.toml: logji reasoning/rules/kb + smuni semantic). Runs the
# full sweep, then diffs survivors against the checked-in baseline
# (mutants-baseline.txt; line:col stripped so unrelated edits don't shift
# entries): exits non-zero on any NEW survivor — a regression in test kill
# power. Baseline entries that are now KILLED print a shrink prompt.
mutants JOBS="8":
    #!/usr/bin/env bash
    set -u
    cargo mutants -j {{ JOBS }}
    status=$?
    # 0 = all caught; 2 = missed mutants (diffed against the baseline below);
    # 3 = timeouts present (a hang IS a catch — the tests noticed; 3 masks 2,
    # so the baseline diff below still runs). Anything else is a real failure.
    if [ $status -ne 0 ] && [ $status -ne 2 ] && [ $status -ne 3 ]; then
        echo "cargo-mutants failed (exit $status is not a missed/timeout status)"
        exit $status
    fi
    sed -E 's/^([^:]+):[0-9]+:[0-9]+: /\1: /' mutants.out/missed.txt | sort -u > mutants.out/missed-normalized.txt
    grep -v '^#' mutants-baseline.txt | grep -v '^$' | sort -u > mutants.out/baseline-normalized.txt
    new=$(comm -13 mutants.out/baseline-normalized.txt mutants.out/missed-normalized.txt)
    gone=$(comm -23 mutants.out/baseline-normalized.txt mutants.out/missed-normalized.txt)
    if [ -n "$new" ]; then
        echo "MUTANTS GATE FAILED — survivors not in mutants-baseline.txt (kill with a test or triage + document):"
        echo "$new"
        exit 1
    fi
    if [ -n "$gone" ]; then
        echo "note: these baseline survivors are now KILLED — remove them from mutants-baseline.txt:"
        echo "$gone"
    fi
    echo "mutants gate clean: $(wc -l < mutants.out/missed-normalized.txt) documented survivor(s), 0 new"

# Import an RDF Turtle / OWL file into a fresh KB and report (see
# `nibli-import --help` for --raw / --export / --query flags). NOTE: just's
# variadic ARGS lose shell quoting — for a multi-word `--query "<text>"`,
# run the built binary directly (`./target/debug/nibli-import …`).
import FILE *ARGS:
    cargo run -p nibli --bin nibli-import -- {{FILE}} {{ARGS}}

# Timing pins for the book's quoted figures (Ch 13 latency numbers, Ch 20 full
# Ch-20 sequence): release-profile, native in-process engine, gdpr.nibli corpus,
# min/median/max over NIBLI_BENCH_RUNS runs (default 10) with verdicts asserted.
# The source for any latency figure the book quotes — never hand-write timings.
bench-book:
    cargo run --release -p nibli --bin nibli-bench-book

# Count the test suite: unit = workspace lib targets; plus the native
# integration/bin test binaries (nibli-engine, gasnu, nibli-verify — the ones
# CI links and runs; lasna's cdylib test target cannot link). The derivation
# for any doc that needs a figure — never hand-write test counts into docs
# (stale counts were an audit finding; see the pre-commit checklist).
count-tests:
    @u=$(cargo test --workspace --lib -- --list 2>/dev/null | grep -c ': test$'); \
    e=$(cargo test -p nibli-engine --tests -- --list 2>/dev/null | grep -c ': test$'); \
    g=$(cargo test -p nibli-host -- --list 2>/dev/null | grep -c ': test$'); \
    v=$(cargo test -p nibli-verify --tests -- --list 2>/dev/null | grep -c ': test$'); \
    echo "unit (workspace --lib):      $u"; \
    echo "nibli-engine test targets:   $e"; \
    echo "gasnu bin tests:             $g"; \
    echo "nibli-verify test targets:   $v"; \
    echo "total: $((u + e + g + v))  (a few lib tests appear in both the unit and per-crate figures)"

# Wipes all compilation artifacts
clean:
    cargo clean
