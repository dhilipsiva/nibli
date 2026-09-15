set shell := ["bash", "-c"]

wasi_target := "wasm32-wasip2"
# Build profile: "debug" (default) or "release" (use `just profile=release run`)
profile := "debug"
wasm_dir := "target/" + wasi_target + "/" + profile
cargo_profile_flag := if profile == "release" { "--release" } else { "" }

export RUST_BACKTRACE := "full"

# The default target executes the full build-and-run pipeline
default: run

# Research artifact. Run these inside `nix develop .#paper` (same flake lock).
paper-driver:
    cargo build --release --locked -p nibli --features bench-bins --bin nibli-bench-paper

paper-check: paper-driver
    python3 paper/scripts/run.py check

paper-smoke: paper-driver
    python3 paper/scripts/run.py smoke

paper-evaluate: paper-driver
    python3 paper/scripts/run.py evaluate
    python3 paper/scripts/analyze.py

paper-build:
    python3 paper/scripts/analyze.py
    python3 paper/scripts/check_artifact.py
    python3 paper/scripts/build.py

paper-package: paper-build
    python3 paper/scripts/package.py

# Remove stale WASM artifacts for the active profile
clean-wasm:
    @echo "Removing stale WASM artifacts ({{profile}})..."
    rm -f {{wasm_dir}}/*.wasm

# Remove stale WASM artifacts for both debug and release
clean-wasm-all:
    @echo "Removing all WASM artifacts..."
    rm -f target/wasm32-wasip2/debug/*.wasm
    rm -f target/wasm32-wasip2/release/*.wasm

# Download the maintained lensisku English dictionary — since the committed-corpus
# milestone this is ONLY the input of `just regen-lexicon` (tools/lexigen); no build
# reads it. lensisku's cached dumps are public — no login needed. The nightly-
# regenerated cached export lives at /api/export/cached/{lang}/{format} (GET only;
# HEAD 401s). Gitignored.
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
        echo "$out" | grep -qF '[Session] Rebuilding and replaying 4 command(s)...' || { echo 'FAIL: missing rebuild message'; exit 1; }; \
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

# Count assertion boundary through the real WIT component + persistent host:
# a later count root rejects the whole call before a durable/live id exists;
# exact-zero/one remain current-model queries; ordinary facts persist/replay.
smoke-host-count-query-only: build-wasm build-host
    @echo "Smoke-testing gasnu query-only exact counts (atomic assert + replay)..."
    @dir=$(mktemp -d); db="$dir/nibli-count.redb"; \
        out1=$(printf 'person(Adam). big(exactly 1 dog).\n:facts\n? person(Adam).\n? big(no dog).\ndog(Bel) & big(Bel).\n? big(exactly 1 dog).\n:facts\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF 'query-only and cannot be asserted' || { echo 'FAIL: outer count assertion was not rejected clearly'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Facts] Knowledge base is empty.' || { echo 'FAIL: mixed rejected call left a partial fact or row'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: rejection consumed the first id'; rm -rf "$dir"; exit 1; }; \
        verdicts=$(echo "$out1" | grep -F '[Query]' | tr '\n' ' '); \
        [ "$verdicts" = '[Query] FALSE [Query] TRUE [Query] TRUE ' ] || { echo "FAIL: expected person FALSE, zero TRUE, one TRUE; got: $verdicts"; rm -rf "$dir"; exit 1; }; \
        out2=$(printf '? big(exactly 1 dog).\n:facts\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out2"; \
        echo "$out2" | grep -qF '[Query] TRUE' || { echo 'FAIL: ordinary supporting fact did not replay'; rm -rf "$dir"; exit 1; }; \
        echo "$out2" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: rejected count call wrote a durable row'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: exact counts are query-only and mixed assertion rejection is atomic across WIT + persistence'

# Schema v2→v3 migration smoke: a legacy `StoredAssertion::Text` row (which the host can
# no longer WRITE) is recompiled once on open into a `Buffer` row via `compile-debug`,
# replays to the right verdict, and the DB is stamped v3 (a second run does NOT
# re-migrate). Negative: a non-KR (Lojban-era) Text row that will not recompile aborts
# startup NON-destructively — the DB stays v2 (a re-run still attempts migration). Seeds
# the pre-v3 fixture with the `seed_v2_text` bin (raw redb). Pre-release gate.
smoke-host-schema-v3-migration: build-wasm build-host
    @echo "Smoke-testing gasnu schema v2→v3 migration (Text→Buffer recompile-once)..."
    @cargo build {{cargo_profile_flag}} -p nibli-store --bin seed_v2_text >/dev/null 2>&1; \
        dir=$(mktemp -d); db="$dir/nibli-v2.redb"; \
        ./target/{{profile}}/seed_v2_text "$db" 5 'dog(Adam).'; \
        out1=$(printf ':facts\n? dog(Adam).\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF 'Migrated 1 legacy text fact' || { echo 'FAIL: migration did not run on the v2 Text row'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Query] TRUE' || { echo 'FAIL: migrated fact did not replay to TRUE'; rm -rf "$dir"; exit 1; }; \
        out2=$(printf '? dog(Adam).\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out2"; \
        if echo "$out2" | grep -qF 'Migrated'; then echo 'FAIL: second run re-migrated (DB not stamped v3)'; rm -rf "$dir"; exit 1; fi; \
        echo "$out2" | grep -qF '[Query] TRUE' || { echo 'FAIL: v3 buffer replay lost the fact'; rm -rf "$dir"; exit 1; }; \
        db2="$dir/nibli-v2-bad.redb"; \
        ./target/{{profile}}/seed_v2_text "$db2" 5 'ro lo gerku cu danlu'; \
        out3=$(printf '? dog(Adam).\n' \
            | NIBLI_DB_PATH="$db2" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1 || true); \
        echo "$out3"; \
        echo "$out3" | grep -qF 'migration failed' || { echo 'FAIL: a non-KR Text row must abort with a migration error'; rm -rf "$dir"; exit 1; }; \
        out4=$(printf '? dog(Adam).\n' \
            | NIBLI_DB_PATH="$db2" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1 || true); \
        echo "$out4" | grep -qF 'migration failed' || { echo 'FAIL: a failed migration must leave the DB at v2 (re-run still migrates)'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: schema v2→v3 migrates Text→Buffer (replays TRUE, stamps v3) and fails closed non-destructively on non-KR rows'

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
# reason end-to-end across the WIT boundary. `exponential` is a committed corpus
# entry (source gismu tenfa), so it resolves in every build. NOT in `ci` (needs
# the WASM build).
smoke-host-backend-unavailable: build-wasm build-host
    @echo "Smoke-testing gasnu backend-unavailable verdict (no compute backend configured)..."
    @out=$(printf ':compute exponential\n? exponential(8, 2, 3).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] UNKNOWN (backend-unavailable)' || { echo 'FAIL: an unreachable backend did not surface UNKNOWN (backend-unavailable)'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] FALSE'; then echo 'FAIL: backend outage degraded to a definitive FALSE'; exit 1; fi; \
        echo 'PASS: an unreachable compute backend yields UNKNOWN (backend-unavailable), not FALSE'

# Reference external-compute names are query-only at assertion ingress across the
# WIT boundary + persistent host, REGISTERED OR NOT (decided 2026-08-09): an
# unregistered `exponential(2, 3, 8).` used to store as an ordinary fact that no
# compute query would ever consult after registration. Mixed statements reject
# atomically; the refusal consumes no id; nothing persists. NOT in `ci` (needs
# the WASM build).
smoke-host-compute-query-only: build-wasm build-host
    @echo "Smoke-testing gasnu query-only reference compute names (assertion ingress)..."
    @dir=$(mktemp -d); db="$dir/nibli-compute.redb"; \
        out1=$(printf 'exponential(2, 3, 8).\nperson(Adam). logarithm(3, 8, 2).\n? person(Adam).\n:facts\nperson(Adam).\n:facts\n' \
            | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out1"; \
        echo "$out1" | grep -qF 'reserved for EXTERNAL COMPUTE' || { echo 'FAIL: an unregistered reference compute assertion was not refused by the name guard'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Facts] Knowledge base is empty.' || { echo 'FAIL: mixed refused call left a partial fact'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Query] FALSE' || { echo 'FAIL: person must be FALSE — the mixed call had to reject atomically'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: the refusals consumed a fact id'; rm -rf "$dir"; exit 1; }; \
        echo "$out1" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: an ordinary fact after the refusals did not assert'; rm -rf "$dir"; exit 1; }; \
        out2=$(printf ':facts\n' | NIBLI_DB_PATH="$db" NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out2"; \
        echo "$out2" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: a refused compute assertion wrote a durable row'; rm -rf "$dir"; exit 1; }; \
        rm -rf "$dir"; \
        echo 'PASS: reference compute names are query-only at assertion ingress, atomically, across WIT + persistence'

# Compute text-contract + registration-order closure across the WIT boundary
# (decided 2026-08-09, corpus boundary reconciled 2026-08-13). An unknown
# `:compute` name is refused because registration declares neither vocabulary nor
# arity, and the same unknown KR query remains a compile error. A corpus
# over-arity query also fails before dispatch. Separately, `:compute <name>` over
# a corpus relation with LIVE stored statements is refused naming the blocking
# ids; after retraction registration succeeds and the valid query dispatches.
# Bare `:compute` reports the canonical registry. The tail pins `:reset` journal
# retention: `reset-kb` clears facts but NOT the guest registry, so after a fuel
# trap the rebuilt session must still refuse a `person` assertion as query-only.
# NOT in `ci` (needs the WASM build).
smoke-host-compute-registration-order: build-wasm build-host
    @echo "Smoke-testing gasnu corpus-scoped, fallible :compute..."
    @out=$(printf ':compute external_probe\n? external_probe(Sample).\nperson(Adam).\n:compute person\n:facts\n:retract 0\n:compute person\n:compute\n? person(Adam).\n? person(Adam, Bel).\n:reset\n:fuel 1000\n? dog(Adam).\n:fuel 10000000000\nperson(Bel).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF 'not a corpus-resolvable nibli KR predicate' || { echo 'FAIL: an unknown compute registration was not refused at the WIT boundary'; exit 1; }; \
        echo "$out" | grep -qF 'unknown predicate "external_probe": not a corpus name' || { echo 'FAIL: registration changed the fail-closed unknown-text query contract'; exit 1; }; \
        echo "$out" | grep -qF 'cannot register' || { echo 'FAIL: registration over a live fact was not refused'; exit 1; }; \
        echo "$out" | grep -qF '(#0)' || { echo 'FAIL: the refusal did not name the blocking fact id'; exit 1; }; \
        echo "$out" | grep -qF '[Facts] 1 active fact(s):' || { echo 'FAIL: the refused registration disturbed the KB'; exit 1; }; \
        [ "$(echo "$out" | grep -cF "[Compute] Registered corpus predicate 'person'")" -eq 1 ] || { echo 'FAIL: expected exactly ONE successful corpus registration'; exit 1; }; \
        echo "$out" | grep -qF '[Compute] Registered: ' || { echo 'FAIL: bare :compute did not report the registry'; exit 1; }; \
        echo "$out" | grep -F '[Compute] Registered: ' | grep -qF 'person' || { echo 'FAIL: the registry report must include the newly registered name'; exit 1; }; \
        if echo "$out" | grep -F '[Compute] Registered: ' | grep -qF 'external_probe'; then echo 'FAIL: refused unknown name leaked into the registry'; exit 1; fi; \
        echo "$out" | grep -qF '[Query] UNKNOWN (backend-unavailable)' || { echo 'FAIL: the post-retraction registration did not take — the query must route to dispatch'; exit 1; }; \
        [ "$(echo "$out" | grep -cF '[Query] UNKNOWN (backend-unavailable)')" -eq 1 ] || { echo 'FAIL: unknown/over-arity text reached dispatch instead of failing compilation'; exit 1; }; \
        echo "$out" | grep -qF 'too many arguments for "person" (arity 1)' || { echo 'FAIL: registered corpus over-arity did not fail before dispatch'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] TRUE'; then echo 'FAIL: a retracted fact answered a registered compute query'; exit 1; fi; \
        echo "$out" | grep -qF '[Session] Rebuilding and replaying' || { echo 'FAIL: the fuel trap did not trigger a session rebuild'; exit 1; }; \
        echo "$out" | grep -qF 'compute formulas are query-only' || { echo 'FAIL: registration lost across :reset + trap rebuild — the journal must retain RegisterCompute entries'; exit 1; }; \
        echo 'PASS: text registration is corpus-scoped and arity-safe; live references block it; accepted routing survives :reset + trap rebuild'

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

# Existential-import profile: import defaults OFF (clean-core). Explicit legacy ON makes
# imported witnesses participate in boolean, find, and exact-count surfaces,
# toggling a loaded KB rebuilds it immediately, and public origin metadata keeps
# an internal witness distinct from an equal-looking direct user constant.
smoke-host-existential-import: build-wasm build-host
    @echo "Smoke-testing gasnu existential-import flag (env + :existential-import toggle)..."
    @off=$(printf 'animal(every dog).\n? dog(?).\n?? dog($d).\n? dog(no dog).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$off"; \
        echo "$off" | grep -qF 'Existential import: OFF (clean-core' || { echo 'FAIL: clean-core default banner missing'; exit 1; }; \
        echo "$off" | grep -qF '[Query] FALSE' || { echo 'FAIL: clean-core must not presuppose a dog'; exit 1; }; \
        echo "$off" | grep -qF '[Find] No witnesses found.' || { echo 'FAIL: clean-core find must be empty'; exit 1; }; \
        collision=$(printf ':assert cat sk_0\n?? cat($c).\n:proof-verbose cat(some cat).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$collision"; \
        echo "$collision" | grep -qF '[Find] _ev0 = sk_0 [generated-witness], $c = sk_0 [knowledge-base]' || { echo 'FAIL: equal-looking internal/user terms lost distinct find origins'; exit 1; }; \
        echo "$collision" | grep -qF 'Exists: _v0 = sk_0 -> TRUE' || { echo 'FAIL: proof did not retain the user constant witness'; exit 1; }; \
        echo "$collision" | grep -qF 'Exists: _ev0 = sk_0 [generated-witness] -> TRUE' || { echo 'FAIL: proof did not expose generated-witness origin'; exit 1; }; \
        toggle=$(printf 'animal(every dog).\n:existential-import on\n:existential-import\n? dog(?).\n?? dog($d).\n? dog(exactly 1 dog).\n:existential-import off\n? dog(?).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$toggle"; \
        echo "$toggle" | grep -qF '[ExistentialImport] ON (imported witnesses participate in find/count)' || { echo 'FAIL: loaded-KB ON toggle did not take'; exit 1; }; \
        echo "$toggle" | grep -qF '[ExistentialImport] ON (legacy import; minted witnesses participate in ∃/∀/find/count)' || { echo 'FAIL: guest profile getter did not report ON'; exit 1; }; \
        echo "$toggle" | grep -qF '[existential-import]' || { echo 'FAIL: imported find result did not expose origin'; exit 1; }; \
        echo "$toggle" | grep -qF '[ExistentialImport] OFF (clean-core)' || { echo 'FAIL: loaded-KB OFF toggle did not take'; exit 1; }; \
        env=$(printf 'animal(every dog).\n? dog(?).\n?? dog($d).\n? dog(exactly 1 dog).\n' \
        | NIBLI_EXISTENTIAL_IMPORT=1 NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$env"; \
        echo "$env" | grep -qF 'Existential import: ON (legacy' || { echo 'FAIL: NIBLI_EXISTENTIAL_IMPORT=1 startup banner missing'; exit 1; }; \
        echo "$env" | grep -qF '[Query] TRUE' || { echo 'FAIL: explicit import must make some/exactly-one true'; exit 1; }; \
        echo "$env" | grep -qF '[existential-import]' || { echo 'FAIL: env-enabled import origin missing'; exit 1; }; \
        echo 'PASS: clean-core default + typed witness origins + coherent import algebra + retroactive toggles work end to end'

# Stratum-ordered materialisation across the WIT boundary: the `:materialize` toggle,
# the NIBLI_MATERIALIZE=0 startup opt-out, and the saturation REPORT — the last is the
# reason the WIT surface exists at all (an error message that names a remedy only a
# native embedder can reach is not a remedy). Verdicts must be IDENTICAL either way:
# materialisation changes how fast a verdict is reached, never which verdict.
smoke-host-materialize: build-wasm build-host
    @echo "Smoke-testing gasnu materialisation (report + :materialize toggle + env)..."
    @kb='person(Ara).\nall $x: person($x) & ~rotten($x) -> fit($x).\n? fit(Ara).\n'; \
        on=$(printf "$kb:materialize\n" \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$on"; \
        echo "$on" | grep -qF '[Query] TRUE' || { echo 'FAIL: nothing makes Ara rotten, so fit(Ara) must be TRUE'; exit 1; }; \
        echo "$on" | grep -qF '[Materialize] ON' || { echo 'FAIL: materialisation should default ON'; exit 1; }; \
        echo "$on" | grep -qF '[Materialize] Saturated:' || { echo 'FAIL: report did not reach the host across the WIT boundary'; exit 1; }; \
        echo "$on" | grep -qF 'rotten' || { echo 'FAIL: `rotten` is read under ~ and is pure EDB — it must appear in the report'; exit 1; }; \
        off=$(printf ":materialize off\n$kb" \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$off"; \
        echo "$off" | grep -qF '[Materialize] OFF' || { echo 'FAIL: :materialize off did not take'; exit 1; }; \
        echo "$off" | grep -qF '[Query] TRUE' || { echo 'FAIL: verdict changed with materialisation off — it must not'; exit 1; }; \
        env=$(printf "$kb" \
        | NIBLI_MATERIALIZE=0 NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm ./target/{{profile}}/nibli-host 2>&1); \
        echo "$env"; \
        echo "$env" | grep -qF 'Materialisation: OFF' || { echo 'FAIL: NIBLI_MATERIALIZE=0 startup banner missing'; exit 1; }; \
        echo "$env" | grep -qF '[Query] TRUE' || { echo 'FAIL: NIBLI_MATERIALIZE=0 changed the verdict — it must not'; exit 1; }; \
        echo 'PASS: materialisation report + toggle + env opt-out work end to end, verdicts unchanged'

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

# Run all unit tests across workspace (parallel — the old --test-threads=1
# constraint died with the thread-local dispatch/cache: both are per-KB
# instance fields now, kb.rs; integration recipes below keep theirs)
test:
    cargo test --lib -- --nocapture

# Run nibli-engine integration tests (full pipeline: parse → compile → reason)
test-engine:
    cargo test -p nibli-engine --test integration -- --nocapture --test-threads=1

# Run gasnu host unit tests (pure functions: trap classification, error/verdict
# formatting, arithmetic). gasnu is a normal bin with no lib target, so the
# workspace `test` recipe (`cargo test --lib`) skips it — this gates it in `ci`.
# WASM-independent: does not need the lasna build.
test-host:
    cargo test -p nibli-host

# Run the batch assertion validator's reporter contract. nibli is bin-only for
# this target, so the workspace `test` recipe (`cargo test --lib`) skips it.
test-validate:
    cargo test -p nibli --bin nibli-validate

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
test-all: test test-engine test-store test-backend test-validate

# CI gate for the hardened runtime surface (fast; native only — no WASM build).
# For the WASM behavioral smokes too, run `just ci-all`.
ci: fmt-check release-check clippy-runtime test test-engine test-host test-validate test-ui test-formalize test-backend test-store test-persistence-replay verify-harness verify-soundness verify-alias-map verify-nibli-kr-seam verify-dict verify-pins verify-adjudication verify-proofs verify-grammar-parity verify-doc-fences verify-book-vocab

# WASM behavioral gate (pre-push, NOT part of `ci` — needs the WASM build, like
# verify-book-capture). Bundles the gasnu smokes; each depends on
# `build-wasm build-host`, so `just` builds the component + host once, then runs
# them all: fuel exhaustion + post-trap recovery + journal replay
# (trap-recovery), plus the script transcript, persist-replay, NAF-note,
# :debug round-trip, and the determinism corpus.
ci-wasm: smoke-component-imports smoke-host-state-controls smoke-host-certify smoke-host-script smoke-host-trap-recovery smoke-host-persist-replay smoke-host-split smoke-host-count-query-only smoke-host-schema-v3-migration smoke-host-naf smoke-host-cwa-false smoke-host-debug smoke-host-collapse smoke-host-backend-unavailable smoke-host-compute-query-only smoke-host-compute-registration-order smoke-host-quiet smoke-host-strict smoke-host-existential-import smoke-host-materialize smoke-host-determinism verify-wasm-node

# Envelope smoke: `:certify` binds verdict + trace + host-tracked profile +
# the lockstep workspace version into one JSON ProofEnvelope — document on
# stdout (pipeable pure certificate), independent-validator verdict on stderr.
smoke-host-certify: build-wasm build-host
    @echo "Smoke-testing gasnu :certify (JSON proof envelope)..."
    @out=$(printf 'dog(Adam).\n:certify dog(Adam).\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm NIBLI_QUIET=1 ./target/{{profile}}/nibli-host 2>&1); \
        echo "$out" | grep -qF '"schema":2' || { echo 'FAIL: envelope JSON missing the schema stamp'; exit 1; }; \
        echo "$out" | grep -qF '"result":"True"' || { echo 'FAIL: envelope missing the bound verdict'; exit 1; }; \
        echo "$out" | grep -qF '"max_chain_depth":10' || { echo 'FAIL: envelope missing effective reasoning depth'; exit 1; }; \
        echo "$out" | grep -qF '"engine_version"' || { echo 'FAIL: envelope missing the lockstep version stamp'; exit 1; }; \
        echo "$out" | grep -qF '[Certify] envelope coherent' || { echo 'FAIL: independent validator did not confirm the envelope'; exit 1; }; \
        echo 'PASS: :certify binds verdict+trace+profile+version into a coherent JSON envelope'

# Import-surface gate: the shipped component must keep its documented import
# list — the wasi:cli + wasi:io sets, wasi:random/insecure-seed, and the
# nibli:engine compute-backend host import — and NOTHING data-bearing: no
# clock, no filesystem, no sockets, no http (the book's Ch 13/15/App C claim
# "no clock or filesystem imports"; this smoke makes that a checked property
# instead of prose). Positive controls FIRST, so an empty or failed WIT dump
# can never read as a clean import list.
smoke-component-imports: build-wasm
    @echo "Smoke-testing the component's import surface (wasm-tools component wit)..."
    @out=$(wasm-tools component wit {{wasm_dir}}/nibli.wasm 2>&1); \
        echo "$out" | grep -qF 'import wasi:cli/environment@' || { echo 'FAIL: dump missing the known wasi:cli import — the dump is broken, not the surface clean'; exit 1; }; \
        echo "$out" | grep -qF 'import wasi:io/streams@' || { echo 'FAIL: dump missing the known wasi:io import — the dump is broken, not the surface clean'; exit 1; }; \
        echo "$out" | grep -qF 'import wasi:random/insecure-seed@' || { echo 'FAIL: dump missing the known wasi:random/insecure-seed import'; exit 1; }; \
        echo "$out" | grep -qF 'import nibli:engine/compute-backend@' || { echo 'FAIL: dump missing the compute-backend host import'; exit 1; }; \
        for banned in 'wasi:clocks' 'wasi:filesystem' 'wasi:sockets' 'wasi:http'; do \
            if echo "$out" | grep -q "import $banned"; then echo "FAIL: component imports $banned — the documented no-clock/no-filesystem surface regressed"; exit 1; fi; \
        done; \
        echo 'PASS: import surface is the documented wasi:cli/wasi:io/insecure-seed + compute-backend set'

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

# Build the nibli-validate binary (batch KR assertion validation via stdin)
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
# reads dictionary-en.json, `just fetch-dict` — a book-repo dependency; the engine
# no longer reads the JSON). Runs the gate when present.
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
# validity, reserved/label integrity from the shipped map) plus a behavioral leg,
# for EVERY shipped alias: a plain alias must compile canonically EQUAL to itself
# under explicit xN labels (named = positional routing); a converted alias must
# equal its CANONICAL BASE alias under the permuted labels. ONE mode since the
# committed-corpus milestone: every build checks the full committed
# corpus (the shipped-artifact re-assertion of the const-eval validation).
verify-alias-map:
    cargo test -p nibli-verify --test alias_differential {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Regenerate/refresh the committed corpus (nibli-lexicon/src/corpus/predicates.rs)
# from a lensisku export. `fetch-dict` is the INPUT step (the JSON is lexigen's
# input only — never a build input). `regen` emits candidate NEW entries to a
# scratch file + a drift report; it never rewrites committed entries.
# One-time full seed: `cargo run -p nibli-lexigen -- bootstrap`.
regen-lexicon:
    cargo run -p nibli-lexigen {{cargo_profile_flag}} -- regen --dict dictionary-en.json

# The KR→smuni seam-conformance gate — the KR front-end's LOJBAN-FREE
# independent oracle, built to outlive THE DROP (TODO.md): hand-verified
# FOL structural goldens for the core construct classes (event decomposition,
# rule vs ∃-conjunction shapes, converted-alias/named-arg routing, standalone
# temporal/deontic wrappers plus the mixed-stack rejection matrix, flat `du`,
# prenex implication, abstraction
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
# an undercount means the corpus truncates places the word supports. ONE mode since
# the committed-corpus milestone: every build checks the gismu ∩ Predilex set (~132
# words) through the provenance bridge; lujvo lemmas are structurally unmapped.
verify-dict:
    cargo test -p nibli-verify --test predilex_differential {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Shipped-artifact parity: grammars/nibli.tmLanguage.json's keyword alternation
# must equal nibli_lexicon::RESERVED_WORDS. grammars/README.md has always said so
# in prose; nothing enforced it — no recipe, no CI job, no test referenced
# grammars/ at all. The pest twin is already pinned inside nibli-kr; this closes
# the third mirror. Also asserts the \b anchors survive (unanchored, an editor
# paints the `we` inside `wealth`) and that the order matches, so the two files
# diff side by side.
verify-grammar-parity:
    cargo test -p nibli-verify --test grammar_parity {{cargo_profile_flag}} -- --nocapture

# Doc-fence gate: every statement inside a ```nibli-kr fence must compile through
# the shipped front-end (the same NibliEngine::assert_text path as the REPL's
# `:load` and nibli-validate), one statement per line, checked as a per-fence
# knowledge base.
#
# Deliberately NOT in the `docs` CI job: that job is Nix + `mdbook build` with no
# Rust toolchain (~2 min), and the docs-job deferral protects that lightness.
# `ci` already compiles the workspace, so this rides here for free.
#
# SCOPE: mdbook/src (recursively) AND the repo-root *.md specs (flat — descending
# would reach the private book/ manuscript). The boundary is COMPILABLE EXAMPLE
# vs. METASYNTAX, carried by the info string, not tutorial vs. spec: notation
# (`pred(term, term, …)`) and NIBLI_KR §14's v2-only `pred` declarations live in
# ```text fences, because tagging either ```nibli-kr claims it compiles today.
verify-doc-fences:
    cargo test -p nibli-verify --test doc_fences {{cargo_profile_flag}} -- --nocapture

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

# KB-level behavioural pins (nibli-pin, NATIVE — no wasm, no fuel, seconds).
#
# Guards EMERGENT engine properties a knowledge base depends on but cannot state:
# chiefly the rights-floor stratification firewall, which falls out of the
# flatten_consequent / collect_ground_facts opacity asymmetry in nibli-reason. A
# pin living in a downstream prose repo would never fire on the refactor that
# breaks it, so the pins are hosted here, beside the code they constrain.
#
# Exit codes are distinct ON PURPOSE: 1 = a pinned property regressed (a real
# finding); 2 = the pin script or harness is broken (nothing was learned). CI
# must not read one as the other. The harness self-tests live in the bin
# (`cargo test -p nibli --bin nibli-pin`) and are what make the runner
# trustworthy — a pin runner that cannot fail is worse than none.
#
# Drop additional `pins/*.nibli` files in to extend coverage; each needs its own
# `:expect-pins <n>` floor. Skips cleanly when the directory is empty.
verify-pins:
    @cargo build --quiet -p nibli --bin nibli-pin
    @cargo test --quiet -p nibli --bin nibli-pin 2>/dev/null >/dev/null || \
        { echo "verify-pins: HARNESS SELF-TESTS FAILED — the runner itself is untrustworthy"; exit 2; }
    @files=$(ls pins/*.nibli 2>/dev/null); \
        if [ -z "$files" ]; then \
            echo "verify-pins: no pins/*.nibli found — skipping"; \
        else \
            ./target/debug/nibli-pin $files; \
        fi

# Adjudication-layer example gate (`examples/adjudication/`): nibli as the
# POLICY layer over an external analyzer (Souffle/CodeQL), pinned by CONTENT
# pins — the live `policy.nibli` is the fixture, loaded with `--kb`, so the
# copy cannot drift and start certifying fiction. Guards the two trust-boundary
# refusals (`derived_only` verdict, `admits` closed vocabulary), the fail-closed
# reading (an unclassified sink is NOT cleared), and the extractor's KR-injection
# escaping. A tracked, public example pinned by nothing is how examples rot.
verify-adjudication:
    @cargo build --quiet -p nibli --bin nibli-pin
    ./target/debug/nibli-pin \
        --kb examples/adjudication/policy.nibli \
        --kb examples/adjudication/facts.nibli \
        examples/adjudication/policy.pins.nibli

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
# .cargo/mutants.toml: nibli-reason reasoning/rules/kb + nibli-semantics
# semantic). Runs the full sweep, then diffs survivors against the checked-in
# baseline (mutants-baseline.txt; line:col stripped so unrelated edits don't
# shift entries): exits non-zero on any NEW survivor — a regression in test
# kill power. Baseline entries that are now KILLED print a shrink prompt.
mutants JOBS="3":
    #!/usr/bin/env bash
    set -u
    # MEMORY GUARD: a runaway mutant can balloon a test process unboundedly (a
    # bound-removing mutation; observed ~25 GB anon-rss, which made the kernel
    # OOM-killer SIGTERM the whole sweep under WSL's ~46 GB cap). Cap each
    # process's virtual address space so the balloon dies ALONE — cargo-mutants
    # counts the killed test as CAUGHT (like a timeout: the tests noticed).
    # 12 GiB clears the normal build+test peaks with wide margin (acceptance-
    # tested: heaviest-crate rebuild + the full per-mutant test set both pass
    # under it). JOBS defaults to 3 so even JOBS simultaneous balloons stay
    # within the WSL cap (3 × 12 GiB = 36 GiB); raise it on hosts with more RAM.
    ulimit -v 12582912
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

# Timing pins for the book's quoted figures (Ch 13 latency numbers, Ch 19 full
# GDPR sequence): release-profile, native in-process engine, gdpr.nibli corpus,
# min/median/max over NIBLI_BENCH_RUNS runs (default 10) with verdicts asserted.
# The source for any latency figure the book quotes — never hand-write timings.
bench-book:
    cargo run --release -p nibli --features bench-bins --bin nibli-bench-book

# Timing for negation-as-failure evaluation: release-profile, native in-process
# engine, utopia.nibli corpus (the worst NAF shape the shipped corpora contain —
# `false/1` is concluded by a 3-variable/15-conjunct rule and read under `~`),
# min/median/max over NIBLI_BENCH_RUNS runs (default 5) with verdicts asserted.
# The `lookup` leg is the same-KB control. The source for any NAF latency figure.
bench-naf:
    cargo run --release -p nibli --features bench-bins --bin nibli-bench-naf

# Timing for RECURSIVE rule evaluation — the transitive-closure cost cliff, and
# its non-recursive echo. Release-profile native bench, self-generating KBs (no
# corpus dependency). Three families: FORWARD `earlier(N0,Nn)` TRUE (definitive,
# so never materialised — the backward-chaining cost, growing ~3-4x per two
# edges); BACKWARD `earlier(Nn,N0)` FALSE on the SAME KB (non-definitive, so the
# cone IS saturated — the same rule the fast way); and the ADJUDICATION legs,
# where a purely positive clearance query and its `~`-read finding twin differ
# ~190x on the same question with no recursion involved. The source for any
# recursion-cost figure — never hand-write these. `NIBLI_BENCH_CLOSURE_FWD` /
# `..._BWD` (comma lists) resize the chains; the forward default stops at n=10
# because n=12 costs ~18 s and n=15 does not finish in a minute.
bench-closure:
    cargo run --release -p nibli --features bench-bins --bin nibli-bench-closure

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
    p=$(cargo test -p nibli --bins -- --list 2>/dev/null | grep -c ': test$'); \
    echo "unit (workspace --lib):      $u"; \
    echo "nibli-engine test targets:   $e"; \
    echo "gasnu bin tests:             $g"; \
    echo "nibli-verify test targets:   $v"; \
    echo "nibli bin tests (nibli-pin): $p"; \
    echo "total: $((u + e + g + v + p))  (a few lib tests appear in both the unit and per-crate figures)"

# Auth core tests (nibli-auth: policy load, can, allowed_fields, explain, tls)
test-auth:
    cargo test -p nibli-auth
    cargo test -p nibli-auth --features axum,async-graphql,juniper

# Check the axum auth example compiles
check-auth-axum:
    cargo check -p auth-axum

# Run the axum auth demo (http://127.0.0.1:3001)
run-auth-axum:
    cargo run -p auth-axum

# Repo-local venv for maturin / FastAPI demos (gitignored via .venv)
_auth_venv := ".venv-auth"

# Create .venv-auth if missing
auth-py-venv:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -d {{_auth_venv}} ]; then
      python3 -m venv {{_auth_venv}}
      {{_auth_venv}}/bin/pip install -U pip
    fi

# Build Python nibli_auth_native (PyO3) into .venv-auth
build-auth-py: auth-py-venv
    #!/usr/bin/env bash
    set -euo pipefail
    source {{_auth_venv}}/bin/activate
    cd nibli-auth-py && maturin develop --release

# Python auth unit tests (requires build-auth-py)
test-auth-py: build-auth-py
    #!/usr/bin/env bash
    set -euo pipefail
    source {{_auth_venv}}/bin/activate
    PYTHONPATH=python python3 -m unittest discover -s python/nibli_auth/tests -v

# FastAPI auth demo (http://127.0.0.1:3002)
run-auth-fastapi: build-auth-py
    #!/usr/bin/env bash
    set -euo pipefail
    source {{_auth_venv}}/bin/activate
    pip install -q -r examples/auth-fastapi/requirements.txt
    PYTHONPATH=python python3 -m uvicorn main:app --app-dir examples/auth-fastapi --host 127.0.0.1 --port 3002

# Build the code-derived docs site (mdBook → mdbook/book/). Source is mdbook/;
# never import the private manuscript at book/.
# Default site-url is book.toml (/docs/nibli/). Override for GitHub Pages:
#   just docs /nibli/
docs site_url="":
    #!/usr/bin/env bash
    set -euo pipefail
    if [ -n "{{site_url}}" ]; then
      export MDBOOK_OUTPUT__HTML__SITE_URL="{{site_url}}"
    fi
    # Regenerate the gitignored mermaid JS assets (idempotent; book.toml is
    # already configured, so this only drops mermaid.min.js + mermaid-init.js).
    mdbook-mermaid install mdbook
    mdbook build mdbook

# Same as `just docs /nibli/` (GitHub Pages project base path)
docs-pages-build:
    just docs /nibli/

# Serve docs locally (http://127.0.0.1:3000) — default primary site-url
docs-serve:
    mdbook-mermaid install mdbook
    mdbook serve mdbook -p 3000 -n 127.0.0.1

# Release-track consistency gate (R0; decisions of record in RELEASING.md): lockstep versions across the
# workspace, publish flags matching the Tier A/Z decision table, and required
# crates.io metadata (description/license/repository) on every publishable
# crate. Native + offline; run before any tag or publish.
release-check:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo metadata --format-version 1 --no-deps | python3 -c '
    import json, sys, tomllib
    md = json.load(sys.stdin)
    # publish = false expected: Tier Z (RELEASING.md decision table) + the auth crates
    # (in neither tier row) + the example bin.
    NO_PUBLISH = {"nibli-pipeline", "nibli-host", "nibli-ui", "nibli-wasm",
                  "nibli-verify", "nibli-lexigen", "nibli-auth", "nibli-auth-py",
                  "auth-axum", "lucy-core"}
    errors = []
    versions = {}
    for p in md["packages"]:
        versions[p["name"]] = p["version"]
        publishable = p["publish"] is None  # metadata: None = anywhere, [] = publish=false
        if p["name"] in NO_PUBLISH:
            if publishable:
                errors.append(p["name"] + ": expected publish = false")
        else:
            if not publishable:
                errors.append(p["name"] + ": Tier A crate unexpectedly publish = false")
            for k in ("description", "license", "repository"):
                if not p.get(k):
                    errors.append(p["name"] + ": missing " + k + " (crates.io requires it)")
            # A versionless NORMAL/BUILD path dep is rejected by cargo publish
            # (a member that quietly drops `workspace = true` regresses to
            # this). Dev-deps are exempt: cargo STRIPS versionless path
            # dev-deps at publish — internal dev-deps are path-only on
            # purpose so they impose no publish-order constraint.
            for d in p.get("dependencies", []):
                if d.get("path") and d.get("kind") != "dev" and d.get("req") == "*":
                    errors.append(p["name"] + ": path dep " + d["name"] + " has no version (cargo publish rejects it)")
    if len(set(versions.values())) != 1:
        errors.append("version lockstep broken: " + repr(sorted(set(versions.values()))))
    else:
        lock = next(iter(versions.values()))
        with open("Cargo.toml", "rb") as f:
            root = tomllib.load(f)
        wsp = root.get("workspace", {}).get("package", {}).get("version")
        if wsp != lock:
            errors.append("[workspace.package] version " + repr(wsp) + " != member lockstep " + repr(lock))
        for name, spec in root.get("workspace", {}).get("dependencies", {}).items():
            v = spec.get("version") if isinstance(spec, dict) else None
            if v != lock:
                errors.append("[workspace.dependencies] " + name + " version " + repr(v) + " != lockstep " + repr(lock))
    # `cargo metadata` reports only the RESOLVED version, so a member that
    # replaces `version.workspace = true` with a literal passes the lockstep
    # legs above and then silently fails to move at the NEXT bump — surfacing
    # one release later as a mystery mismatch. Only reading the manifests
    # closes it.
    import os
    for p in md["packages"]:
        mf = p["manifest_path"]
        with open(mf, "rb") as f:
            pkg = tomllib.load(f).get("package", {})
        if pkg.get("version") != {"workspace": True}:
            errors.append(p["name"] + ": [package].version must be `version.workspace = true` (found " + repr(pkg.get("version")) + ")")
    # Two version literals live OUTSIDE the lockstep by design and are
    # invisible to cargo metadata. Assert both, or the only thing keeping them
    # right is that someone remembers.
    with open("nibli-auth-py/pyproject.toml", "rb") as f:
        proj = tomllib.load(f).get("project", {})
    if "version" not in proj.get("dynamic", []):
        errors.append("nibli-auth-py/pyproject.toml: [project] must keep `dynamic = [\"version\"]` so the maturin wheel rides the lockstep")
    with open("fuzz/Cargo.toml", "rb") as f:
        fz = tomllib.load(f).get("package", {})
    if fz.get("version") != "0.0.0":
        errors.append("fuzz/Cargo.toml: workspace-excluded, must stay pinned at 0.0.0 (found " + repr(fz.get("version")) + ")")
    # The bench bins include_str! repo-root corpora that no package tarball can
    # carry — a default-on `bench-bins` would break `cargo publish` (see the
    # comment block in nibli/Cargo.toml).
    with open("nibli/Cargo.toml", "rb") as f:
        nb = tomllib.load(f)
    if "bench-bins" in nb.get("features", {}).get("default", []):
        errors.append("nibli: `bench-bins` must NOT be a default feature (its bins include_str! repo-root corpora; cargo publish would fail)")
    if errors:
        print("release-check FAILED:")
        for e in errors:
            print("  - " + e)
        sys.exit(1)
    print("release-check PASS: " + str(len(md["packages"])) + " members at lockstep " + next(iter(versions.values())))
    '

# ── Release automation (R3) ────────────────────────────────────────────────
# `release-check` above is the VERSION-AGNOSTIC structural gate and rides
# `just ci`. Everything below is VERSION-SPECIFIC and must never join `ci` —
# its answer is deliberately "false" on an ordinary main commit.
# The operator runbook (incl. yank/hotfix policy) is RELEASING.md.

# The release-moment gate: this tree IS exactly VERSION and is releasable.
# Cheap (no compile, offline) so the release workflow's preflight can run it
# before any toolchain spins up. Composes release-check for the structural half.
release-verify VERSION: release-check
    #!/usr/bin/env bash
    set -euo pipefail
    V="{{VERSION}}" python3 -c '
    import os, re, sys, tomllib, subprocess
    V = os.environ["V"]
    errors = []
    if not re.fullmatch(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-[0-9A-Za-z.-]+)?", V):
        if V.startswith("v"):
            print("release-verify FAILED: pass " + V[1:] + ", not " + V + " — the tag carries the v, the manifest does not")
        else:
            print("release-verify FAILED: " + repr(V) + " is not a semver version")
        sys.exit(1)
    with open("Cargo.toml", "rb") as f:
        root = tomllib.load(f)
    wsv = root["workspace"]["package"]["version"]
    if wsv != V:
        errors.append("[workspace.package] version is " + repr(wsv) + ", expected " + repr(V))
    # ── CHANGELOG ──
    text = open("CHANGELOG.md", encoding="utf-8").read()
    lines = text.splitlines()
    heads = []  # (index, version-or-None, raw)
    fence = False
    for i, ln in enumerate(lines):
        if ln.lstrip().startswith("```"):
            fence = not fence
            continue
        if fence:
            continue
        m = re.match(r"^## \[([^\]]+)\]\s*(?:-\s*(\S+))?\s*$", ln)
        if m:
            heads.append((i, m.group(1), m.group(2)))
    names = [h[1] for h in heads]
    if V not in names:
        errors.append("CHANGELOG.md has no `## [" + V + "]` section (did you run `just release-prep " + V + "`?)")
    else:
        idx = names.index(V)
        if names[0] != "Unreleased":
            errors.append("CHANGELOG.md: first section must be `## [Unreleased]`, found " + repr(names[0]))
        elif idx != 1:
            errors.append("CHANGELOG.md: `## [" + V + "]` must be the first section after [Unreleased], found at position " + str(idx))
        date = heads[idx][2]
        if not date or not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
            errors.append("CHANGELOG.md: `## [" + V + "]` needs a YYYY-MM-DD date, found " + repr(date))
        start = heads[idx][0] + 1
        end = heads[idx + 1][0] if idx + 1 < len(heads) else len(lines)
        body = "\n".join(lines[start:end]).strip()
        if not body or body == "Nothing yet.":
            errors.append("CHANGELOG.md: `## [" + V + "]` section is empty — a release with no documented changes violates the CHANGELOG-required decision")
    # Link refs. The [Unreleased] compare must point at the NEW tag — the line
    # everyone forgets on release 2 (and after a hotfix merge-back).
    if not re.search(r"^\[" + re.escape(V) + r"\]:\s*\S*/releases/tag/v" + re.escape(V) + r"\s*$", text, re.M):
        errors.append("CHANGELOG.md: missing link ref `[" + V + "]: .../releases/tag/v" + V + "`")
    if not re.search(r"^\[Unreleased\]:\s*\S*/compare/v" + re.escape(V) + r"\.\.\.HEAD\s*$", text, re.M):
        errors.append("CHANGELOG.md: `[Unreleased]:` must compare from v" + V + "...HEAD")
    # ── Cargo.lock ── (precise message; the --locked run below is authoritative)
    with open("Cargo.lock", "rb") as f:
        lock = tomllib.load(f)
    members = {p["name"] for p in __import__("json").loads(
        subprocess.run(["cargo", "metadata", "--format-version", "1", "--no-deps"],
                       capture_output=True, text=True, check=True).stdout)["packages"]}
    for p in lock.get("package", []):
        if p["name"] in members and p.get("version") != V:
            errors.append("Cargo.lock: " + p["name"] + " at " + repr(p.get("version")) + ", expected " + V + " — run `cargo update --workspace`")
    # ── the tag, ONLY on a real tag ref ──
    # Gate on GITHUB_REF_TYPE, never on GITHUB_REF_NAME being non-empty: that
    # is "main" on a branch push and would fail every CI run.
    if os.environ.get("GITHUB_REF_TYPE") == "tag":
        tag = os.environ.get("GITHUB_REF_NAME", "")
        if tag != "v" + V:
            errors.append("tag is " + repr(tag) + " but the workspace is at " + V)
    if errors:
        print("release-verify FAILED:")
        for e in errors:
            print("  - " + e)
        sys.exit(1)
    '
    # Authoritative lock check: fails if the lock would change AT ALL.
    cargo metadata --locked --format-version 1 --no-deps >/dev/null
    echo "release-verify PASS: tree is {{VERSION}}, CHANGELOG rolled, lock in sync"

# GitHub Release body for VERSION, to stdout. A recipe (not inline workflow
# YAML) so it is locally testable and so the asset table stays in lockstep with
# release-dist/release-wasm's naming. Never interpolate the result into a shell
# string — the workflow writes it to a file and passes --notes-file.
release-notes VERSION:
    #!/usr/bin/env bash
    set -euo pipefail
    V="{{VERSION}}" python3 -c '
    import os, re, sys
    V = os.environ["V"]
    lines = open("CHANGELOG.md", encoding="utf-8").read().splitlines()
    start = end = None
    fence = False
    for i, ln in enumerate(lines):
        if ln.lstrip().startswith("```"):
            fence = not fence
            continue
        if fence:
            continue
        if re.match(r"^## \[" + re.escape(V) + r"\]\s*(?:-.*)?$", ln):
            start = i + 1
        elif start is not None and ln.startswith("## "):
            end = i
            break
    if start is None:
        sys.exit("release-notes: CHANGELOG.md has no `## [" + V + "]` section")
    body = lines[start:end if end is not None else len(lines)]
    # Drop the trailing link-reference block.
    while body and (not body[-1].strip() or re.match(r"^\[.+\]:", body[-1])):
        body.pop()
    body = "\n".join(body).strip()
    if not body:
        sys.exit("release-notes: `## [" + V + "]` section is empty")
    print(body)
    print()
    print("## Assets")
    print()
    print("| File | What |")
    print("|------|------|")
    for slug, human in (("x86_64-linux", "Linux x86-64"), ("aarch64-linux", "Linux ARM64"), ("aarch64-darwin", "macOS Apple silicon")):
        print("| `nibli-" + V + "-" + slug + ".tar.gz` | " + human + " binaries: `nibli-host`, `nibli`, `nibli-validate`, `nibli-pin` |")
    print("| `nibli-pipeline-" + V + ".wasm` | The WASI P2 engine component (architecture-independent) |")
    print("| `SHA256SUMS` | Checksums for every asset above |")
    print()
    print("`nibli-host` loads the component: `NIBLI_WASM_PATH=./nibli-pipeline-" + V + ".wasm ./nibli-host`")
    print()
    print("The macOS archive is unsigned — after a browser download, clear the quarantine flag:")
    print("`xattr -dr com.apple.quarantine ./nibli-host`")
    print()
    print("Libraries are on crates.io at " + V + " (`cargo add nibli-engine`); API docs on docs.rs.")
    print()
    print("Full changelog: https://github.com/dhilipsiva/nibli/blob/v" + V + "/CHANGELOG.md")
    print()
    print("Docs: https://dhilipsiva.github.io/nibli/ · Playground: https://dhilipsiva.dev/nibli-playground/")
    '

# Release-profile binaries for the CURRENT platform.
# NEVER --workspace: that links the cdylib/component crates and the WIT `@`
# export symbols break the linker (see .cargo/mutants.toml). NEVER
# --features bench-bins: those bins include_str! repo-root corpora.
release-bins:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo build --release --locked -p nibli-host -p nibli
    for b in nibli-host nibli nibli-validate nibli-pin; do
      if [ ! -x "target/release/$b" ]; then
        echo "release-bins FAILED: target/release/$b missing (renamed [[bin]]?)" >&2
        exit 1
      fi
    done
    echo "release-bins PASS: 4 binaries in target/release/"

# Package this platform's binaries as dist/nibli-VERSION-SLUG.tar.gz.
# Tarred HERE, inside the matrix job, because actions/upload-artifact does not
# preserve the executable bit — a raw binary would arrive mode 0644 and ship
# un-runnable.
release-dist VERSION SLUG: release-bins
    #!/usr/bin/env bash
    set -euo pipefail
    stage="target/release-stage/nibli-{{VERSION}}-{{SLUG}}"
    rm -rf "$stage" && mkdir -p "$stage" dist
    for b in nibli-host nibli nibli-validate nibli-pin; do cp "target/release/$b" "$stage/"; done
    cp README.md LICENSE-MIT LICENSE-APACHE "$stage/"
    tar czf "dist/nibli-{{VERSION}}-{{SLUG}}.tar.gz" -C "target/release-stage" "nibli-{{VERSION}}-{{SLUG}}"
    echo "release-dist PASS: dist/nibli-{{VERSION}}-{{SLUG}}.tar.gz"

# The WASI component, release profile, renamed for release.
# Needs cargo-component → runs in the DEFAULT devshell, not `.#release`.
# The lib target is named `nibli` (nibli-pipeline/Cargo.toml `[lib] name`), so
# the artifact on disk is nibli.wasm; the rename lives here, not in YAML.
release-wasm VERSION:
    #!/usr/bin/env bash
    set -euo pipefail
    just profile=release build-wasm
    mkdir -p dist
    cp "target/wasm32-wasip2/release/nibli.wasm" "dist/nibli-pipeline-{{VERSION}}.wasm"
    echo "release-wasm PASS: dist/nibli-pipeline-{{VERSION}}.wasm"

# Publish the Tier A crates to crates.io. SAFE TO RE-RUN — that is the whole
# design. `cargo publish --workspace` hard-errors on an already-published
# version (verify_unpublished bails before uploading anything), so a resume
# passes --exclude for each crate already live. Excluding is far better than a
# hand-rolled per-crate loop: it keeps cargo's own dependency ordering and
# index-propagation waits instead of re-implementing them.
# Pass any non-empty second arg for a rehearsal (--dry-run needs no token).
# A DRY RUN DELIBERATELY SKIPS THE PREFLIGHT and always runs cargo, so it
# verify-BUILDS all 13 tarballs. Taking the early "all already live" exit
# instead would make the rehearsal prove nothing about packaging — and at the
# current release every crate IS already live, which is exactly when you most
# want the rehearsal to mean something. cargo downgrades already-published from
# an error to a warning under --dry-run, so no --exclude is needed here.
release-publish VERSION DRY_RUN="":
    #!/usr/bin/env bash
    set -euo pipefail
    just release-verify {{VERSION}}
    if [ "{{DRY_RUN}}" != "" ]; then
      echo "release-publish: REHEARSAL — packaging + verify-building every Tier A crate."
      echo "  (expect one 'already exists' warning per crate already on crates.io)"
      cargo publish --workspace --locked --dry-run
      echo "release-publish PASS (dry run): all tarballs package and build"
      exit 0
    fi
    attempt=1
    while :; do
      # Partition against the SPARSE INDEX (the same source cargo's own
      # verify_unpublished consults) — never against cargo's error text.
      # Recomputed every attempt so a retry after a partial upload sees it.
      mapfile -t already < <(V="{{VERSION}}" python3 -c '
    import json, os, subprocess, sys, urllib.request
    V = os.environ["V"]
    md = json.loads(subprocess.run(["cargo","metadata","--format-version","1","--no-deps"],
                                   capture_output=True, text=True, check=True).stdout)
    # Derive Tier A from the manifests; never hardcode the list.
    names = sorted(p["name"] for p in md["packages"] if p["publish"] is None)
    print("::TIERA::" + str(len(names)), file=sys.stderr)
    for n in names:
        p = ("1/" if len(n) == 1 else "2/" if len(n) == 2 else "3/" + n[0] + "/" if len(n) == 3
             else n[:2] + "/" + n[2:4] + "/")
        url = "https://index.crates.io/" + p + n
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "nibli-release (github.com/dhilipsiva/nibli)"})
            raw = urllib.request.urlopen(req, timeout=30).read().decode()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                print("::NEW::" + n, file=sys.stderr)   # never published at ANY version
                continue
            raise
        if any(json.loads(l)["vers"] == V for l in raw.splitlines() if l.strip()):
            print(n)
    ' 2>>/tmp/nibli-publish-probe.log )
      total=$(grep -o '::TIERA::[0-9]*' /tmp/nibli-publish-probe.log | tail -1 | cut -d: -f5)
      if grep -q '::NEW::' /tmp/nibli-publish-probe.log; then
        echo "warning: these crates have never been published — the crates.io NEW-CRATE rate limit (burst 5, then ~1/10min) applies; publish them manually once first:" >&2
        grep -o '::NEW::.*' /tmp/nibli-publish-probe.log | sed 's/::NEW::/  - /' >&2
      fi
      echo "release-publish: ${#already[@]}/${total:-?} crates already live at {{VERSION}}"
      if [ "${#already[@]}" -eq "${total:-0}" ] && [ "${total:-0}" -gt 0 ]; then
        echo "release-publish: nothing to publish — all ${total} Tier A crates are already at {{VERSION}}"
        exit 0
      fi
      excludes=()
      for c in "${already[@]}"; do excludes+=(--exclude "$c"); done
      if [ "${#already[@]}" -gt 0 ]; then
        echo "release-publish: resuming, excluding ${#already[@]} already-published crate(s)"
      fi
      if cargo publish --workspace --locked ${excludes[@]+"${excludes[@]}"}; then
        echo "release-publish PASS"
        exit 0
      fi
      if [ "$attempt" -ge 3 ]; then
        echo "release-publish FAILED after $attempt attempts. Already-live crates are permanent." >&2
        echo "Re-run \`just release-publish {{VERSION}}\` — it skips what landed. See RELEASING.md §Partial-publish recovery." >&2
        exit 1
      fi
      # cargo waits only 60s per dependency wave for index confirmation and the
      # timeout is unstable-gated, so a slow index is the realistic failure.
      # Sleep past the sparse-index CDN TTL before re-probing.
      echo "release-publish: attempt $attempt failed; re-probing in 90s" >&2
      sleep 90
      attempt=$((attempt + 1))
    done

# Roll the tree to VERSION: bump the workspace version, move the CHANGELOG's
# [Unreleased] into a dated section, refresh the lock. Does NOT commit or tag —
# you review the diff. Refuses rather than pretending to be idempotent; the
# undo is `git checkout -- Cargo.toml Cargo.lock CHANGELOG.md`.
release-prep VERSION DATE="": release-check
    #!/usr/bin/env bash
    set -euo pipefail
    V="{{VERSION}}" D="{{DATE}}" python3 -c '
    import os, re, subprocess, sys, tomllib
    from datetime import datetime, timezone
    V = os.environ["V"]
    D = os.environ["D"] or datetime.now(timezone.utc).strftime("%Y-%m-%d")
    def die(msg, hint=None):
        print("release-prep REFUSED: " + msg)
        if hint: print("  " + hint)
        sys.exit(1)
    if V.startswith("v"):
        die("pass " + V[1:] + ", not " + V, "the tag carries the v, the manifest does not")
    if not re.fullmatch(r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)", V):
        die(repr(V) + " is not a plain X.Y.Z version",
            "pre-release versions have no CHANGELOG/tag precedent here — cut them by hand")
    with open("Cargo.toml", "rb") as f:
        root = tomllib.load(f)
    old = root["workspace"]["package"]["version"]
    if old == V:
        die("already at " + V + " — nothing to prep")
    if tuple(int(x) for x in V.split(".")) <= tuple(int(x) for x in old.split(".")):
        die("refusing to go from " + old + " down to " + V)
    def git(*a):
        return subprocess.run(["git", *a], capture_output=True, text=True).stdout.strip()
    if subprocess.run(["git","diff","--quiet"]).returncode or subprocess.run(["git","diff","--cached","--quiet"]).returncode:
        die("working tree is dirty", "the point of this recipe is that you review its diff — commit or stash first")
    if git("tag","-l","v"+V):
        die("tag v" + V + " already exists locally")
    remote = subprocess.run(["git","ls-remote","--tags","origin","refs/tags/v"+V], capture_output=True, text=True)
    if remote.returncode == 0 and remote.stdout.strip():
        die("tag v" + V + " already exists on origin", "that release is public — bump the patch instead")
    elif remote.returncode != 0:
        print("release-prep: NOTE — could not reach origin to check for tag v" + V + " (offline?)")
    branch = git("branch","--show-current")
    if branch != "main":
        print("release-prep: NOTE — on branch " + repr(branch) + ", not main.")
        print("  Expected for a hotfix (RELEASING.md §Hotfix); otherwise check you meant this.")
    # ── CHANGELOG parse ──
    text = open("CHANGELOG.md", encoding="utf-8").read()
    lines = text.splitlines()
    heads, fence = [], False
    for i, ln in enumerate(lines):
        if ln.lstrip().startswith("```"):
            fence = not fence
            continue
        if fence: continue
        m = re.match(r"^## \[([^\]]+)\]", ln)
        if m: heads.append((i, m.group(1)))
    names = [h[1] for h in heads]
    if V in names:
        die("CHANGELOG.md already has a `## [" + V + "]` section",
            "undo a half-finished prep with: git checkout -- Cargo.toml Cargo.lock CHANGELOG.md")
    if not names or names[0] != "Unreleased":
        die("CHANGELOG.md must start with `## [Unreleased]`")
    u_start = heads[0][0] + 1
    u_end = heads[1][0] if len(heads) > 1 else len(lines)
    body = "\n".join(lines[u_start:u_end]).strip()
    if not body or body == "Nothing yet.":
        if os.environ.get("NIBLI_RELEASE_ALLOW_EMPTY") != "1":
            die("[Unreleased] is empty — a release with no documented changes violates the CHANGELOG-required decision",
                "write the entries first, or set NIBLI_RELEASE_ALLOW_EMPTY=1")
        body = "Maintenance release; no user-facing changes."
    # ── Cargo.toml: SECTION-SCOPED line edits ──
    # Not a tomllib round-trip: tomllib is parse-only, and any writer would
    # discard the root manifest comment blocks that encode locked decisions.
    dep_names = {k for k, v in root["workspace"].get("dependencies", {}).items()
                 if isinstance(v, dict) and "version" in v}
    expected = 1 + len(dep_names)          # derived, never hardcoded
    out, section, edits = [], None, 0
    for ln in open("Cargo.toml", encoding="utf-8").read().splitlines(keepends=True):
        h = re.match(r"^\[([^\]]+)\]", ln)
        if h: section = h.group(1)
        if section == "workspace.package" and re.match(r"^version\s*=\s*\"" + re.escape(old) + r"\"\s*$", ln.strip()):
            ln = ln.replace("\"" + old + "\"", "\"" + V + "\"", 1); edits += 1
        elif section == "workspace.dependencies" and ln.split("=")[0].strip() in dep_names:
            new_ln = re.sub(r"(version\s*=\s*)\"" + re.escape(old) + r"\"", r"\1\"" + V + "\"", ln, count=1)
            if new_ln != ln: ln = new_ln; edits += 1
        out.append(ln)
    if edits != expected:
        die("expected " + str(expected) + " version edits in Cargo.toml, made " + str(edits) + " — aborting before write")
    open("Cargo.toml", "w", encoding="utf-8").writelines(out)
    with open("Cargo.toml", "rb") as f:
        chk = tomllib.load(f)
    bad = [k for k, v in chk["workspace"].get("dependencies", {}).items()
           if isinstance(v, dict) and "version" in v and v["version"] != V]
    if chk["workspace"]["package"]["version"] != V or bad:
        die("post-write reparse disagrees (workspace.package or " + repr(bad) + ") — restore with git checkout")
    # ── CHANGELOG roll ──
    new = lines[:u_start] + ["", "Nothing yet.", "", "## [" + V + "] - " + D, ""] + body.splitlines() + [""] + lines[u_end:]
    text = "\n".join(new) + "\n"
    text = re.sub(r"^\[Unreleased\]:\s*(\S*)/compare/\S+\.\.\.HEAD\s*$",
                  lambda m: "[Unreleased]: " + m.group(1) + "/compare/v" + V + "...HEAD\n[" + V + "]: " + m.group(1) + "/releases/tag/v" + V,
                  text, count=1, flags=re.M)
    open("CHANGELOG.md", "w", encoding="utf-8").write(text)
    print("release-prep: " + old + " -> " + V + " (" + D + "); " + str(edits) + " manifest edits")
    '
    # Refresh the lock. --workspace is REQUIRED: a bare `cargo update`
    # re-resolves every third-party dep and turns a version bump into an
    # unreviewable diff. Never "fix" a failure here by dropping the flag.
    cargo update --workspace --offline || cargo update --workspace
    just release-verify {{VERSION}}
    echo ""
    echo "Nothing has been committed or tagged. Review, then:"
    echo "  git diff"
    echo "  just ci-all"
    echo "  git commit -am 'release(v{{VERSION}}): <summary>'"
    echo "  git push origin main          # let CI go green BEFORE tagging"
    echo "  git tag -a v{{VERSION}} -m 'v{{VERSION}}' && git push origin v{{VERSION}}"
    echo ""
    echo "The tag push runs .github/workflows/release.yml: gates -> artifacts ->"
    echo "draft Release -> crates.io -> publish. See RELEASING.md."
    echo "Undo this prep with: git checkout -- Cargo.toml Cargo.lock CHANGELOG.md"

# Wipes all compilation artifacts
clean:
    cargo clean

# Transaction/recovery controls use the real built component, including fault
# injection at the host/store boundary and two-process retained-record replay.
smoke-host-state-controls: build-wasm build-host
    NIBLI_WASM_PATH={{wasm_dir}}/nibli.wasm cargo test -p nibli-host recovery_tests -- --ignored --test-threads=1
    python3 nibli-host/tests/smoke_state_controls.py target/{{profile}}/nibli-host {{wasm_dir}}/nibli.wasm
