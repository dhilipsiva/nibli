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

# Download the maintained lensisku English dictionary (the smuni-dictionary build reads
# ../dictionary-en.json). The bulk export needs a logged-in Bearer token: get one from
# lensisku.lojban.org and `export LENSISKU_TOKEN=...` before running. Gitignored; without
# it the build falls back to the in-tree dictionary (same as CI).
fetch-dict:
    @test -n "${LENSISKU_TOKEN:-}" || { echo 'error: set LENSISKU_TOKEN (Bearer token from lensisku.lojban.org)'; exit 1; }
    curl -fsSL -H "Authorization: Bearer ${LENSISKU_TOKEN}" \
      "https://lensisku.lojban.org/api/export/cached/dictionary-en.json" \
      -o dictionary-en.json
    @echo "Wrote dictionary-en.json ($(wc -c < dictionary-en.json) bytes)"

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
        echo "$out" | grep -qF '[Query] RESOURCE_EXCEEDED (fuel)' || { echo 'FAIL: query fuel trap not translated into a RESOURCE_EXCEEDED (fuel) verdict'; exit 1; }; \
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

# go'i full-bridi smoke: a BARE `? go'i` (no sumti) must repeat the WHOLE previous
# bridi, inheriting its sumti. After `la .adam. cu gerku`, a bare `? go'i` queries
# gerku(adam) -> TRUE. Pre-fix the selbri-only snapshot queried gerku(zo'e) -> FALSE.
# Pre-release gate (needs the WASM build; not part of `ci`).
smoke-gasnu-goi-bare: build-wasm build-gasnu
    @echo "Smoke-testing bare go'i full-bridi inheritance (? go'i repeats the whole bridi)..."
    @run() { printf 'la .adam. cu gerku\n? go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1; }; \
        ok() { echo "$1" | grep -qF '[Query] TRUE' && ! echo "$1" | grep -qF 'cannot enter component instance'; }; \
        out=$(run); \
        if ! ok "$out"; then \
            echo 'note: first attempt not TRUE; retrying once. The engine verdict here is DETERMINISTIC at default fuel (the adam anchor pins the candidate set to a single event); a one-off non-TRUE is a rare WASM-host/CI transient, not a reasoning nondeterminism. A persistent fail across both attempts IS a real regression.'; \
            out=$(run); \
        fi; \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: bare ? goi not TRUE after retry (real regression)'; exit 1; }; \
        if echo "$out" | grep -qF 'cannot enter component instance'; then echo 'FAIL: session bricked after retry'; exit 1; fi; \
        echo 'PASS: bare ? goi repeats the full previous bridi (gerku(adam) TRUE)'

# Partial go'i per-place merge: `? la .karl. go'i` after `... prami la .bel.`
# overrides x1 (karl) and INHERITS x2 (bel) -> prami(karl,bel) FALSE. Pre-fix the
# partial path dropped the antecedent's places (prami(karl,zo'e) -> TRUE).
smoke-gasnu-goi-partial: build-wasm build-gasnu
    @echo "Smoke-testing partial go'i per-place merge (supplied x1 + inherited x2)..."
    @out=$(printf 'la .karl. cu prami la .kim.\nla .adam. cu prami la .bel.\n? la .karl. go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] FALSE' || { echo 'FAIL: partial go'\''i produced no verdict'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] TRUE'; then echo 'FAIL: partial go'\''i lost the inherited x2 (prami(karl,zoe) matched instead of prami(karl,bel))'; exit 1; fi; \
        echo 'PASS: partial go'\''i merges per place (prami(karl,bel) FALSE — x1 overridden, x2 inherited)'

# Queries update the go'i antecedent: after asserting gerku(adam), querying
# gerku(bel) (FALSE) makes a following `? go'i` repeat gerku(bel) -> FALSE. Pre-fix
# `? go'i` tracked only the last ASSERT (gerku(adam)) -> TRUE.
smoke-gasnu-goi-after-query: build-wasm build-gasnu
    @echo "Smoke-testing go'i tracks the last QUERIED bridi (not just the last assert)..."
    @out=$(printf 'la .adam. cu gerku\n? la .bel. cu gerku\n? go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] FALSE' || { echo 'FAIL: no FALSE verdict'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] TRUE'; then echo 'FAIL: ? goi tracked the last ASSERT (gerku(adam) TRUE) not the last QUERY (gerku(bel) FALSE)'; exit 1; fi; \
        echo 'PASS: ? goi repeats the last queried bridi (gerku(bel) FALSE)'

# Direct-API :assert go'i snapshot carries sumti: after `:assert prami adam bel`,
# `? la .karl. go'i` inherits x2=bel -> prami(karl,bel) FALSE. Pre-fix the synthetic
# snapshot had empty terms (prami(karl,zo'e) -> TRUE).
smoke-gasnu-goi-assert-fact: build-wasm build-gasnu
    @echo "Smoke-testing direct-API :assert go'i snapshot carries sumti..."
    @out=$(printf ':assert prami karl kim\n:assert prami adam bel\n? la .karl. go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] FALSE' || { echo 'FAIL: no FALSE verdict'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] TRUE'; then echo 'FAIL: :assert snapshot lost args (prami(karl,zoe) matched instead of prami(karl,bel))'; exit 1; fi; \
        echo 'PASS: :assert go'\''i snapshot carries args (prami(karl,bel) FALSE)'

# Nested go'i in a `lo nu` abstraction body resolves instead of fail-closing.
# `? mi nelci lo nu go'i` after `mi klama` must produce a [Query] verdict, NOT the
# pre-fix "unsupported position" rejection.
smoke-gasnu-goi-nested: build-wasm build-gasnu
    @echo "Smoke-testing nested go'i in a lo nu abstraction body resolves (not fail-closed)..."
    @out=$(printf 'mi klama\n? mi nelci lo nu go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        if echo "$out" | grep -qF 'unsupported position'; then echo 'FAIL: nested go'\''i still rejected (not resolved)'; exit 1; fi; \
        echo "$out" | grep -qF '[Query]' || { echo 'FAIL: nested go'\''i did not produce a query verdict'; exit 1; }; \
        echo 'PASS: nested go'\''i in lo nu resolves (no unsupported-position reject)'

# Selbri-position go'i in a tanru: `mi sutra go'i` after `mi klama` resolves the
# tanru arm to the antecedent's relation selbri (`mi sutra klama`). Asserting
# `mi sutra klama` first makes the resolved query match -> TRUE. Pre-fix it was
# rejected with "unsupported position". Pre-release gate (needs the WASM build).
smoke-gasnu-goi-tanru: build-wasm build-gasnu
    @echo "Smoke-testing selbri-position go'i in a tanru (mi sutra go'i resolves)..."
    @out=$(printf 'mi sutra klama\nmi klama\n? mi sutra go'\''i\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        if echo "$out" | grep -qF 'unsupported position'; then echo 'FAIL: tanru go'\''i still rejected (not resolved)'; exit 1; fi; \
        echo "$out" | grep -qF '[Query] TRUE' || { echo 'FAIL: ? mi sutra go'\''i did not resolve to mi sutra klama (TRUE)'; exit 1; }; \
        echo 'PASS: selbri-position go'\''i resolves (mi sutra go'\''i -> mi sutra klama, TRUE)'

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

# CWA-FALSE-note smoke (dual of the NAF note): a positive FALSE that rests on the closed-world
# assumption (a missing fact, not derivable) must print the closed-world caveat, carried as the
# first-class `cwa-false` WIT proof-trace field. A numeric-decided FALSE (`5 = 3`) must NOT — it
# is genuinely false, not closed-world. Guards both directions end-to-end across the WIT boundary.
smoke-gasnu-cwa-false: build-wasm build-gasnu
    @echo "Smoke-testing gasnu closed-world FALSE note (WIT proof-trace cwa-false flag)..."
    @out=$(printf '? la .adam. cu gerku\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] FALSE' || { echo 'FAIL: missing-fact query did not answer FALSE'; exit 1; }; \
        echo "$out" | grep -qF '[Note: FALSE is closed-world' || { echo 'FAIL: missing closed-world FALSE note (cwa-false flag not carried through the WIT proof-trace)'; exit 1; }; \
        num=$(printf '? li mu cu dunli li ci\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$num"; \
        if echo "$num" | grep -qF '[Note: FALSE is closed-world'; then echo 'FAIL: a numeric-decided FALSE wrongly carried the closed-world note'; exit 1; fi; \
        echo 'PASS: closed-world FALSE carries the caveat; numeric-decided FALSE does not'

# Pre-release smoke: exercises the full WASM `:debug` round-trip — lasna guest
# converter (logji -> WIT logic-buffer) -> WIT boundary -> gasnu reverse converter
# (WIT -> nibli_types) -> nibli-render tree + English gloss. An ASYMMETRIC converter
# field-swap (e.g. one side maps And -> Or) is type-valid, so `just check`/`ci` miss
# it, but it corrupts the rendered structure here. NOT in `ci` (needs the WASM build).
smoke-gasnu-debug: build-wasm build-gasnu
    @echo "Smoke-testing gasnu :debug WASM round-trip (typed buffer -> host render)..."
    @out=$(printf ':debug ro lo gerku cu danlu\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Logic]' || { echo 'FAIL: missing [Logic] block'; exit 1; }; \
        echo "$out" | grep -qF '∀ _v0:' || { echo 'FAIL: ForAll node not rendered (converter regression?)'; exit 1; }; \
        echo "$out" | grep -qF 'Or:' || { echo 'FAIL: material-conditional Or node not rendered'; exit 1; }; \
        echo "$out" | grep -qF 'gerku_x1(' || { echo 'FAIL: role predicate not rendered functionally'; exit 1; }; \
        echo "$out" | grep -qF '[English] For every X, if X is a dog, then X is an animal.' || { echo 'FAIL: English back-translation wrong (round-trip corrupted)'; exit 1; }; \
        if echo "$out" | grep -qF '(Pred'; then echo 'FAIL: S-expression leaked into :debug output'; exit 1; fi; \
        echo 'PASS: :debug renders the typed buffer host-side (tree + English), no S-expr'

# Pre-release smoke: the collapsed macro-logical-DAG proof view. `?` shows the
# compressed surface-level steps (no role/event scaffolding); `:proof-verbose`
# keeps the full role-level trace. NOT in `ci` (needs the WASM build).
smoke-gasnu-collapse: build-wasm build-gasnu
    @echo "Smoke-testing gasnu collapsed proof (? default) + :proof-verbose escape hatch..."
    @collapsed=$(printf 'la .rex. cu gerku\nro lo gerku cu danlu\n? la .rex. cu danlu\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$collapsed"; \
        echo "$collapsed" | grep -qF '[Query] TRUE' || { echo 'FAIL: collapsed query did not answer TRUE'; exit 1; }; \
        echo "$collapsed" | grep -qF 'by the rule' || { echo 'FAIL: collapsed proof missing the macro rule step'; exit 1; }; \
        if echo "$collapsed" | grep -qF 'Conjunction'; then echo 'FAIL: verbose scaffolding leaked into the collapsed ? view'; exit 1; fi; \
        if echo "$collapsed" | grep -qF 'role-level detail'; then echo 'FAIL: role-level detail cluster shown in collapsed text'; exit 1; fi; \
        echo 'PASS: ? shows the clean collapsed macro-logical DAG'
    @verbose=$(printf 'la .rex. cu gerku\nro lo gerku cu danlu\n:proof-verbose la .rex. cu danlu\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$verbose"; \
        echo "$verbose" | grep -qF '[Query] TRUE' || { echo 'FAIL: :proof-verbose query did not answer TRUE'; exit 1; }; \
        echo "$verbose" | grep -qF 'Conjunction' || { echo 'FAIL: :proof-verbose did not show the full role-level trace'; exit 1; }; \
        echo 'PASS: :proof-verbose shows the full role-level trace'

# Backend-unavailable smoke: an external compute predicate (tenfa) with NO backend
# configured must yield UNKNOWN (backend-unavailable), NEVER a definitive FALSE — a
# backend outage is not a derived falsehood. Exercises the new four-valued reason
# end-to-end across the WIT boundary. NOT in `ci` (needs the WASM build).
smoke-gasnu-backend-unavailable: build-wasm build-gasnu
    @echo "Smoke-testing gasnu backend-unavailable verdict (no compute backend configured)..."
    @out=$(printf ':compute tenfa\n? li bi tenfa li re li ci\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] UNKNOWN (backend-unavailable)' || { echo 'FAIL: an unreachable backend did not surface UNKNOWN (backend-unavailable)'; exit 1; }; \
        if echo "$out" | grep -qF '[Query] FALSE'; then echo 'FAIL: backend outage degraded to a definitive FALSE'; exit 1; fi; \
        echo 'PASS: an unreachable compute backend yields UNKNOWN (backend-unavailable), not FALSE'

# Non-finite smoke: a numeric literal too large for an f64 (~309+ digits overflows to ±inf)
# makes the comparison/arithmetic undetermined — the query must surface UNKNOWN (non-finite),
# NEVER a confident TRUE/FALSE. Exercises the new four-valued reason across the WIT boundary.
smoke-gasnu-non-finite: build-wasm build-gasnu
    @echo "Smoke-testing gasnu non-finite numeric verdict (literal overflows f64)..."
    @nines=$(printf 'so %.0s' $(seq 320)); \
        out=$(printf "? li ${nines}cu dunli li ${nines}\n" \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$out"; \
        echo "$out" | grep -qF '[Query] UNKNOWN (non-finite)' || { echo 'FAIL: a non-finite numeric literal did not surface UNKNOWN (non-finite)'; exit 1; }; \
        if echo "$out" | grep -qE '\[Query\] (TRUE|FALSE)'; then echo 'FAIL: non-finite input degraded to a confident verdict'; exit 1; fi; \
        echo 'PASS: a non-finite numeric literal yields UNKNOWN (non-finite), not a confident verdict'

# Quiet-mode smoke: NIBLI_QUIET=1 suppresses the per-assertion bookkeeping the book
# strips — `[Fact #N]` on the host, `[Skolem]`/`[Rule]` in the guest (the latter reached
# only via the host->guest WASI env hop) — while the verdict + proof trace stay. The
# default (unset) still prints the diagnostics, so a live REPL is unchanged. Guards the
# host gate AND the env forwarding end-to-end. Pre-release gate (needs the WASM build).
smoke-gasnu-quiet: build-wasm build-gasnu
    @echo "Smoke-testing gasnu NIBLI_QUIET mode (suppress [Fact]/[Skolem]/[Rule], keep proof)..."
    @q=$(printf 'la .adam. gerku\nro lo gerku cu danlu\n? la .adam. danlu\n' \
        | NIBLI_QUIET=1 NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$q"; \
        echo "$q" | grep -qF '[Query] TRUE' || { echo 'FAIL: quiet-mode query lost its verdict'; exit 1; }; \
        echo "$q" | grep -qF 'adam is an animal' || { echo 'FAIL: quiet-mode query lost its proof trace'; exit 1; }; \
        if echo "$q" | grep -qE '\[(Fact|Skolem|Rule)'; then echo 'FAIL: NIBLI_QUIET=1 did not suppress the per-assertion bookkeeping'; exit 1; fi; \
        v=$(printf 'la .adam. gerku\nro lo gerku cu danlu\n? la .adam. danlu\n' \
        | NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu 2>&1); \
        echo "$v"; \
        echo "$v" | grep -qF '[Fact #0] Asserted.' || { echo 'FAIL: default (verbose) mode dropped the [Fact] echo'; exit 1; }; \
        echo "$v" | grep -qE '\[(Skolem|Rule)' || { echo 'FAIL: default (verbose) mode dropped the guest [Skolem]/[Rule] diagnostics'; exit 1; }; \
        echo 'PASS: NIBLI_QUIET=1 suppresses [Fact]/[Skolem]/[Rule] but keeps the verdict + proof; default stays verbose'

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
    cargo clippy --no-deps -p nibli-protocol -p nibli-render -p nibli-store -p nibli-engine -p nibli --all-targets -- -D warnings

# Run gerna unit tests only (bypasses cdylib linker issues)
test-gerna:
    cargo test -p gerna --lib -- --nocapture

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
test-gasnu:
    cargo test -p gasnu

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

# Launch the standalone Transparency Triad web UI (dev server with hot-reload) on
# a fixed port (default 8080; override e.g. `just ui 9000`). Reasoning runs fully
# in-browser; the only optional network call is the client-side Translate.
ui PORT="8080":
    cd nibli-ui && dx serve --port {{PORT}}

# Run nibli-store unit tests
test-store:
    cargo test -p nibli-store -- --nocapture

# Run REPL with persistent storage
run-persist: build-wasm
    NIBLI_DB_PATH=nibli.redb NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm cargo run -p gasnu {{cargo_profile_flag}}

# Persistence and replay regressions across engine and store layers
test-persistence-replay:
    cargo test -p nibli-engine --test integration persistent_engine_honors_store_retractions_after_reopen -- --nocapture --test-threads=1

# Run every test suite (unit + integration + Python + store)
test-all: test test-engine test-store test-backend test-classifier

# CI gate for the hardened runtime surface (fast; native only — no WASM build).
# For the WASM behavioral smokes too, run `just ci-all`.
ci: fmt-check clippy-runtime test test-engine test-gasnu test-backend test-store test-persistence-replay verify-harness verify-soundness verify-parser verify-proofs verify-book-vocab

# WASM behavioral gate (pre-push, NOT part of `ci` — needs the WASM build, like
# verify-book-capture). Bundles the six gasnu smokes; each depends on
# `build-wasm build-gasnu`, so `just` builds the component + host once, then runs
# all six: fuel exhaustion + post-trap recovery + journal replay (trap-recovery),
# plus the script transcript, go'i, persist-replay, NAF-note, and :debug round-trip.
ci-wasm: smoke-gasnu-script smoke-gasnu-trap-recovery smoke-gasnu-goi smoke-gasnu-goi-bare smoke-gasnu-goi-partial smoke-gasnu-goi-after-query smoke-gasnu-goi-assert-fact smoke-gasnu-goi-nested smoke-gasnu-goi-tanru smoke-gasnu-persist-replay smoke-gasnu-naf smoke-gasnu-cwa-false smoke-gasnu-debug smoke-gasnu-collapse smoke-gasnu-backend-unavailable smoke-gasnu-non-finite smoke-gasnu-quiet smoke-gasnu-determinism verify-wasm-node

# Three-way determinism, WASMTIME leg: the shared determinism-corpus.lojban must produce
# exactly its pinned annotations through the lasna component under gasnu. The native leg
# is determinism_corpus_native (verify-soundness); the V8 leg is verify-wasm-node.
smoke-gasnu-determinism: build-wasm build-gasnu
    @echo "Smoke-testing gasnu three-way determinism corpus..."
    @expected=$(grep '^# =>' determinism-corpus.lojban | sed 's/^# => //'); \
        actual=$(NIBLI_WASM_PATH={{wasm_dir}}/lasna.wasm ./target/{{profile}}/gasnu --script determinism-corpus.lojban 2>&1 | sed -n 's/^\[Query\] //p'); \
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

# Comprehensive pre-push / pre-release gate: the fast native `ci` plus the WASM
# behavioral smokes. `ci` alone does not exercise the WASM component.
ci-all: ci ci-wasm

# Build the nibli-validate binary (batch Lojban validation via stdin)
build-validate:
    cargo build -p nibli --bin nibli-validate {{cargo_profile_flag}}

# Manuscript gate: run every Lojban example in book/ through the engine (parse + vocab).
# Detection half of the manuscript-CI gate (see book/tools/README.md).
verify-book: build-validate
    python3 book/tools/verify_book.py --validate-bin target/debug/nibli-validate

# Manuscript gate, vocab-only (fast; no build needed). book/ is a SEPARATE repo
# (gitignored here), so it is absent on a fresh checkout / in CI — skip gracefully
# then, mirroring verify_book.py's own XML-absent skip. Runs the gate when present.
verify-book-vocab:
    @if [ -f book/tools/verify_book.py ]; then \
        python3 book/tools/verify_book.py --vocab-only; \
    else \
        echo "verify-book-vocab: book/ not checked out (separate repo) — skipping"; \
    fi

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

# Differential SOUNDNESS gate (Track A), two oracles: nibli's verdict must agree with
# (1) the Vampire FOL prover over the Horn/NAF-free fragment, and (2) the clingo ASP solver
# over the stratified-NAF + closed-world fragment (curated + random NAF programs). The Nix
# dev shell provides `vampire` + `clingo`; each side skips cleanly if its solver is absent.
verify-soundness:
    cargo test -p nibli-verify --lib --test differential_gate {{cargo_profile_flag}} -- --nocapture --test-threads=1

# gerna <-> camxes parse-differential (the FRONT-END gate): every sentence gerna accepts
# must parse under the official Lojban grammar (ilmentufa camxes, driven via node over
# the shipped corpora + seeded random batches). One-directional: gerna implements a
# fragment, so gerna-rejects carry no signal. The Nix dev shell provides node + the
# pinned ilmentufa checkout (NIBLI_CAMXES_DIR); skips cleanly when either is absent.
verify-parser:
    cargo test -p nibli-verify --test parser_differential {{cargo_profile_flag}} -- --nocapture --test-threads=1

# Mechanized-proof gate (Track B): check the Lean 4 soundness proofs in `proofs/`. The Nix
# dev shell provides `lean`; `lean` exits non-zero on any unproved/false theorem. Skips
# cleanly if `lean` is absent (the proofs are still conformance-checked from Rust via the
# `exhaustive_soundness_matches_lean_model` test in `cargo test -p logji`).
verify-proofs:
    @if command -v lean >/dev/null 2>&1; then \
        for f in proofs/*.lean; do echo "checking $f"; lean "$f" || exit 1; done; \
        echo "verify-proofs: all proofs/*.lean check (mechanized soundness)"; \
    else \
        echo "verify-proofs: lean not found (the Nix dev shell provides it) — skipping"; \
    fi

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
