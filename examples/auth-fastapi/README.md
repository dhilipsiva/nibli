# auth-fastapi

FastAPI demo for **nibli_auth** — same builtin policy and scenarios as
[`examples/auth-axum`](../auth-axum).

## Build native extension

```bash
# inside nix develop (maturin on PATH)
just build-auth-py
```

## Install Python deps

```bash
pip install -r examples/auth-fastapi/requirements.txt
```

## Run

```bash
just run-auth-fastapi
# http://127.0.0.1:3002
```

## Try

```bash
curl -s -H 'X-Agent: Alice' http://127.0.0.1:3002/docs/Doc1
curl -s -X PUT -H 'X-Agent: Bob' http://127.0.0.1:3002/docs/Doc1
curl -s -X PUT -H 'X-Agent: Carol' http://127.0.0.1:3002/docs/Doc1
curl -s -H 'X-Agent: Dave' http://127.0.0.1:3002/docs/Doc1
```

## Concurrency

Uses Rust **thread-local** warm authorizer via PyO3 (`nibli_auth_native`).
Ownership/roles come from the in-memory `DB` dict as `context_kr` per request.
