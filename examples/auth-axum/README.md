# auth-axum

Minimal **axum** demo for [`nibli-auth`](../../nibli-auth) using the same builtin
policy as A1 (`nibli-auth/policy/auth-0.1.0.nibli`).

## Concurrency

The reasoner KB is `!Send` (`RefCell`). This example does **not** put
`Authorizer` in `axum::State`. Each Tokio worker uses a **thread-local** warm
authorizer (`nibli_auth::tls`). Ownership / role facts come from a simulated app
DB and are passed per request as `context_kr`.

## Run

```bash
# from repo root, inside nix develop
cargo run -p auth-axum
```

Server: `http://127.0.0.1:3001`

## Try

```bash
# owner read (200)
curl -s -H 'X-Agent: Alice' http://127.0.0.1:3001/docs/Doc1

# stranger update (403)
curl -s -X PUT -H 'X-Agent: Bob' http://127.0.0.1:3001/docs/Doc1

# admin update (200) — needs resource(Doc1) in context
curl -s -X PUT -H 'X-Agent: Carol' http://127.0.0.1:3001/docs/Doc1

# tenant read (200) / update (403)
curl -s -H 'X-Agent: Dave' http://127.0.0.1:3001/docs/Doc1
curl -s -X PUT -H 'X-Agent: Dave' http://127.0.0.1:3001/docs/Doc1

# explain
curl -s -H 'X-Agent: Alice' 'http://127.0.0.1:3001/docs/Doc1?explain=1'
```

Header **`X-Agent`** is required (demo identity).
