# Authorization

Nibli ships a **built-in authorization** surface: a versioned KR policy, fail-closed vocabulary, and a warm `Authorizer` that answers with ordinary entailment. Allow means the engine returned **TRUE** for `authorized(...)` — not a learned score, not an LLM.

Code lives in **`nibli-auth`** (native), **`nibli:engine@0.6.0` `authorizer`** (WASM component export), optional Rust features (`axum`, `async-graphql`, `juniper`), and **`nibli-auth-py`** / **`python/nibli_auth`** (PyO3).

This page is **code-derived** (crates, policy file, examples). It is not the Orange AVA book manuscript.

## Ontology

| Predicate | Places | Role |
|-----------|--------|------|
| `authorized` | agent, action, resource | **Decision head** — “may perform action on resource” |
| `owns` | owner, owned, basis | Existing corpus; ownership facts |
| `has_role` | agent, role | Role assignment |
| `in_tenant` | agent, tenant | Tenancy of a principal |
| `resource` | resource | Declare a protected resource (needed for admin rules) |
| `resource_tenant` | resource, tenant | Resource’s tenant |
| `visible_attr` | agent, resource, attr | Field-level (reserved for finer policies; v0.1 masking uses row `can`) |
| `agent` | agent | Optional sort for principals |

**Do not use as auth heads** (corpus collisions):

| Name | Why |
|------|-----|
| `can` | Tin/can (`lante`), not permission |
| `field` | Agricultural field (`foldi`) |
| `principal` | “Chief among” (`ralju`) — prefer `agent` |

**Actions, roles, attrs** are KR **quoted strings**: `"read"`, `"update"`, `"admin"`, `"title"`.

```nibli-kr
owns(Alice, Doc1).
authorized(Alice, "update", Doc1).   # query shape
has_role(Carol, "admin").
resource(Doc1).
```

## Builtin policy

File: [`nibli-auth/policy/auth-0.1.0.nibli`](https://github.com/dhilipsiva/nibli/blob/main/nibli-auth/policy/auth-0.1.0.nibli)  
Version constant: `nibli_auth::POLICY_VERSION` (`"0.1.0"`).

Shipped rules (summary):

- **Owner** — `owns($a, $r)` ⇒ authorized for `"read"` and `"update"`.
- **Admin** — `has_role($a, "admin") & resource($r)` ⇒ read/update that resource.
- **Tenant** — same tenant on agent and resource ⇒ `"read"` only.

**Rule writing tip:** every variable that appears in the conclusion should be constrained by a positive body condition (or bound by a ground query). Free conclusion-only variables do not fire under backward chaining here (admin rules therefore mention `resource($r)`).

Overlay extra KR with `Authorizer::load_policy(Some(extra))` or per-call `context_kr`.

## Efficiency model

| Requirement | Mechanism |
|-------------|-----------|
| No engine per request | One warm authorizer (or one per OS thread) |
| Policy once | `load_policy` / thread-local first use |
| Ephemeral request facts | `context_kr` asserted then retracted |
| Cheap hot path | `can` / `allowed_fields` — **no proof** |
| Proofs opt-in | `explain` only |
| Decision cache | Keyed by policy version + agent/action/object + context hash |

**Multi-threaded servers:** the KB uses `RefCell` and is **`!Send`**. Do **not** put `Authorizer` in `axum::State` or `Arc<Mutex<_>>`. Use:

- Rust: `nibli_auth::tls` (thread-local warm policy).
- Python: same TLS behind `nibli_auth_native` (each OS thread warms once).

Cross-thread durable owns/roles belong in the **app database** and should be passed as **`context_kr`** each call (see the examples).

**UNKNOWN** on the hot path is treated as **deny** (`allowed=false`); only engine **TRUE** allows.

## Rust API

```rust
use nibli_auth::{Authorizer, tls};

let mut auth = Authorizer::new();
auth.load_policy(None)?;
auth.assert_facts("owns(Alice, Doc1).")?;
let d = auth.can("Alice", "update", "Doc1", "")?;
assert!(d.allowed);

// Multi-thread / axum workers:
let d = tls::can("Alice", "read", "Doc1", "owns(Alice, Doc1).")?;
let fields = tls::allowed_fields("Alice", "read", "Doc1", "owns(Alice, Doc1).", &["title", "body"])?;
```

- **`can`** — row-level allow/deny (`Decision`).
- **`allowed_fields`** — v0.1: if row `can` allows, return all `candidates` (serializer masking).
- **`explain`** — same as can plus optional proof JSON.

Optional Cargo features on `nibli-auth`: `axum` (`Agent` header extractor, `require`, `field_mask`), `async-graphql`, `juniper`.

## WIT (WASM component)

Package **`nibli:engine@0.6.0`** exports **`authorizer`** alongside `engine` (logical auth surface v0.1 in the single shipping package).

| WIT | Notes |
|-----|--------|
| `load-policy` | Builtin (+ optional extra KR) |
| `can` / `allowed-fields` / `explain` | Same semantics as Rust |
| Parameter **`object`** | Protected resource id — WIT reserves the keyword `resource` |

Native and guest both wrap the same policy file via `nibli-auth`. `engine.session` and `authorizer.session` do **not** share a KB in v0.1.

## Python API

```bash
just build-auth-py    # maturin develop into .venv-auth
just test-auth-py
```

```python
from nibli_auth import can, allowed_fields, explain

d = can("Alice", "update", "Doc1", "owns(Alice, Doc1).")
assert d.allowed
fields = allowed_fields("Alice", "read", "Doc1", ["title", "body"], "owns(Alice, Doc1).")
```

Package layout: extension `nibli_auth_native` (PyO3); helpers under `python/nibli_auth/` (`fastapi_ext`, optional `drf`, `strawberry_ext`, `graphene_ext`, `spectacular`).

Identity header in demos: **`X-Agent`** (not a production auth scheme).

## Examples (same policy)

| Example | Command | Port |
|---------|---------|------|
| [auth-axum](https://github.com/dhilipsiva/nibli/tree/main/examples/auth-axum) | `just run-auth-axum` | 3001 |
| [auth-fastapi](https://github.com/dhilipsiva/nibli/tree/main/examples/auth-fastapi) | `just run-auth-fastapi` | 3002 |

Scenarios: Alice owner, Bob stranger, Carol admin, Dave same-tenant read-only.

## Extism

Extism is **not** the primary interface. A future PDK could wrap the same `can` / policy model; it is not implemented. Prefer the native Component Model / WIT path and in-process PyO3.

## Versioning

| Layer | Version |
|-------|---------|
| Policy file / `POLICY_VERSION` | `0.1.0` |
| WIT package | `nibli:engine@0.6.0` (authorizer export) |
| Crate `nibli-auth` | workspace `0.1.0` (unpublished) |

Do not invent predicates outside the fail-closed lexicon. Bump the policy version string when shipping incompatible rule changes.

## Tests

```bash
just test-auth          # Rust core + axum/graphql/juniper features
just check-auth-axum
just test-auth-py       # requires maturin / .venv-auth (local)
just docs               # includes this chapter
```
