"""nibli_auth — Python helpers over the nibli-auth native extension.

Concurrency: the native module uses a Rust thread-local warm Authorizer
(KB is !Send). Pass owns/roles as context_kr per call (same as auth-axum).
"""

from __future__ import annotations

from nibli_auth._native import (
    Decision,
    Explained,
    allowed_fields,
    can,
    explain,
    policy_version,
    reset_thread_auth,
)

__all__ = [
    "Decision",
    "Explained",
    "allowed_fields",
    "can",
    "explain",
    "policy_version",
    "reset_thread_auth",
    "fastapi_ext",
]

__version__ = policy_version()
