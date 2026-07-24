"""Import the PyO3 extension with a clear install hint."""

from __future__ import annotations

try:
    from nibli_auth_native import (  # type: ignore
        Decision,
        Explained,
        allowed_fields,
        can,
        explain,
        policy_version,
        reset_thread_auth,
    )
except ImportError as e:  # pragma: no cover
    raise ImportError(
        "nibli_auth_native extension not found. Build it with:\n"
        "  just build-auth-py\n"
        "  # or: cd nibli-auth-py && maturin develop --release\n"
        f"Original error: {e}"
    ) from e

__all__ = [
    "Decision",
    "Explained",
    "allowed_fields",
    "can",
    "explain",
    "policy_version",
    "reset_thread_auth",
]
