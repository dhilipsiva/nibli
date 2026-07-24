"""FastAPI helpers for nibli_auth (optional dependency: fastapi)."""

from __future__ import annotations

from typing import Any, Callable, Mapping, Optional

from nibli_auth._native import can


def agent_from_headers(headers: Mapping[str, str]) -> str:
    """Read demo identity from X-Agent (case-insensitive)."""
    for k, v in headers.items():
        if k.lower() == "x-agent" and v and str(v).strip():
            return str(v).strip()
    raise LookupError("missing X-Agent header")


def require(
    agent: str,
    action: str,
    object: str,
    context_kr: str = "",
) -> Any:
    """Return Decision if allowed, else raise fastapi.HTTPException(403)."""
    try:
        from fastapi import HTTPException
    except ImportError as e:  # pragma: no cover
        raise ImportError("fastapi is required for nibli_auth.fastapi_ext") from e

    d = can(agent, action, object, context_kr)
    if not d.allowed:
        raise HTTPException(
            status_code=403,
            detail={
                "allowed": False,
                "verdict": d.verdict,
                "reason": d.reason,
            },
        )
    return d


def context_from_db(db: Mapping[str, str], agent: str) -> str:
    """Look up per-agent KR context snippet (empty if unknown)."""
    return db.get(agent, "") or ""


def make_require_dependency(
    action: str,
    object_from_path: Callable[..., str],
    db_attr: str = "db",
):
    """
    Build a FastAPI dependency factory.

    Usage sketch::

        dep = make_require_dependency("read", lambda name: name)
        # wire with Depends in a route that also has Path(name) and Header x_agent
    """

    def dependency(
        name: str,
        x_agent: Optional[str] = None,
        request: Any = None,
    ):
        try:
            from fastapi import Header, HTTPException, Request
        except ImportError as e:  # pragma: no cover
            raise ImportError("fastapi is required") from e

        # Prefer explicit header param when provided by the route.
        agent = (x_agent or "").strip()
        if not agent and request is not None:
            try:
                agent = agent_from_headers(request.headers)
            except LookupError:
                raise HTTPException(status_code=401, detail="missing X-Agent header")
        if not agent:
            raise HTTPException(status_code=401, detail="missing X-Agent header")

        obj = object_from_path(name)
        ctx = ""
        if request is not None and hasattr(request.app.state, db_attr):
            db = getattr(request.app.state, db_attr)
            if isinstance(db, Mapping):
                ctx = context_from_db(db, agent)
        return require(agent, action, obj, ctx)

    return dependency
