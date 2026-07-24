"""Graphene helpers (optional: graphene)."""

from __future__ import annotations

from typing import Any

from nibli_auth._native import can


def ensure_can(agent: str, action: str, object: str, context_kr: str = "") -> None:
    d = can(agent, action, object, context_kr)
    if not d.allowed:
        raise Exception(f"forbidden: {d.verdict}")  # graphene often wraps Exception


def resolve_with_auth(
    action: str,
    get_object: Any,
    get_agent: Any = None,
    get_context_kr: Any = None,
):
    """Wrap a resolve_ method."""

    def deco(fn: Any) -> Any:
        def wrapper(root: Any, info: Any, *args: Any, **kwargs: Any) -> Any:
            agent = (
                get_agent(info)
                if get_agent
                else getattr(info.context, "agent", "") or ""
            )
            obj = get_object(root, info, **kwargs) if callable(get_object) else str(get_object)
            ctx = (
                get_context_kr(info)
                if get_context_kr
                else getattr(info.context, "nibli_kr", "") or ""
            )
            ensure_can(str(agent), action, str(obj), str(ctx))
            return fn(root, info, *args, **kwargs)

        return wrapper

    return deco
