"""Strawberry GraphQL helpers (optional: strawberry-graphql)."""

from __future__ import annotations

from typing import Any, Callable, Optional

from nibli_auth._native import can


def require_can(
    agent: str,
    action: str,
    object: str,
    context_kr: str = "",
) -> None:
    """Raise PermissionError if not allowed (map to GraphQL error in resolvers)."""
    d = can(agent, action, object, context_kr)
    if not d.allowed:
        raise PermissionError(f"forbidden: {d.verdict} {d.reason}")


def field_guard(
    action: str,
    object_from_info: Callable[[Any], str],
    agent_from_info: Optional[Callable[[Any], str]] = None,
    context_from_info: Optional[Callable[[Any], str]] = None,
):
    """Decorator for strawberry field resolvers."""

    def deco(fn: Callable[..., Any]) -> Callable[..., Any]:
        def wrapper(root: Any, info: Any, *args: Any, **kwargs: Any) -> Any:
            agent = (
                agent_from_info(info)
                if agent_from_info
                else getattr(info.context, "agent", None) or ""
            )
            if not agent:
                raise PermissionError("missing agent on context")
            obj = object_from_info(info) if callable(object_from_info) else str(root)
            ctx = context_from_info(info) if context_from_info else getattr(info.context, "nibli_kr", "") or ""
            require_can(str(agent), action, obj, str(ctx))
            return fn(root, info, *args, **kwargs)

        return wrapper

    return deco
