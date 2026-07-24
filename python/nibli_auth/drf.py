"""Django REST framework helpers (optional: djangorestframework)."""

from __future__ import annotations

from typing import Any, Optional

from nibli_auth._native import can


def _agent_from_request(request: Any) -> str:
    h = getattr(request, "headers", None) or {}
    # DRF Request.headers is case-insensitive
    agent = h.get("X-Agent") or h.get("x-agent") or ""
    return str(agent).strip()


def _context_from_request(request: Any) -> str:
    db = getattr(request, "nibli_context_db", None)
    if db is None:
        db = getattr(getattr(request, "user", None), "nibli_context", None)
    if isinstance(db, dict):
        agent = _agent_from_request(request)
        return db.get(agent, "") or ""
    if isinstance(db, str):
        return db
    return ""


class NibliPermission:
    """
    DRF-style permission class (duck-typed; no hard django import at module load).

    Set on the view:
      nibli_action = "read" | "update" | ...
      nibli_object_attr = "pk"  # attribute on the object for KR Name
    Attach context via request.nibli_context_db = {agent: kr_snippet}.
    """

    nibli_action: str = "read"

    def has_permission(self, request: Any, view: Any) -> bool:
        agent = _agent_from_request(request)
        if not agent:
            return False
        # List views: allow through; object check does the real work when applicable.
        return True

    def has_object_permission(self, request: Any, view: Any, obj: Any) -> bool:
        agent = _agent_from_request(request)
        if not agent:
            return False
        action = getattr(view, "nibli_action", self.nibli_action)
        attr = getattr(view, "nibli_object_attr", "pk")
        object_id = str(getattr(obj, attr, obj))
        # Ensure KR Name shape for simple ints
        if object_id and object_id[0].isdigit():
            object_id = f"Doc{object_id}"
        ctx = _context_from_request(request)
        d = can(agent, action, object_id, ctx)
        return bool(d.allowed)


class NibliDjangoFilterBackend:
    """
    Sketch: mark request for row-level filtering; actual queryset filtering is
    app-specific (map KR resource names to primary keys).
    """

    def filter_queryset(self, request: Any, queryset: Any, view: Any) -> Any:
        # No automatic filtering without a domain mapping — return unchanged.
        request.nibli_auth_filter = True  # type: ignore[attr-defined]
        return queryset
