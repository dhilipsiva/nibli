"""django-spectacular / OpenAPI notes for nibli_auth (no hard dependency)."""

from __future__ import annotations

# Suggested OpenAPI pieces for apps using X-Agent + 403 Decision body.

X_AGENT_SECURITY = {
    "type": "apiKey",
    "in": "header",
    "name": "X-Agent",
    "description": "Demo principal identity for nibli-auth (not a production auth scheme).",
}

FORBIDDEN_DECISION_SCHEMA = {
    "type": "object",
    "properties": {
        "allowed": {"type": "boolean"},
        "verdict": {"type": "string"},
        "reason": {"type": "string", "nullable": True},
    },
}


def spectacular_extend_schema_auth():
    """
    Optional helper if drf-spectacular is installed::

        from drf_spectacular.utils import extend_schema, OpenApiParameter
        # attach X-Agent parameter + 403 response manually in views
    """
    return {
        "security": [{"XAgent": []}],
        "parameters": [
            {
                "name": "X-Agent",
                "in": "header",
                "required": True,
                "schema": {"type": "string"},
            }
        ],
        "responses": {403: FORBIDDEN_DECISION_SCHEMA},
    }
