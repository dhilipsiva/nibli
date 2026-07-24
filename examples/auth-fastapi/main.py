"""
FastAPI demo for nibli_auth — same scenarios as examples/auth-axum.

Run (after `just build-auth-py` and fastapi install):
  PYTHONPATH=python:examples/auth-fastapi just run-auth-fastapi
  # or: PYTHONPATH=python uvicorn main:app --app-dir examples/auth-fastapi --port 3002
"""

from __future__ import annotations

from typing import Dict, List, Optional

from fastapi import FastAPI, Header, HTTPException, Query
from pydantic import BaseModel

from nibli_auth import allowed_fields, can, explain
from nibli_auth.fastapi_ext import context_from_db, require

# Simulated app DB: agent -> context KR (same policy as auth-axum)
DB: Dict[str, str] = {
    "Alice": "owns(Alice, Doc1).",
    "Carol": 'has_role(Carol, "admin").\nresource(Doc1).',
    "Dave": 'in_tenant(Dave, "acme").\nresource_tenant(Doc1, "acme").',
    # Bob: empty
}


class DocView(BaseModel):
    name: str
    fields: List[str]
    verdict: str
    reason: Optional[str] = None


app = FastAPI(title="nibli-auth FastAPI demo", version="0.1.0")
app.state.db = DB


def _agent(x_agent: Optional[str]) -> str:
    agent = (x_agent or "").strip()
    if not agent:
        raise HTTPException(status_code=401, detail="missing X-Agent header")
    return agent


@app.get("/health")
def health() -> str:
    return "ok"


@app.get("/docs/{name}", response_model=DocView)
def get_doc(
    name: str,
    x_agent: Optional[str] = Header(default=None, alias="X-Agent"),
    explain_flag: bool = Query(default=False, alias="explain"),
) -> DocView:
    agent = _agent(x_agent)
    ctx = context_from_db(DB, agent)
    if explain_flag:
        ex = explain(agent, "read", name, ctx)
        if not ex.decision.allowed:
            raise HTTPException(
                status_code=403,
                detail={
                    "allowed": False,
                    "verdict": ex.decision.verdict,
                    "reason": ex.decision.reason,
                },
            )
        fields = allowed_fields(
            agent, "read", name, ["title", "body", "secret"], ctx
        )
        return DocView(
            name=name,
            fields=fields,
            verdict=ex.decision.verdict,
            reason=ex.decision.reason,
        )
    d = require(agent, "read", name, ctx)
    fields = allowed_fields(agent, "read", name, ["title", "body", "secret"], ctx)
    return DocView(name=name, fields=fields, verdict=d.verdict, reason=d.reason)


@app.put("/docs/{name}", response_model=DocView)
def put_doc(
    name: str,
    x_agent: Optional[str] = Header(default=None, alias="X-Agent"),
) -> DocView:
    agent = _agent(x_agent)
    ctx = context_from_db(DB, agent)
    d = require(agent, "update", name, ctx)
    fields = allowed_fields(agent, "update", name, ["title", "body"], ctx)
    return DocView(name=name, fields=fields, verdict=d.verdict, reason=d.reason)
