"""Routing-table resolution for OpenRouter model selection (Patterns A & B).

The table lives at skills/council/model-routing.json. Resolution always
degrades to "claude" when a task/lens is unmapped or the file is absent, so
routing is never a hard dependency.
"""

import json
import os

CLAUDE = "claude"

DEFAULT_ROUTING_PATH = os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "skills", "council", "model-routing.json",
)


def load_routing(path=DEFAULT_ROUTING_PATH):
    """Load the routing table; return {} on a missing or invalid file."""
    try:
        with open(path, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except (OSError, json.JSONDecodeError):
        return {}


def _fallback(routing):
    return routing.get("defaults", {}).get("fallback", CLAUDE)


def resolve_task_model(routing, task):
    """Return the model id for a task class, or the fallback (default claude)."""
    return routing.get("tasks", {}).get(task) or _fallback(routing)


def resolve_lens_model(routing, lens):
    """Return the model id for a council lens, or the default lens model."""
    return (routing.get("lenses", {}).get(lens)
            or routing.get("defaults", {}).get("lens", CLAUDE))


def routed_consult(task, system, prompt, *, routing=None, **consult_kwargs):
    """Resolve the cheap model for a task class and consult it (Pattern B).

    Returns a {"fallback": "claude", "reason": ...} signal without any network
    call when the task routes to Claude; otherwise returns the consult result
    (which is itself fail-soft). Extra kwargs pass through to consult().
    """
    table = routing if routing is not None else load_routing()
    model = resolve_task_model(table, task)
    if model == CLAUDE:
        return {"fallback": "claude", "reason": f"task '{task}' routed to claude"}

    from openrouter_client import consult  # local import keeps modules decoupled
    return consult(model, system, prompt, **consult_kwargs)
