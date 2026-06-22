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
