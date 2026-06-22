#!/usr/bin/env python3
# mcp/openrouter/server.py
"""openrouter MCP server — exposes a single `consult` tool over stdio.

Reads OPENROUTER_API_KEY from the environment. Fails soft: a failed call
returns a structured {"error", "fallback": "claude"} dict so callers degrade
to their normal Claude path. Single-shot only — no multi-turn, no tool use.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from mcp.server.fastmcp import FastMCP
from openrouter_client import consult as consult_impl

mcp = FastMCP("openrouter")


@mcp.tool()
def consult(model: str, system: str, prompt: str,
            max_tokens: int = 1024, temperature: float | None = None) -> dict:
    """Call an arbitrary OpenRouter-hosted model, single-shot.

    Args:
        model: OpenRouter model id, e.g. "openai/gpt-4o-mini".
        system: System prompt (persona / instructions).
        prompt: User prompt for this single turn.
        max_tokens: Max completion tokens (default 1024).
        temperature: Optional sampling temperature.

    Returns:
        On success: {"text", "model", "usage": {"prompt_tokens", "completion_tokens"}}.
        On any failure: {"error", "error_kind", "fallback": "claude"}.
    """
    return consult_impl(model, system, prompt,
                        max_tokens=max_tokens, temperature=temperature)


if __name__ == "__main__":
    mcp.run()
