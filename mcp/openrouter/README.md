# openrouter MCP Server

Single-tool MCP server that calls arbitrary OpenRouter-hosted models from
inside Claude Code workflows. Fail-soft: any error degrades to Claude.

## Install

`mcp/openrouter/.venv/` is a **required one-time bootstrap** — it is the exact
interpreter that `settings.json` → `mcpServers.openrouter.command` invokes. The
server will not start (FileNotFoundError) until this venv exists.

```bash
python3 -m venv mcp/openrouter/.venv
mcp/openrouter/.venv/bin/pip install -r mcp/openrouter/requirements.txt
export OPENROUTER_API_KEY=sk-or-...   # shell env only; never commit
```

Registered in repo `settings.json` under `mcpServers.openrouter`. The key is
passed through via `${OPENROUTER_API_KEY}` — it is never written to any file.

## Tool

`consult(model, system, prompt, max_tokens=1024, temperature=None)`
- Success → `{"text", "model", "usage": {"prompt_tokens", "completion_tokens"}}`
- Failure → `{"error", "error_kind", "fallback": "claude"}` (never raises)

Surfaced to callers (including Workflow agents via ToolSearch) as
`mcp__openrouter__consult`.

## Pattern B — cheap sub-task routing

Routing table: `skills/council/model-routing.json` (`tasks` map). For a routed
sub-task class (currently `classification`, `scout-research`, `scoring`):

1. Read `tasks[<class>]` from the routing table.
2. If it is `"claude"` (or absent), use the normal Claude path — do not call the tool.
3. Otherwise call `mcp__openrouter__consult(model=<that id>, system=..., prompt=...)`.
4. If the result has `"fallback": "claude"`, redo the sub-task the normal Claude way.

Python consumers (hooks/pipeline scripts) skip the manual steps and call
`routing.routed_consult(<class>, system, prompt)` directly.

## Test

```bash
python3 -m pytest .            # unit (no network)
OPENROUTER_SMOKE=1 python3 -m pytest tests/test_smoke.py -v   # live, costs tokens
```
