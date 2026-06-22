# openrouter MCP — agent notes

## Commands
python3 -m pytest .       # unit tests (no network)
python3 server.py         # run the stdio server (normally launched by Claude Code)

## Layout
openrouter_client.py  # pure consult() + transport (fail-soft, never raises)
routing.py            # load_routing / resolve_* / routed_consult (Pattern B)
server.py             # FastMCP entrypoint exposing the `consult` tool

## Rules
- Never let OpenRouter become a hard dependency: every path falls back to claude.
- consult is single-shot. No tool use, no multi-turn.
- OPENROUTER_API_KEY comes from the shell env only. Never write it to a file.
