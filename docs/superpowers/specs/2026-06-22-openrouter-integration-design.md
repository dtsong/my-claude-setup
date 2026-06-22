# OpenRouter Integration — Design Spec

**Date:** 2026-06-22
**Status:** Approved design, pending implementation plan
**Related:** council engine (`commands/_council-engine.md`, `.claude/workflows/council-deliberate.js`)

## Overview

Add the ability to call arbitrary OpenRouter-hosted models from inside Claude Code
workflows, exposed as a single MCP primitive. Two usage patterns build on it:

- **Pattern A — multi-model council lenses:** back selected council lenses with
  non-Claude vendor models so deliberation gains genuine cross-vendor diversity.
- **Pattern B — cheap sub-task routing:** route high-volume, low-stakes sub-tasks
  (classification, scout research, scoring) to inexpensive models while reserving
  Opus for synthesis.

## Goals / Non-goals

**Goals**
- One reusable primitive (`consult`) callable from main loop, subagents, and
  Workflow agents (via ToolSearch).
- Council lenses reuse their existing persona prompts verbatim — no new persona
  content; diversity comes from the model itself.
- OpenRouter is never a hard dependency: any failure falls back to Claude.

**Non-goals**
- Pointing the whole Claude Code harness at OpenRouter (`ANTHROPIC_BASE_URL`). Out
  of scope; this is about calling OpenRouter *from within* workflows.
- Multi-turn agentic loops on non-Claude models. `consult` is single-shot.
- Tool use / function calling on non-Claude models (future extension).

## Architecture

### The `openrouter` MCP server (the one primitive)

A small MCP server registered in `settings.json` → `mcpServers`. Language:
**Python** (matches existing hooks/pipeline tooling; `new-mcp-server` skill
scaffolds it). Reads `OPENROUTER_API_KEY` from env; never committed.

Tool:

```
consult(model: str, system: str, prompt: str,
        max_tokens?: int, temperature?: float)
  -> { text: str, model: str, usage: {prompt_tokens, completion_tokens} }
```

- Maps to `POST https://openrouter.ai/api/v1/chat/completions` with
  `messages = [{role: system, content: system}, {role: user, content: prompt}]`.
- `Authorization: Bearer $OPENROUTER_API_KEY`; sets `HTTP-Referer`/`X-OpenRouter-Title`
  for attribution.
- Fails soft: missing key, 4xx/5xx, or timeout → returns a structured error the
  caller can detect and fall back on (never raises an unhandled exception).

Optional later: `list_models()` passthrough to `GET /api/v1/models`.

### Routing config

`skills/council/model-routing.json`:

```json
{
  "lenses":  { "<lens>": "claude" | "<openrouter-model-id>" },
  "tasks":   { "classification": "<cheap-model>", "scout-research": "...", "scoring": "..." },
  "defaults": { "lens": "claude", "fallback": "claude" }
}
```

- `lenses`: per-lens model. Default `claude` (existing subagent path). Override
  chosen lenses to vendor model ids (`openai/...`, `google/...`).
- `tasks`: task-class → cheap model for Pattern B.
- `fallback`: model family used when an OpenRouter call fails.

## Pattern A — multi-model council lenses

In `council-deliberate.js`, a lens whose routing entry is non-Claude is dispatched
as a **thin Claude relay `agent()`** whose only job is:

1. Call `consult(model=<routing>, system=<existing lens persona prompt>, prompt=<round prompt>)`.
2. Return the model's `text` verbatim as that lens's contribution.

Claude-routed lenses keep the current native-subagent path unchanged.

**Why a relay:** Workflow scripts run sandboxed (no shell, no HTTP), so a workflow
`agent()` cannot call OpenRouter directly — but a Claude agent it spawns *can* call
the MCP tool. The relay adds one short Claude turn (negligible reasoning); the lens
output is genuinely the other vendor's reasoning, so diversity is preserved and the
deterministic Workflow orchestration stays intact.

**Rejected alternative:** run non-Claude rounds in the main-loop council command via
direct MCP calls (no relay). Saves the hop but forfeits Workflow's deterministic
round-to-round orchestration. Not chosen.

## Pattern B — cheap sub-task routing

Skills/subagents that perform a routed task class call `consult(<tasks[class]>, …)`
directly — main-loop and subagent contexts have MCP access, so no relay is needed.
On failure, fall back to the normal Claude path for that sub-task.

## Resilience & secrets

- **Fallback:** every caller treats a `consult` error as "use Claude instead."
  OpenRouter outages degrade gracefully to today's all-Claude behavior.
- **Secrets:** `OPENROUTER_API_KEY` lives in the shell env only, documented in
  setup. The MCP server fails soft (and logs once) if the key is absent.

## Testing

- **Unit:** mock OpenRouter; assert `consult` request shape, response parsing, and
  error → structured-failure signal.
- **Smoke:** one live call to a cheap model behind an explicit flag/env.
- **Integration (Pattern A):** a quick-mode council run with one lens routed to a
  non-Claude model returns that lens's text and the deliberation completes.

## Implementation phases

1. **Phase 1 — MCP server + Pattern B.** Build `openrouter` MCP server, routing
   config loader, and cheap-routing for one sub-task class. Lower risk, immediately
   useful, exercises the primitive end-to-end.
2. **Phase 2 — Pattern A.** Add the lens relay in `council-deliberate.js` and the
   `lenses` routing table; verify diversity in a deliberation run.

## Resolved decisions

- Lens persona source: **reuse existing persona prompt** (model plays the lens).
- Mechanism: **MCP server** (idiomatic to this MCP-heavy repo).
- Non-Claude lens execution: **thin Claude relay** inside the Workflow substrate.
- Server language: **Python**.
- Fallback: **always degrade to Claude**.
