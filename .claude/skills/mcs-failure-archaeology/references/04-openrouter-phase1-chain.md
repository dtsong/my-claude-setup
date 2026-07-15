# OpenRouter Phase 1 chain

PR #55, feature branch `feat/openrouter-phase1`, merged 2026-06-22 (commit `c8b5368`). Status: **merged, in production, but has zero callers wired in** (Phase 2 lens relay is design-only). This is the most recent multi-commit feature chain in the repo and the clearest example of the local-review-loop pattern.

## Feature commits (all 2026-06-22, chronological)

`b61e102` (request builders) → `3e99a66` (fail-soft `consult` primitive: never raises, callers degrade to the normal Claude path on any failure) → `7a01a5d` (stdio MCP server) → `daff46a` (routing config/resolver) → `4d9694e` (`routed_consult`, "Pattern B" primitive) → `dfc0676` (register the MCP server, document the Pattern B contract) → `884611d` (gated live smoke test).

## Pre-merge review-fix chain (same morning)

- `4d40c2c` (01:41): hoist imports to module top, clarify venv bootstrap steps in README.
- `898174d` (01:46): **three review findings fixed in one commit**, +33 lines of tests:
  1. `urlopen` raises `HTTPError` on 4xx/5xx responses. The original code caught only generic exceptions, so HTTP failures (bad key, rate limit, etc.) were misclassified as transport failures. Fixed to catch `HTTPError` explicitly and return `(code, body)` for correct classification.
  2. `parse_success` crashed with an unhandled exception if `message.content` was not a string (e.g. null content from certain models/responses). Fixed to raise a `TypeError` that `consult` converts into a fallback signal instead of propagating.
  3. DRY'd the `max_tokens` default (was hardcoded in more than one place).

## The review-count trap

`gh pr view 55 --json reviews,comments` returns `{"comments":[],"reviews":[]}` (verified 2026-07-02): **PR #55 has zero GitHub reviews and zero comments.** The three findings in `898174d` were caught by a local Claude code-review loop, not a human reviewer, run in the same session before merge. Both fix commits (`4d40c2c`, `898174d`) are co-authored by Claude Sonnet 4.6, while the feature commits were authored under Opus/Fable sessions. Do not use PR review-count as a proxy for how scrutinized a change was in this repo; check for a same-day fix commit chain instead.

## Post-merge fix: PR #56 (`01b6081`, merged 2026-06-25)

A 4th bug shipped anyway and needed a post-merge fix: LLM conductors sometimes JSON-stringified the Workflow `args` object before passing it to `council-audit.template.js` / `council-deliberation.template.js`. Destructuring keys off a string (instead of an object) silently yielded `undefined` for every key, so the contract guard threw "requires args: sessionDir, idea, roster[]" on otherwise-valid invocations. Fix: parse stringified payloads back into objects in both templates, plus a tightened engine instruction in `commands/_council-engine.md` explicitly naming the exact error a stringified payload produces (so a future LLM conductor reading the instruction avoids the mistake).

## Design docs and tracking

- `docs/superpowers/specs/2026-06-22-openrouter-integration-design.md` (+ `.html` companion). **Note**: an earlier sweep's notes cited `docs/designs/2026-06-22-...`; that path does not exist. The correct path is under `docs/superpowers/specs/`, verified 2026-07-02.
- `docs/superpowers/plans/2026-06-22-openrouter-phase1.md`.
- Tracking issue `#54` ("OpenRouter integration: MCP consult() primitive + multi-model council lenses + cheap routing") is still **OPEN** as of 2026-07-02: Phase 2 (lens relay, eval-gated) is design-only, never started.

## Current state, not just history

- `mcp/openrouter/` requires manual venv bootstrap at `mcp/openrouter/.venv/`; the exact interpreter path is hardcoded in `settings.json`'s `mcpServers.openrouter.command`. The server raises `FileNotFoundError` without that venv.
- `OPENROUTER_API_KEY` is read from the shell env only (`${OPENROUTER_API_KEY}` expansion in settings.json); as of this sweep's checks it was unset in the working environment, meaning `consult` returns a `missing_key` fallback rather than actually routing.
- `skills/council/model-routing.json` routes only 3 task classes (`classification`, `scout-research`, `scoring`) as of 2026-07-02; `"lenses": {}` is an empty stub, i.e. Phase 2 has zero live callers.
- Model IDs in `model-routing.json` were stale 2024-era placeholders (`openai/gpt-4o-mini`, `google/gemini-flash-1.5`) at authoring; fixed by US-004/#62 (PR #70, merged 2026-07-02) with `mcp/openrouter/check_models.py` as the staleness checker. IDs still rot: re-run that script monthly.

## Evidence commands

```bash
git log --oneline feat/openrouter-phase1 2>/dev/null || git log --oneline --all | grep -E "b61e102|3e99a66|7a01a5d|daff46a|4d9694e|dfc0676|884611d"
git show --stat 898174d
gh pr view 55 --json reviews,comments
git show --stat 01b6081
gh issue view 54
```
