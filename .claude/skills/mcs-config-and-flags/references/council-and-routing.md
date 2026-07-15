# Council knobs, model routing, and governance config files

## Council cost profiles and mode flags

`commands/council.md` declares the theme config consumed by the shared engine (`commands/_council-engine.md`):

```
DEFAULT_PROFILE: balanced
```

Resolution order for the active profile: `--profile` flag on invocation > `DEFAULT_PROFILE` > hardcoded fallback `balanced`. The resolved profile persists in the session's `session.md` and the workspace index; a session with no recorded profile resumes as `balanced`.

`commands/_council-engine.md`'s "Cost Profiles & Model Routing" section is the spawn-site table, keyed by tier alias (never a pinned `claude-*` ID). That "never" is a documented convention only for `agents/**`: `settings.json`'s top-level `model` field is hard-enforced tier-alias-only by pre-commit (`check_settings.py` rule L1, since PR #71/#64, 2026-07-05), but `check_frontmatter.py` only validates `model:` when it is a dict block (`preferred`/`minimum`/`reasoning_demand`), never a scalar `claude-*` string, and its pre-commit glob (`files: ^skills/.*\.md$`) never matches `agents/*.md` at all. No hook enforces tier-alias-only for agent persona frontmatter today. Re-verify: `grep -n TIER_ALIASES pipeline/hooks/check_settings.py`; `grep 'files:' .pre-commit-config.yaml`.

| Spawn site | lean | balanced | max |
|---|---|---|---|
| Brainstorm agents (3x one-shot) | sonnet | sonnet | sonnet |
| Council agents (Phase 2.4, live R1→R3) | sonnet | opus | opus |
| Round 2 challenge agents | opus (fresh one-shots) | persistent agents respond | fable (fresh one-shots, falls back to opus on spawn error) |
| Audit agents (5D.2) | sonnet | sonnet | opus |
| Conductor (interview/synthesis/PRD) | inherits the user's `/model`, guidance only | | |

Re-verify: `grep DEFAULT_PROFILE commands/council.md`; `grep -A12 "Cost Profiles" commands/_council-engine.md`.

## Backend/mode flags

- `CLAUDE_CODE_DISABLE_WORKFLOWS`: unset by default (workflows enabled). `_council-engine.md:39` detects availability via `printenv CLAUDE_CODE_DISABLE_WORKFLOWS` plus a Claude Code version floor of ≥2.1.154; if a workflow invocation later fails, the engine treats that as detection and degrades workflow → teams → sequential, never a hard exit. This machine's `claude --version` was `2.1.198` as of 2026-07-02, above the floor, so the workflow backend is eligible.
- `ACCEPTANCE_GATE_STALE_HOURS`: default `72`, set in `hooks/acceptance-gate.sh` (`STALE_HOURS="${ACCEPTANCE_GATE_STALE_HOURS:-72}"`). Overriding it changes how long an abandoned session's acceptance contract keeps blocking `TaskUpdate → completed` calls repo-wide.

Re-verify: `printenv CLAUDE_CODE_DISABLE_WORKFLOWS; claude --version`; `grep STALE_HOURS hooks/acceptance-gate.sh`.

## skills/council/model-routing.json (OpenRouter task routing)

`tasks` block, consumed by `mcp/openrouter/routing.py` to resolve a task name to an OpenRouter vendor model ID, as of 2026-07-05:

```json
{
  "tasks": {
    "classification": "openai/gpt-5.4-nano",
    "scout-research": "google/gemini-3.5-flash",
    "scoring": "openai/gpt-5.4-mini"
  },
  "lenses": {},
  "defaults": { "lens": "claude", "fallback": "claude" }
}
```

- **Status**: `tasks` entries were refreshed off the 2024-era `gpt-4o-mini`/`gemini-flash-1.5` IDs to the fresh IDs above; #62/US-004 is closed (PR #70 merged). AC-010..012 (acceptance-contract.md) are all `verified`: `python3 -m pytest mcp/openrouter/tests/ -q` passes 31, skips 1, and a refresh procedure exists (`mcp/openrouter/check_models.py`, monthly + pre-caller cadence). Missing or invalid table entries still degrade to `claude` (`routing.py:19-25`), so staleness here fails soft, not hard.
- `lenses: {}` is still an empty stub; the "Phase 2 lens relay" (per-lens OpenRouter routing inside council rounds) is design-only and eval-gated, not implemented.
- **Schema expansion is on `main` since PR #72 merged (2026-07-05, commit `92e95d4`)**: the file carries `tiers`, `profiles` (`max-plan`, `api-billed`), 13 `spawn_sites`, and an `egress_policy.openrouter` block, validated by the hard pre-commit hook `check_model_routing.py`; AC-013..016 are `verified` in the acceptance contract. Re-verify with `jq 'keys' skills/council/model-routing.json` before citing the schema shape.

Re-verify: `cat skills/council/model-routing.json` (working tree); `git show main:skills/council/model-routing.json` (merged truth); `gh pr view 72 --json state`; `python3 -m pytest mcp/openrouter/tests/ -q` (routing unit tests, no network).

## pipeline/config/budgets.json (governance token budgets)

Consumed by `pipeline/hooks/_utils.py` (`load_budgets()`, `get_budget_limits()`) for the skill-governance token/word budget checks. Top-level limits: `coordinator_max_words: 600`, `specialist_max_words: 1500`, `reference_max_words: 1100`, `standalone_max_words: 1500`, `max_simultaneous_tokens: 5500` (spec version `1.3`).

`overrides` is a dict keyed by **exact repo-relative path**, matched via `get_budget_limits()`'s `if normalized in overrides` check: no globbing, no prefix matching. It holds 25 entries, all for soc-security skills (`threat-model-skill`, `verification-scaffold-skill`, `compliance-pipeline-skill`, etc.), each with a `max_words`/`max_simultaneous_tokens` and a `rationale` string. Every key is written as `skills/<name>/...`, but the real files live at `skills/soc-security/skills/<name>/...` (verified: `find skills/soc-security -maxdepth 1 -type d` shows a nested `skills/soc-security/skills/` directory). The keys therefore **never match**, and every soc-security skill silently falls back to the classification default (1500/2000 words for specialist) instead of its intended, often larger, override. This is currently harmless: `check_token_budget.py`'s own docstring states it is advisory, "WARN tier, always exits 0."

Re-verify orphaned keys: `python3 -c "import json,os; d=json.load(open('pipeline/config/budgets.json')); print([k for k in d['overrides'] if not os.path.exists(k)])"`. Re-verify enforcement tier: `tail -5 pipeline/hooks/check_token_budget.py` (look for the unconditional `sys.exit(0)` / lack of a nonzero exit).

## pipeline/config/model-routing.yaml (governance tier defaults, not wired)

Separate concept from `skills/council/model-routing.json` despite the shared filename fragment. Defines default model tiers per skill classification (`coordinator`/`specialist`/`standalone` → `sonnet`; `reasoning` task type → `opus`), budget-zone thresholds (`green: 0.70`, `yellow: 0.90`, `red: 1.00`), and a tier-to-Claude-Code-model-ID map (`sonnet` → `claude-sonnet-4-6`, etc.), per `pipeline/specs/SKILL-MODEL-ROUTING-SPEC.md`. `overrides: {}` is empty. **No `pipeline/hooks/*.py` script reads this file** (verified by grepping all hook scripts for `model-routing.yaml` and for `yaml` imports outside `check_frontmatter.py`, which parses skill frontmatter, not this file). Treat it as a documented-but-unenforced design artifact, not live config.

Re-verify: `grep -rl "model-routing.yaml" pipeline/hooks/*.py` (expect empty).

## pipeline/config/security-suppressions.json (not wired)

```json
{ "spec_version": "1.3", "suppressions": [], "_comment": "Per-file security check suppressions..." }
```

Schema for exempting specific files from a future security-scanning pre-commit hook, per `pipeline/specs/SKILL-SECURITY-SPEC.md`. No `check_security.py` exists in `pipeline/hooks/` today, so nothing reads or enforces this file: it is a schema stub for a hook that has not been built.

Re-verify: `ls pipeline/hooks/check_security.py 2>&1` (expect "No such file"); `jq .suppressions pipeline/config/security-suppressions.json` (expect `[]`).
