---
name: mcs-config-and-flags
description: Use when you need the current value, default, production/experimental/parked status, or enforcement guard for any Claude Code configuration axis in this repo, such as settings.json fields, env flags, permissions allow/deny lanes, hooks wiring, settings.local.json, council cost profiles, model-routing.json/yaml, budgets.json overrides, or security-suppressions.json, and when adding a brand-new configuration axis. Not for what a setting means at the Claude Code platform level (mcs-claude-code-platform) or for how a config change gets reviewed and merged (mcs-change-control).
---

# mcs-config-and-flags

## Overview

This repo's live config is scattered across `settings.json`, `hooks.json`, `.claude/settings.local.json`, `commands/council.md`, `commands/_council-engine.md`, `hooks/acceptance-gate.sh`, `skills/council/model-routing.json`, and `pipeline/config/{budgets,model-routing.yaml,security-suppressions}.json`. Several were rewritten by the `claude-config-model-optimization` campaign (issues #59-#66, completed 2026-07-06, PR train #67-#74). `settings.json` and `hooks.json` are symlinked into `~/.claude/` on this machine, so edits deploy to the live harness the instant they land, whether from a commit or the app itself. Treat every value below as a dated snapshot: run the paired re-verify command first.

## When to use and when NOT to

Use for: "what does this env var do here", "is this permission axis production or a parked experiment", "what model is the session actually pinned to", "what's the current council cost profile", "how do I add a new config knob without it rotting".

Route elsewhere for:
- **Platform semantics** (what a hook event/matcher/precedence rule means in Claude Code generally) → `mcs-claude-code-platform`.
- **How a change to these files gets classified, reviewed, or merged** → `mcs-change-control`.
- **Live triage of a broken hook or permission** → `mcs-debugging-playbook`.
- **Running council/ship/looper, where artifacts land** → `mcs-run-and-operate`.
- **Historical incidents behind an axis** (why the gate was rewired) → `mcs-failure-archaeology`.

## The axis catalog

Axis values snapshotted 2026-07-05; campaign status re-verified 2026-07-06: `main` merged through PR #74, all of US-001..US-008 closed (PR #72 landed US-005, PR #73 US-007 extraction, PR #74 US-008 HTML layer). "This machine only" marks facts tied to `/Users/danielsong/...` paths, never load-bearing for another clone.

| Surface | Axis | Current (2026-07-05) | Default | Status | Guard | Re-verify |
|---|---|---|---|---|---|---|
| settings.json | `model` | `opus` (tier alias) | unset (no pin) | production, hard-enforced (L1, PR #71/#64) | `check_settings.py` rule L1: rejects pinned `claude-*` IDs and bare `claude` | `grep -n TIER_ALIASES pipeline/hooks/check_settings.py` |
| settings.json | `env.CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS` | `"1"` | unset | production, required by council teams backend | none | `jq -r .env.CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS settings.json` |
| settings.json | `env.CLAUDE_CODE_DISABLE_1M_CONTEXT` | `"1"` | unset | production, deliberate (AC-005 verified) | `docs/model-routing.md` | `jq -r .env.CLAUDE_CODE_DISABLE_1M_CONTEXT settings.json` |
| settings.json | `env.CLAUDE_CODE_DISABLE_AUTO_MEMORY` | `"1"` | unset | production, deliberate (handover protocol wins) | none | `jq -r .env.CLAUDE_CODE_DISABLE_AUTO_MEMORY settings.json` |
| settings.json | `permissions.allow` | 27 entries, real workload | `[]` | production, PR #69 merged (US-003, shipped 2026-07-05) | none automated | `jq '.permissions.allow' settings.json` |
| settings.json | `permissions.deny` | 26 entries | `[]` | production | none automated | `jq '.permissions.deny' settings.json` |
| settings.json | `permissions.defaultMode` | `acceptEdits` | `default` (ask) | production | semantics: `mcs-claude-code-platform` | `jq -r .permissions.defaultMode settings.json` |
| settings.json | `effortLevel` | `high` | unset | production | none | `jq -r .effortLevel settings.json` |
| settings.json | `tui` | `fullscreen` | unset | production, app-written (`0954f52`) | none | `jq -r .tui settings.json` |
| settings.json | `statusLine.command` | claude-hud via bun | unset | production, this machine only | none | `jq -r .statusLine.command settings.json` |
| settings.json | `enabledPlugins` | 9 plugins | `{}` | production | none | `jq '.enabledPlugins' settings.json` |
| settings.json | `extraKnownMarketplaces` | `skill-codex` + `research-toolkit-local` (local dir, this machine only) | `{}` | production | none | `jq '.extraKnownMarketplaces' settings.json` |
| settings.json | `mcpServers.openrouter` | repo-local `.venv` interpreter, this machine only | absent | production, manual bootstrap; `OPENROUTER_API_KEY` unset in this shell (verified 2026-07-02) | `mcp/openrouter/README.md` | `test -x mcp/openrouter/.venv/bin/python && echo ok` |
| hooks.json | `PreCompact` → `pre-compact-handover.sh` | matcher `auto` | none | production | none | `jq '.hooks.PreCompact' hooks.json` |
| settings.json hooks | `PreToolUse` (`TaskUpdate`) → `acceptance-gate.sh` | live blocking gate | none | production | exit-2/stderr contract in script header | `jq '.hooks.PreToolUse' settings.json` |
| settings.json hooks | 5 events → `telemetry-dispatch.sh` | fail-soft dispatcher (US-001, PR #67, `c562ab8`) | none | production | self-guards, never exits 2 | `jq '.hooks.SessionStart' settings.json` |
| hooks/telemetry-dispatch.sh | `CLAUDE_TELEMETRY_HOOK` | unset (defaults to private-repo path, this machine only) | unset | production, optional | dispatcher's own readability check | `grep -n CLAUDE_TELEMETRY_HOOK hooks/telemetry-dispatch.sh` |
| .claude/settings.local.json | `permissions.allow` | 38 entries, accretion incl. debug junk | absent, gitignored | pattern is production; entries vary | none, "2-week" rule is unenforced | `jq '.permissions.allow \| length' .claude/settings.local.json` |
| commands/council.md | `DEFAULT_PROFILE` | `balanced` | `balanced` | production | none | `grep DEFAULT_PROFILE commands/council.md` |
| commands/_council-engine.md | cost-profile spawn-site table | sonnet/opus/fable per site | n/a | production | none | `grep -A10 "Cost Profiles" commands/_council-engine.md` |
| hooks/acceptance-gate.sh | `ACCEPTANCE_GATE_STALE_HOURS` | `72` (overridable) | `72` | production | script itself | `grep STALE_HOURS hooks/acceptance-gate.sh` |
| runtime env | `CLAUDE_CODE_DISABLE_WORKFLOWS` | unset (needs CC ≥2.1.154; here 2.1.198, verified 2026-07-02) | unset | production | `_council-engine.md:39` | `printenv CLAUDE_CODE_DISABLE_WORKFLOWS; claude --version` |
| skills/council/model-routing.json | `tasks.*` | fresh IDs (`openai/gpt-5.4-nano`, `google/gemini-3.5-flash`, `openai/gpt-5.4-mini`) | n/a | production, shipped (#62/US-004 closed, PR #70 merged) | AC-010..012 verified; `mcp/openrouter/check_models.py` (monthly + pre-caller cadence) | `cat skills/council/model-routing.json` |
| skills/council/model-routing.json | `lenses` | `{}` stub | `{}` | candidate, Phase-2 design-only | none | `jq '.lenses' skills/council/model-routing.json` |
| skills/council/model-routing.json | schema expansion (`tiers`/`profiles`/`spawn_sites`/`egress_policy`) | spec_version 2.0 on `main` (merged 2026-07-05) | n/a | production, #63/US-005 closed via PR #72 | `check_model_routing.py` (hard, pre-commit) | `gh pr view 72 --json state` |
| pipeline/config/budgets.json | `overrides` (25 soc-security entries) | **orphaned**: keys say `skills/<name>/...`, real path is `skills/soc-security/skills/<name>/...` | `{}` | known-wrong, low severity (WARN-tier, always exit 0) | `check_token_budget.py` | `python3 -c "import json,os;d=json.load(open('pipeline/config/budgets.json'));print([k for k in d['overrides'] if not os.path.exists(k)])"` |
| pipeline/config/budgets.json | `max_simultaneous_tokens` | `5500` | `5500` | production, enforcement truth | `check_token_budget.py` | `jq .max_simultaneous_tokens pipeline/config/budgets.json` |
| pipeline/config/model-routing.yaml | tier defaults, `overrides: {}` | defined, **not wired**: no hook reads it | n/a | documentation-only | none | `grep -rl "model-routing.yaml" pipeline/hooks/*.py` (expect empty) |
| pipeline/config/security-suppressions.json | `suppressions` | `[]` | `[]` | design-only, **not wired**: no `check_security.py` exists | none | `ls pipeline/hooks/check_security.py 2>&1` (expect "No such file") |

Full field lists live in `references/`: `settings-json.md` (settings.json + settings.local.json), `hooks-wiring.md` (both hook files, all 6 hooks, and the 2 that docs claim run but don't), `council-and-routing.md` (cost profiles, both model-routing files, budgets, suppressions), `adding-a-config-axis.md` (checklist).

## How to add a config axis (summary)

1. Pick the surface: session-wide default → `settings.json`; per-repo experiment → `.claude/settings.local.json`; council knob → `commands/council.md` or `_council-engine.md`; model routing → `skills/council/model-routing.json`; governance budget → `pipeline/config/budgets.json`.
2. Check `pipeline/hooks/` for whether a guard should exist: as of 2026-07-06 `settings.json` has a hard schema guard (`check_settings.py`, US-006/#64 closed, PR #71 merged) and `skills/council/model-routing.json` has a hard structural guard (`check_model_routing.py`, US-005/#63 closed, PR #72 merged); re-verify with `grep -A2 "id: settings-schema\|id: model-routing" .pre-commit-config.yaml`.
3. Document rationale in `docs/model-routing.md` (model/permission axes) or the relevant `commands/*.md` (council axes).
4. Add a row to this table with a re-verify command. Full checklist: `references/adding-a-config-axis.md`.

## Gotchas

- `settings.json` is the live global config via symlink (`~/.claude/settings.json -> settings.json`, this machine). WRONG: edit it directly to test a permission tweak. RIGHT: use `.claude/settings.local.json` (gitignored), promote via PR.
- Two files are both called "model routing" and do unrelated things: `skills/council/model-routing.json` (OpenRouter task routing) vs `pipeline/config/model-routing.yaml` (governance tier defaults, **not consumed by any hook**). Don't cite one for the other.
- `budgets.json`'s 25 soc-security override keys silently no-op: `get_budget_limits()` does exact-string path matching and the real files live one directory deeper than the keys assume. Harmless only because the hook is WARN-tier (always exits 0); promoting it to HARD-tier would misfire against every SoC-security skill.
- As of 2026-07-05, `settings.json` has a HARD pre-commit schema guard (`settings-schema` → `check_settings.py`, `files: ^settings\.json$`; issue #64/US-006 closed, PR #71 merged): it rejects non-tier-alias `model` values (L1), a stray `[1m]` suffix (L2), and private-repo paths in hook commands (L3). `skills/council/model-routing.json` similarly gained a HARD guard (`model-routing` → `check_model_routing.py`). Re-verify: `grep -A2 'id: settings-schema\|id: model-routing' .pre-commit-config.yaml`.
- `ARCHITECTURE.md`'s "Active Hooks" table lists only `PreCompact`, omitting the 6 hooks actually wired in `settings.json`. Don't treat it as source of truth for hook wiring; read `hooks.json` and `settings.json` directly.
- `hooks/careful-mode.sh`, `freeze-mode.sh`, `skill-telemetry.sh` exist but are registered in no settings file. `/careful` and `/freeze` only flip a state file; nothing checks it. Don't assume they protect anything.
- `ACCEPTANCE_GATE_STALE_HOURS`, `CLAUDE_TELEMETRY_HOOK`, `CLAUDE_CODE_DISABLE_WORKFLOWS` are env overrides absent from `settings.json` itself: grep the consuming script, not `settings.json`, for defaults.
- Numbers move mid-session: HEAD advanced `0954f52` (fable pin) → `a1a8a72` (tier alias, PR #68) → `105427a` → `d84b549` (permissions rewrite, PR #69) during authoring alone. Re-run the paired command; never trust a cached count.

## Provenance and maintenance

Last verified: 2026-07-05 (axis values); 2026-07-06 (campaign status: contract 26/26, issues #58-#66 all closed, PR train #67-#74 merged, `main` at `74e34c5`). During original authoring the branch under PR #72 kept moving mid-edit (`82292e1` → `f21fc8d`), which is itself the proof of the next bullet: numbers in this table move mid-session, always re-run the paired command rather than trusting the printed value.

Global re-verification, run before trusting any "current" value above:
- `git log --oneline -5 && git status` (confirm you're not on a stale snapshot).
- `gh pr list --state open` (which US-00x rewrites are in flight vs merged; do not assume a closed GitHub issue lags or leads a merge, check the PR directly).
- `gh issue list --search "council-claude-config-model-optimization" --state open` (which axes are still known-wrong-parked).
- `cat .claude/ship-state.md .claude/looper-state.md` (queue/phase truth for issues #59-#66).
