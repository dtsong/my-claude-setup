---
name: mcs-claude-code-platform
description: >-
  Use when you need Claude Code platform mechanics as this repo actually wires them: writing or
  debugging a hook (stdin JSON payloads, which event plus exit code plus stream combination actually
  blocks), reading settings.json versus settings.local.json versus hooks.json, understanding why a
  skill or command loads twice, registering or calling an MCP server, or checking Workflow tool and
  agent-teams preflight. Not for this repo's commit rules and acceptance-gate incident history (mcs-
  change-control), the full config/flag value catalog (mcs-config-and-flags), or symptom-to-cause
  triage (mcs-debugging-playbook).
---

# mcs-claude-code-platform

## Overview

Claude Code loads config, hooks, skills, and MCP servers from specific files with specific contracts. Get a contract wrong (stdin JSON vs. env vars, exit code vs. output stream) and the failure is silent, not loud. This repo has shipped both failure modes in production (see Gotchas), so every mechanism below carries the repo evidence that proves it.

This machine has `~/.claude/settings.json`, `~/.claude/hooks.json`, `~/.claude/hooks`, `~/.claude/skills`, `~/.claude/agents` all symlinked into this repo (verified 2026-07-02). Editing the repo file edits the live global config, no staging step.

## When to use, and when NOT to

Use this skill for *how the platform mechanism works*, illustrated with this repo's wiring. Route elsewhere for:

- Why these hooks/non-negotiables exist, incident rationale, commit conventions → `mcs-change-control`
- Live symptom → cause triage ("my hook isn't firing") → `mcs-debugging-playbook`
- Full current value of every config axis (permissions lists, env vars, model pin) → `mcs-config-and-flags`
- Historical narrative of what was tried and reverted → `mcs-failure-archaeology`
- System-level design rationale (why shared-engine-plus-theme, why symlink deploy) → `mcs-architecture-contract`
- Running `/council`, `/ship`, `/looper` end to end → `mcs-run-and-operate`

## 1. Hook system contract

Two registration surfaces, both live simultaneously: `settings.json`'s `"hooks"` key (`PreToolUse` on matcher `TaskUpdate` → `acceptance-gate.sh`; five telemetry events, matcher `""`, → `telemetry-dispatch.sh`; `settings.json:60-131`) and a separate `hooks.json` (`PreCompact`, matcher `"auto"`, → `pre-compact-handover.sh`; `hooks.json:1-13`). `install.sh` has independent opt-in flags `--with-settings`/`--with-hooks-json` for linking each (`install.sh:45-46`), confirming they're two distinct surfaces, not aliases.

**Payload delivery is stdin JSON, not environment variables.** `acceptance-gate.sh` and `pre-compact-handover.sh` both `INPUT=$(cat)` and parse JSON out of it. Three scripts still read `TOOL_NAME`/`TOOL_INPUT`/`FILE_PATH` as env vars (`careful-mode.sh`, `freeze-mode.sh`, `skill-telemetry.sh`), and none is registered anywhere (grepped 2026-07-02: zero hits in `settings.json`, `hooks.json`, `.claude/settings.local.json`). `/careful`/`/freeze` only run `enable` (touches a state file); nothing calls `check`.

**Blocking semantics**, the single fact that fails silently if you get it wrong:

| Event | Exit + stream | Blocks? |
|---|---|---|
| `PreToolUse` | exit `2`, stderr | **Yes**, denies the tool, stderr fed back to Claude |
| `PreToolUse` | any other non-zero | No, logged, non-blocking |
| `PostToolUse` | any exit, any stream | **Never**, tool already ran |
| `PostToolUseFailure` | n/a | Registered here (`settings.json:104-112`) and listed in this repo's schema enum (`pipeline/config/settings.schema.json:28`, as of 2026-07-05); not confirmed as a **platform**-documented event name from repo files alone, re-verify: `grep -n PostToolUseFailure pipeline/config/settings.schema.json settings.json` |
| `PreCompact` | n/a | Not blocking; side-effect script only on `matcher: "auto"` |
| `SessionStart`/`Stop`/`SessionEnd` | n/a | Side-effect only here (telemetry); never used to block |

Encoded lesson (`acceptance-gate.sh:7-10`, fixed by commit `605112d`): the gate was originally `PostToolUse` + stdout + exit `1`, non-blocking by construction, so `TaskUpdate → completed` slipped through and the gate was pure decoration. Fixed by moving to `PreToolUse` + stderr + exit `2`.

**Matchers used here:** bare tool name (`"TaskUpdate"`), empty string (all tools), or for `PreCompact` the literal trigger value `"auto"`. No regex/pipe matcher syntax appears in this repo.

Full event table, script inventory, and the `grep -c || echo 0` double-counting pitfall (`4bb8bf2`) with a WRONG/RIGHT pair: `references/hook-events-and-blocking.md`.

## 2. Settings precedence and layering

Three files: `settings.json` (repo root, symlinked to `~/.claude/settings.json` here) is the global baseline, holding `env`, `permissions.{allow,deny,defaultMode}`, `hooks`, `mcpServers`, `enabledPlugins`, `extraKnownMarketplaces`, `model`. `.claude/settings.local.json` is project-local `permissions.allow` accretion only (39 entries, verified 2026-07-02); no `deny`/`hooks`/`defaultMode` override observed there. `hooks.json` is hook-only (Section 1).

Exact cross-layer precedence is platform behavior this repo doesn't implement or override. Don't state a specific ordering as repo-verified; confirm against current docs. Directly observable instead: local entries add permissions the global file doesn't grant (e.g. `Bash(chmod +x:*)` locally vs. `Bash(chmod *)` denied globally, `settings.json:55`), additive on a narrower pattern, not a blanket override.

`install.sh` does **not** symlink `settings.json`/`hooks.json`/`CLAUDE.md` by default (opt-in flags only); default `skills/` linking is per-skill-pack, `commands/`/`agents/` linking is per-file (`install.sh:150-167`). This machine's whole-directory symlinks for `skills`/`agents`/`hooks` are a manual, this-machine-only convenience, not the installer's default. Don't assume a fresh install looks the same.

Full axis catalog and MCP registration detail: `references/settings-mcp-registration.md`. Current values for every axis: `mcs-config-and-flags`.

## 3. Skill and command discovery

Only the frontmatter `description` field loads into context up front; the body loads on invocation. Proven directly in this authoring session: every skill/command listed by name only, until a `Skill` tool call loaded one. `commands/*.md` files feed the **same** discovery list as `skills/*/SKILL.md`, confirmed by exact correspondence between all 29 `commands/*.md` basenames and one block of this session's own available-skills list.

**Double-registration, proven:** `skills/heavy-file-ingestion/SKILL.md` (full skill, real body) and `commands/heavy-file-ingestion.md` (4-line stub whose body is "invoke the `heavy-file-ingestion` skill") both appeared as **separate entries** in this session's own list, both paying their own description-token cost every session. `council`/`ece` also shadow both surfaces, but that's a coordinator-command-plus-large-department-tree pattern, not a duplicate-description one. Don't conflate the two.

Plugin/marketplace skills load namespaced `<plugin>:<skill>` (observed: `superpowers:brainstorming`, `research-toolkit:generate-diagram` from the local-directory marketplace, `settings.json:155-160`). As of 2026-07-02: 9 `enabledPlugins`, 2 `extraKnownMarketplaces`. Re-verify before citing, this drifts.

`pipeline/hooks/check_frontmatter.py` enforces `description` ≥10 words (`MIN_DESCRIPTION_WORDS = 10`, line 24) and kebab-case `name`, but only on `^skills/.*\.md$` per `.pre-commit-config.yaml`. **`commands/*.md` and `agents/*.md` frontmatter is validated by nothing.**

Full loading detail, plugin-namespacing mechanics, install.sh symlink granularity: `references/skill-loading-and-agents.md`.

## 4. MCP servers

One registered: `mcpServers.openrouter` (`settings.json:169-178`). Stdio transport; `command` points at the repo-local venv interpreter `mcp/openrouter/.venv/bin/python`, not bare `python3`. The venv is a required manual one-time bootstrap, absent = `FileNotFoundError` (already bootstrapped on this machine). `${OPENROUTER_API_KEY}` env passthrough is substituted from the launching shell at spawn time, never written to a repo file; unset in this environment as of 2026-07-02, so the server returns its `missing_key` fallback until exported. FastMCP's single `consult(...)` tool (`server.py:21-38`) surfaces as `mcp__openrouter__consult`, an instance of the general `mcp__<server-key>__<tool-name>` pattern. Fail-soft contract (`{"error","error_kind","fallback":"claude"}`, never raises) is this server's own design choice, not a platform guarantee.

Full detail and the "adding a second server" checklist: `references/settings-mcp-registration.md`.

## 5. Workflow tool and agent teams

`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` set in `settings.json:3`. The council engine's preflight (`commands/_council-engine.md:34-46`) never hard-exits. It detects teams via `printenv`, detects the Workflow tool plus `CLAUDE_CODE_DISABLE_WORKFLOWS` unset (engine states a ≥2.1.154 version floor, repo-stated, not independently platform-confirmed here; this machine's `claude --version` is `2.1.198`, above it), and treats a failed workflow invocation itself as the unavailability signal, degrading **workflow → teams → sequential**.

**Args-as-object:** passing `args` as a JSON-encoded string throws `requires args: sessionDir, idea, roster[]`, because the whole payload arrives as one string with none of the expected keys present (`commands/_council-engine.md:689`). PR #56 / `01b6081` added a defensive parse in the templates (`typeof args === 'string' ? JSON.parse(args) : (args || {})`), tolerated at the script level, but the engine still instructs callers to pass a real object. Don't rely on the tolerance.

Full args schema and degradation detail: `references/skill-loading-and-agents.md`.

## 6. Subagent types

`agents/*.md` files (38 on disk) carry only `name` + `description` frontmatter; zero of 23 council agent files have `model:` (`grep -l "^model:" agents/*.md` → 0 hits). The file's `name:` value is the exact string the engine passes as `subagent_type` at every Task-tool spawn site (`commands/_council-engine.md:622-628`); model selection happens entirely at the spawn site via a cost-profile table, tier aliases only, never a pinned ID. Whether the platform mechanically resolves `subagent_type` by scanning `agents/*.md` is **not verifiable from repo files alone**, platform-internal behavior the repo relies on without implementing; its evidence is behavioral (documented sessions with per-agent round files), not a static proof.

Full detail: `references/skill-loading-and-agents.md`.

## Gotchas

- **WRONG:** blocking hook on `PostToolUse` printing to stdout, exit 1. **RIGHT:** `PreToolUse` + stderr + exit 2. Anything else silently logs and does not block (the `605112d` incident, real in this repo).
- **WRONG:** `COUNT=$(grep -c pattern file || echo 0)`. **RIGHT:** `COUNT=$(grep -c pattern file 2>/dev/null) || COUNT=0`. `grep -c` exits 1 on zero matches while still printing `0`, so the first form appends a second value (`4bb8bf2`).
- **WRONG:** assume `/careful`/`/freeze` protect anything, or that `skill-usage-report.sh` reads live data. All three depend on hooks (`check` entrypoints, `skill-telemetry.sh`) that are registered nowhere.
- Editing repo `settings.json` "just to test" is not a sandboxed edit: on any machine where it's symlinked into `~/.claude/`, that's a live global config change, no staging.
- `PostToolUseFailure` is registered and wired to telemetry here (`settings.json:104-112`) and listed in the schema enum (`pipeline/config/settings.schema.json:28`, as of 2026-07-05), but its platform-documented status is unconfirmed from repo files. Don't assume it behaves like `PostToolUse`.
- Deleting `mcp/openrouter/.venv` as build junk kills the MCP server; it's the exact configured interpreter, not disposable.
- A skill and a command can share a name (`heavy-file-ingestion`) and both cost description tokens every session. Descriptions aren't deduplicated by name.

## Provenance and maintenance

Last verified: 2026-07-02, branch `feat/61-permissions-rewrite` (HEAD `105427a`), by direct inspection of `settings.json`, `hooks.json`, `hooks/*.sh`, `install.sh`, `commands/_council-engine.md`, `agents/*.md`, `mcp/openrouter/`, and git history (`605112d`, `4bb8bf2`, `01b6081`).

Re-verification commands (repo root):

- Hooks: `python3 -m json.tool settings.json | grep -A2 '"hooks"'` and `cat hooks.json`
- Dead scripts: `grep -rl "careful-mode\|freeze-mode\|skill-telemetry" settings.json hooks.json .claude/settings.local.json`
- Symlinks: `ls -la ~/.claude/settings.json ~/.claude/hooks.json ~/.claude/skills ~/.claude/agents`
- Plugins/MCP: `python3 -c "import json;d=json.load(open('settings.json'));print(d['enabledPlugins'],d['mcpServers'])"`
- Version vs. Workflow floor: `claude --version` against `commands/_council-engine.md:39`
- Agents: `ls agents/*.md | wc -l && grep -l "^model:" agents/*.md | wc -l`
- Incident commits present: `git log --oneline | grep -E "605112d|4bb8bf2|01b6081"`
