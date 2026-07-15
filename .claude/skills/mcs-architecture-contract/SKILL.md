---
name: mcs-architecture-contract
description: >-
  Use when you need to know WHY this repo is built the way it is, not just what a file contains:
  shared engine plus themed layer, symlink deployment, backend degradation (workflow to teams to
  sequential), fail-soft contracts, progressive skill loading, session-state layering, and which
  invariants are enforced-by-hook versus prose-only. Also use to check a known-weak-point first:
  routing truth on three surfaces, unsynced session state, private-repo coupling. Do NOT use for step-
  by-step procedures (mcs-run-and-operate) or generic Claude Code platform mechanics (mcs-claude-code-
  platform).
---

# mcs-architecture-contract

## Overview

This repo (`my-claude-setup`) is a prompt-driven Claude Code configuration system: markdown files ARE the runtime, there is no build step, and `~/.claude/settings.json` / `~/.claude/hooks.json` / `~/.claude/skills` are symlinks straight into this git working tree ("this machine only" fact, re-verify with `ls -la ~/.claude | grep -- '->'`). Every load-bearing decision below exists to keep that live-production surface fail-soft: a malformed hook, a missing sibling repo, or an unavailable runtime capability must degrade quietly, never hard-fail a session. Read this before changing `commands/_council-engine.md`, `settings.json`, `hooks.json`, or anything under `pipeline/hooks/`.

## When to use and when NOT to

Use when: reviewing a change that touches the engine/theme boundary, deciding whether a proposed change breaks an invariant, tracing why a symptom exists (state disagreeing across files, a hook that silently no-ops, a routing value that doesn't match another routing value), or scoping work that must not violate `pipeline/specs/SKILL-GOVERNANCE-SPEC.md`.

Route instead to:
- **mcs-run-and-operate**: how to actually run `/council`, `/ship`, `/looper`, `/handover`; where session artifacts land.
- **mcs-claude-code-platform**: generic Claude Code mechanics (hook event contract, Skill/Workflow tool semantics, settings precedence) that apply beyond this repo.
- **mcs-config-and-flags**: the full catalog of every configuration axis and its current value.
- **mcs-debugging-playbook**: live symptom-to-cause triage.
- **mcs-failure-archaeology**: the historical chronicle of what was already tried and reverted.

## System diagram (as of 2026-07-02)

```
 commands/council.md ──┐            commands/ece.md ──┐
  (theme: 14 vars)      │                (theme: 14 vars) │
                        ▼                                 ▼
            commands/_council-engine.md  (1753 lines, theme-agnostic
            Phase 0-5 orchestration, 8 modes, 3 cost profiles)
                        │
        ┌───────────────┼────────────────────┐
        ▼               ▼                    ▼
   agents/council-*.md  skills/council/<dept>/  workflow templates
   agents/ece-*.md      DEPARTMENT.md + SKILL.md  council-deliberation
   (no model: frontmatter)  (progressive loading)   .template.js /
                                                      council-audit
                                                      .template.js
                        │                             (Workflow tool,
                        ▼                              args = JSON obj)
         session artifacts (.claude/council/sessions/<slug>/):
         session.md, design.md, prd.md, acceptance-contract.md,
         issues.md, plus .claude/council/index.json (workspace)
         and ~/.claude/council/global-registry.json (cross-workspace)

 ── surrounding the whole stack ──
 settings.json (live via ~/.claude symlink: model, permissions, hooks,
   mcpServers), hooks.json (PreCompact only), pipeline/hooks/*.py
   (pre-commit, mostly ^skills/**/*.md, plus 2 single-file exceptions
   for settings.json and model-routing.json; CI runs none of them)
```

## Load-bearing decisions, with WHY

**1. Shared engine + themed layer.** `commands/_council-engine.md` (1753 lines, `wc -l commands/_council-engine.md`) holds all theme-agnostic Phase 0-5 orchestration, mode table, and the 3-tier cost-profile table. `commands/council.md` (337 lines) and `commands/ece.md` (266 lines) each supply the same 14 config variables (`THEME_ID`, `THEME_NAME`, `INTAKE_PROMPT`, `AGENT_FILE_PREFIX`, `CONDUCTOR_PERSONA`, `SESSION_DIR_ROOT`, `TEAM_PREFIX`, `GLOBAL_REGISTRY_PATH`, `INDEX_PATH`, `CHALLENGE_RULES`, `DEFAULT_PROFILE`, `EXTRA_MECHANICS`, plus phase labels and roster), ending "Follow all instructions in `commands/_council-engine.md`, substituting the theme variables defined above" (`council.md:337`, `ece.md:266`). WHY: a third theme costs one new command file, zero engine edits.

**2. Prompt-driven, no build step.** Markdown files are the executable artifact. The only non-markdown runtime pieces are two Workflow-tool JS templates (`skills/council/references/workflows/*.template.js`) and the OpenRouter MCP server (`mcp/openrouter/`). WHY: zero compile/deploy latency between edit and effect, which is what makes decision 3 safe to rely on.

**3. Symlink deployment model.** `~/.claude/settings.json -> repo/settings.json`, plus `hooks.json`, `skills`, `commands`, `agents` (verify: `ls -la ~/.claude`, this-machine-only fact). WHY: editing this repo IS editing the live global config, no staging, no gate before the next tool call. This is why fail-soft (decision 5) is non-negotiable.

**4. Backend degradation chain: workflow -> teams -> sequential.** Preflight (`commands/_council-engine.md:34-46`) detects `CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1` for teams and Workflow-tool availability (requires Claude Code >= 2.1.154) for workflows, "never hard-exits here" (engine:36). `workflow` modes degrade workflow -> teams -> sequential (engine:42); `teams-preferred` phases degrade teams -> workflow/sequential (engine:43). A workflow invocation that fails at runtime is itself treated as a detection signal and triggers the next degradation step (engine:39). The resolved backend is printed once and recorded in `session.md`'s `Backend:` field.

**5. Fail-soft everywhere.** Four independently-verified cases of the same contract: OpenRouter `consult()` never raises, every failure returns `{"error", "error_kind", "fallback": "claude"}` (`mcp/openrouter/openrouter_client.py:69-117`); `hooks/telemetry-dispatch.sh` (shipped 2026-07-02, PR #67/#59) exits 0 silently if the private hook is missing and never exits 2 (on `Stop`, exit 2 would block Claude from stopping); `hooks/acceptance-gate.sh` treats a hook-input parse failure as `exit 0` allow, not a block (`acceptance-gate.sh:20-21`); the workflow templates tolerate a JSON-stringified `args` payload rather than throwing (`council-deliberation.template.js:32-35`, PR #56/`01b6081`). WHY: each sits on the hot path of ordinary tool use in a live symlinked config; a hard failure here breaks every subsequent tool call, not just the current one.

**6. Progressive skill loading.** Coordinator (`SKILL.md`, target <=800 tokens) routes to Layer 2 specialists (target <=2000 tokens), which reference Layer 3 files (target <=1500 tokens) loaded within a procedure step. Per-file targets are **guideline**, not hard limits: the only hard limit is the suite context-load ceiling of **5500 tokens** (`pipeline/config/budgets.json:11`; enforced by `check_context_load.py`, hard tier). The user's own global `CLAUDE.md` states the ceiling informally as "~5,000 tokens"; that number is stale against enforced 5500, which is the enforcement truth.

**7. Session-state layering.** Three surfaces, written at different points, never reconciled: `session.md` (per-session phase/backend/profile), `.claude/council/index.json` (workspace roster), `~/.claude/council/global-registry.json` (cross-workspace, keyed by absolute workspace path). This is why a session run from a different repo can leave usage entries in this repo's `registry.json`: `~/.claude/skills` symlinks here, and the registry is shared across every workspace on the machine.

## Invariants and their enforcement status

Six invariants matter most; full evidence and re-verification commands are in `references/invariants-enforcement.md`.

| Invariant | Status |
|---|---|
| Tier-alias-only model references, never pinned `claude-*` IDs | prose-only (no validator covers `agents/`) |
| Agents omit `model:` frontmatter | true today, unenforced |
| One specialist loaded at a time; no cross-specialist references | enforced-by-hook (structure) / prose-only (loading discipline) |
| Eval cases live outside skill directories | contradicted in practice by 9 council departments; not enforced |
| Workflow `args` passed as a real JSON object, never a string | prose-instructed; code tolerates a string and degrades gracefully |
| Blocking hooks require `PreToolUse` + `exit 2` + stderr | platform semantics, documented via two repeat incidents, not self-checking |

## Known-weak points (as of 2026-07-05)

Full detail and re-verification commands are in `references/known-weak-points.md`.

1. **Routing truth on 3 surfaces, third now schema-full and hook-enforced** (`settings.json` model, engine cost-profile prose, `model-routing.json` v2.0 with `tiers`/`spawn_sites`/`egress_policy`, guarded by hard hook `check_model_routing.py`): US-005/#63 content is done on branch `feat/63-unified-routing-table` behind open PR #72; issue #63 stays `OPEN` until that PR merges to main.
2. **Session state on 3 unsynced surfaces** (`session.md`, `index.json`, global registry): `index.json` shows `contract_issue: null` while `issues.md` already lists real issues.
3. **Private-repo coupling**: US-001/#59 (merged PR #67) made the 5 telemetry events fail-soft; US-007/#65 (dormant-suite extraction) landed via PR #73, leaving only gitignored symlinks pointing at the private repo.
4. **Registry telemetry durable for one day only** (`dc44611`, 2026-07-02): short of the 2-4 week window the design doc requires before pruning.
5. **`/careful` and `/freeze` are unwired**: `check` hooks aren't registered anywhere, and use the wrong (env-var, not stdin-JSON) interface even if they were.
6. **Spec-promised hooks that don't exist**: `check_security.py`, `check_triggers.py`, documented in the security/trigger specs, absent from `pipeline/hooks/`.
7. **Governance validators cover `^skills/` almost exclusively; CI runs none of them**: two new single-file exceptions (`settings-schema` on `settings.json`, `model-routing` on `skills/council/model-routing.json`) landed via PR #71/#72, but `agents/`, `commands/`, `pipeline/`, `hooks/` stay outside every glob, and `validate.yml` never invokes `pre-commit` or any `check_*.py`.

## Gotchas

- WRONG: assuming `council.md`/`ece.md` duplicate logic. RIGHT: only the 14-variable header duplicates; all behavior lives once in `_council-engine.md`, so a fix there fixes both themes.
- WRONG: treating a workflow-tool failure as a hard stop. RIGHT: it's a detection signal that re-resolves the backend one rung down; check `session.md`'s `Backend:` line before assuming a bug.
- WRONG: reading `registry.json` as a trustworthy usage signal. RIGHT: write-mostly telemetry, one day of durable history as of 2026-07-02; the directory tree plus each `DEPARTMENT.md` is authoritative.
- WRONG: assuming a hook that warns and exits 1 blocks anything. RIGHT: only `PreToolUse` + `exit 2` + stderr blocks. This exact mistake shipped and merged once already (incident `605112d`).
- WRONG: believing `/careful` or `/freeze` add protection because the command prints "enabled". RIGHT: their `check` hooks are never registered, and would no-op on a stdin/env mismatch anyway.
- WRONG: citing eval-cases-outside-skill-dirs as a compliance guarantee because the spec marks it "Hard". RIGHT: zero hook coverage, and 9 council departments already violate it in the committed tree.
- WRONG: assuming `settings.json`, the engine's cost table, and `model-routing.json` agree on routing. RIGHT: three different surfaces; `model-routing.json` is now the schema-full, hook-enforced one, but the other two are still separate prose/config sources (US-005/#63 content done, PR #72 open, not yet merged to main).
- WRONG: editing `settings.json` here "just to test something locally." RIGHT: it's the live global config via symlink, no staging gate; every edit lands on the next tool call.

## Provenance and maintenance

Last verified: 2026-07-06, `main` at `74e34c5` (campaign closeout: PR train #67-#74 all merged, issues #58-#66 closed, contract 26/26 verified).

Re-verification commands:
- Engine/theme line counts: `wc -l commands/_council-engine.md commands/council.md commands/ece.md`
- Symlink deployment (this-machine-only): `ls -la ~/.claude | grep -- '->'`
- Suite ceiling hard limit: `grep max_simultaneous_tokens pipeline/config/budgets.json`
- Current settings.json model value: `grep '"model"' settings.json`
- US-005/US-007 landing status: `gh issue view 63 --json state,title` / `gh issue view 65 --json state,title`, and `gh pr view 72 --json state,title` for the PR itself (or `cat .claude/ship-state.md` for the local queue snapshot)
- All pre-commit hook file globs (confirms the 2 exceptions to `^skills/`): `grep -n 'files:' .pre-commit-config.yaml`
- Deep invariant/weak-point re-checks: see `references/invariants-enforcement.md` and `references/known-weak-points.md`
