# PRD: Claude Code Configuration + Model Optimization

## Overview

One ungated MVP PR-train of eight user stories that corrects configuration defects, unifies model routing into a single schema-validated source of truth spanning both billing profiles (Max plan and API-billed), extracts dormant capability to the private sibling repo, and adds an HTML presentation layer to the council engine. None of these stories flips live model behavior; eval-gated activation (12-case smoke set, 38-case golden harness) is deliberately out of this PRD and lands in v1.1.

Design source: `.claude/council/sessions/claude-config-model-optimization-20260702-0003/design.md` (committed c26cf08, F10 addendum after).

## Goals

- Zero self-contradictions in `settings.json` (model pin vs env flags, governance compliance)
- Every spawn site has documented model routing for both max-plan and api-billed profiles
- The telemetry hook survives a clean clone without `my-claude-setup-private`
- Permission prompts drop by ~50% via an allowlist that matches the real bash/python/gh workload
- Dormant suites (ECE, resume-tailor, soc-security, docx-to-pdf) leave this repo with a preserved record
- OpenRouter config carries current model IDs and a refresh mechanism so IDs never rot again
- Council design-approval touchpoints render an HTML verdict page

## Non-Goals

- No live model flips: no `routed_consult` callers, no `/ship`/`/looper`/council-profile model changes (v1.1, gated by F11 smoke eval)
- No OpenRouter Phase 2 lens relay (F6: future, gated by 38-case harness + egress safeguards)
- No council-skill pruning (deferred: durable telemetry increment + 2-4 week window first)
- No new data/ML skills (F8: unvalidated demand)
- No F3b telemetry hardening (vendoring, batching, alert tuning: v1.1)

## Quality Gates

- `pre-commit run --all-files` passes (token budgets, frontmatter, reference integrity, isolation, secrets)
- `python3 -m pytest mcp/openrouter/tests/ -q` passes where OpenRouter files are touched
- Repo has NO tsc/eslint surface (bash/python/markdown); stating this explicitly is the required verification posture per CLAUDE.md directive 2

## User Stories

### US-001: Fail-soft telemetry dispatcher (F3a)
**Description:** As a user of this config on any machine, I want the session telemetry hook to no-op cleanly when the private repo is absent so that fresh clones and the API work account stop erroring on every tool call.
**Agent:** Operator
**Acceptance Criteria:**
- [ ] AC-001: `hooks/telemetry-dispatch.sh` exists; it resolves the private hook path from `CLAUDE_TELEMETRY_HOOK` (default `$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py`), exits 0 silently if the file is missing, otherwise execs `python3` on it with all arguments forwarded
- [ ] AC-002: All five hook events in `settings.json` (SessionStart, PostToolUse, PostToolUseFailure, Stop, SessionEnd) invoke the dispatcher; the string `my-claude-setup-private` no longer appears in `settings.json`
- [ ] AC-003: With the private path unset/missing, the dispatcher exits 0 with no output and no python3 spawn

### US-002: Session default model to tier alias, 1M conflict resolved (F1)
**Description:** As the config owner, I want `settings.json.model` to hold a governance-compliant tier alias so that the default stops violating the repo's own alias-only rule and stops self-cancelling against `CLAUDE_CODE_DISABLE_1M_CONTEXT=1`.
**Agent:** Architect
**Acceptance Criteria:**
- [ ] AC-004: `settings.json.model` is a tier alias (`opus`) with no `[1m]` suffix and no pinned `claude-*` ID
- [ ] AC-005: The 1M-context stance is one deliberate state: `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` retained AND no `[1m]` suffix anywhere in `settings.json`
- [ ] AC-006: The routing doc (US-005) records the escalation rule: opus daily, fable ceiling on Max; sonnet on API

### US-003: Permissions allowlist rewrite + experiment lane (F2)
**Description:** As a daily user, I want the allowlist to encode the repo's real bash/python/markdown workload so that routine commands stop prompting and intent is explicit.
**Agent:** Craftsman
**Acceptance Criteria:**
- [ ] AC-007: Allow entries cover `Bash(pre-commit run *)`, `Bash(pytest *)`, `Bash(python3 *)`, `Bash(gh *)`, `Bash(jq *)`, and Write scopes for `agents/**`, `commands/**`, `skills/**`, `hooks/**`, `pipeline/**`; the imagined-TS entries (`Write(src/**)`, `Write(tests/**)`) are removed or justified in a comment-adjacent doc
- [ ] AC-008: Deny list is preserved intact (no weakening of secrets/rm -rf/sudo/curl-pipe rules)
- [ ] AC-009: `.gitignore` covers `settings.local.json` and the routing doc describes the experiment-lane convention

### US-004: OpenRouter model ID refresh + rot prevention (F4)
**Description:** As the API-account owner, I want current OpenRouter model IDs and a refresh mechanism so that the cheap path cannot silently 404 into the expensive fallback.
**Agent:** Scout
**Acceptance Criteria:**
- [ ] AC-010: `skills/council/model-routing.json` contains no 2024-era IDs (`gpt-4o-mini`, `gemini-flash-1.5` gone); replacements are validated against a live `list_models()` call at implementation time
- [ ] AC-011: A refresh mechanism exists: script or documented `list_models()` procedure that flags stale/unknown IDs, wired into pre-commit or a documented cadence
- [ ] AC-012: `python3 -m pytest mcp/openrouter/tests/ -q` passes with the new IDs

### US-005: Unified two-account routing table (F5)
**Description:** As the config owner, I want one schema-validated routing source of truth keyed by spawn site and billing profile so that the same decision stops living in three vocabularies.
**Agent:** Oracle
**Acceptance Criteria:**
- [ ] AC-013: `skills/council/model-routing.json` extended with `tiers`, `profiles` (`max-plan`, `api-billed`), `spawn_sites` (session_default, council.lean/balanced/max, brainstorm, challenge, audit, ship_implement, ship_review, looper, subagent, routed_consult, cheap_tasks), and `egress_policy` (send_allowlist, zdr, no_train, audit_actual_model, kill_switch per external destination)
- [ ] AC-014: A validation test rejects pinned `claude-*` IDs in Claude-tier alias slots, asserts every spawn site has an entry for every profile, and fails on external destinations lacking an egress_policy
- [ ] AC-015: A routing design doc (`docs/model-routing.md` or equivalent) renders the full spawn-site x profile table including the Max-plan rule (cheap tasks -> Haiku 4.5 in-family, NOT OpenRouter) and API rule (sonnet default, OpenRouter Pattern B trial behind cost ceiling)
- [ ] AC-016: `_council-engine.md` cost-profile section references model-routing.json as source of truth (generated from or validated against it)

### US-006: settings.json schema guard (Skeptic non-negotiable)
**Description:** As the owner of live symlinked production config, I want pre-commit JSON-schema validation of settings.json so that a malformed edit cannot reach the running harness.
**Agent:** Skeptic
**Acceptance Criteria:**
- [ ] AC-017: A JSON-schema for settings.json exists (model must match alias pattern, hooks/permissions/env shapes validated) and a pre-commit hook validates the file against it
- [ ] AC-018: The hook fails on: pinned `claude-*` model IDs, `[1m]` suffixes, absolute private-repo paths in hook commands
- [ ] AC-019: `pre-commit run --all-files` passes on the final tree

### US-007: Dormant suite extraction (F7)
**Description:** As the repo owner, I want ECE, resume-tailor, soc-security, and docx-to-pdf moved to `my-claude-setup-private` so that this repo carries only active-workload capability while the record is preserved.
**Agent:** Architect
**Acceptance Criteria:**
- [ ] AC-020: Pre-flight: all references grepped and enumerated (`/ece` command body, ece registry, cross-links, README mentions); `/ece` vs `_council-engine.md` coupling documented before the cut
- [ ] AC-021: Suites moved to `my-claude-setup-private` in one atomic commit here (15 `ece-*` agents, ece skills + command, resume-tailor, soc-security, docx-to-pdf); a manifest/pointer section lands in this repo's README
- [ ] AC-022: Reference-integrity pre-commit hook passes after extraction; no dangling references remain
- [ ] AC-023: No secrets travel with the suites (secrets scan on the private-repo commit)

### US-008: HTML presentation layer for council touchpoints (F10)
**Description:** As a council user, I want the design-approval touchpoint to render a self-contained HTML verdict page so that I review tensions, routing, and decisions visually instead of in a text wall.
**Agent:** Advocate-style task, assigned Craftsman
**Acceptance Criteria:**
- [ ] AC-024: `_council-engine.md` synthesis touchpoint instructs the conductor to generate `design.html` from the synthesis payload (overview, tracks, tension resolutions, decision log) and `open` it before the AskUserQuestion approval
- [ ] AC-025: A reference template exists (derived from this session's `design.html`: lens-color system, tension ledger, decision table) under `skills/council/references/`, within governance token budgets for reference files or stored as a pure HTML asset exempt from prose budgets
- [ ] AC-026: AskUserQuestion remains the approval mechanism; HTML generation failure degrades gracefully to the text-only flow

## Technical Notes

- Ship order: US-001 -> US-002 -> US-003 -> US-004 -> US-005 -> US-006 -> US-007 -> US-008. US-001 first (US-005 metrics and US-007 records depend on the telemetry pipeline surviving). US-006 depends on US-002 (schema encodes the alias rule). US-005 depends on US-004 (table carries fresh IDs).
- `settings.json` is live via the `~/.claude/settings.json` symlink: every merge is a production deploy. Rollback = `git checkout settings.json`.
- Uncommitted settings.json diff on main (model pin + tui/skipWorkflow keys) must be reconciled by US-002, not clobbered.
- Repo verification surface is pre-commit + pytest only; there is no tsc/eslint here.

## Dependencies

- `my-claude-setup-private` sibling repo must exist and be writable (US-001 default path, US-007 destination)
- `gh` CLI authenticated (issue export + /ship)
- `OPENROUTER_API_KEY` available for the `list_models()` validation in US-004 (fallback: document candidates and mark pending-live-check)
