---
name: mcs-model-routing-campaign
description: Use when consulting or extending the model-routing unification and OpenRouter multi-model council campaign in this repo (US-001..US-008, GitHub issues 59 to 66, council session claude-config-model-optimization-20260702-0003; track 1 completed 2026-07-06), checking phase state before touching .claude/ship-state.md or .claude/looper-state.md, mapping an issue to its acceptance criterion and test command, extending skills/council/model-routing.json, or judging whether OpenRouter Phase 2 lens-relay prerequisites (38-case harness, egress gates, fresh IDs, API key) are met. Not for generic ship/looper mechanics with no campaign context (mcs-run-and-operate), the full settings.json config-axis catalog (mcs-config-and-flags), or commit/PR review rules (mcs-change-control).
---

# Model Routing Campaign

## Overview

This is the executable runbook for the one live campaign that unifies model routing (currently split across `settings.json.model`, the engine's cost-profile prose, and `skills/council/model-routing.json`) and gates OpenRouter multi-model council behind evals. Core principle: track 1 (US-001..US-008, config hygiene + a routing design doc) ships ungated because it changes no live model behavior; track 2 (live model flips, OpenRouter Phase 2 lens relay) is eval-gated and stays gated no matter how tempting a shortcut looks.

## When to use, and when NOT to

Use when about to touch: `.claude/ship-state.md`, `.claude/looper-state.md`, `skills/council/model-routing.json`, `mcp/openrouter/`, issues #58-#66, or the council session `claude-config-model-optimization-20260702-0003`.

Route elsewhere for non-campaign questions:
- Generic `/ship` or `/looper` mechanics with no campaign context → **mcs-run-and-operate**.
- "What does config axis X do / what's its default" → **mcs-config-and-flags**.
- "Is this commit message right / can I force-push / did the gate block me correctly" → **mcs-change-control**.
- "Why does this hook silently no-op" → **mcs-debugging-playbook**.
- "Has this been tried before" (Fable pin history, registry.json saga) → **mcs-failure-archaeology**.

## Phase 0: Orientation gate (run first, every time)

```bash
cd /path/to/my-claude-setup   # repo root
git branch --show-current && git log origin/main..HEAD --oneline
tail -1 .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md
gh issue list --label council-claude-config-model-optimization --state all --json number,title,state
sed -n '1,20p' .claude/ship-state.md
cat .claude/looper-state.md 2>/dev/null | sed -n '1,15p'
gh pr list --state open --json number,title,headRefName,mergeable,statusCheckRollup
```

**Observed 2026-07-06 (campaign closeout), for calibration only (re-run, don't trust these verbatim):** contract `Progress: 26/26 verified`; issues #58 through #66 all CLOSED (PR train #67 through #74 merged: telemetry dispatcher, tier alias, permissions rewrite, OpenRouter ID refresh, settings schema guard, unified routing table, dormant-suite extraction, HTML layer); `ship-state.md` and `looper-state.md` both `active: false, phase: complete`; session closed at commit `74e34c5`.

**Branch on what you observe:**
- Contract shows `26/26 verified` → skip to Phase 3's gate check (only the OpenRouter Phase 2 prerequisites remain open).
- `ship-state.md` `active: false` and all 8 issues closed/merged → Phase 1 is done; re-verify Phase 2 numbers (AC-013..019) yourself, then decide the Phase 3 gate.
- `active: true` → find the first ship-state row whose Status isn't `merged`; that's the resume point. Cross-check `gh pr list` before invoking `/looper` again: don't open a duplicate PR for an issue that already has one open.
- Contract mtime >72h old and `active: true` → `hooks/acceptance-gate.sh`'s 72h staleness window means the hook stops blocking `TaskUpdate→completed` here. That's a hook-behavior fact, not permission to skip verification: still run the mapped AC test before calling anything done.

## Phase 1: Complete (US-001..US-008, issues #59-#66)

Eight issues, topologically ordered in `ship-state.md`, each mapped to 2-4 acceptance criteria with an exact test command in the contract. Completed 2026-07-06: all eight merged via PRs #67 through #74, tracking issue #58 closed, contract at 26/26 verified. Full table, per-AC test commands, evidence format, and the resume-a-stalled-looper procedure (kept as the template for future campaigns): `references/phase1-user-stories.md`.

## Phase 2: Routing unification hardening

Target: promote `skills/council/model-routing.json` to the single routing source of truth, killing the three-surfaces problem (`settings.json.model`, `_council-engine.md` prose table, this file: one fact in three vocabularies that can never stay in sync). US-005 (#63, merged via PR #72 on 2026-07-05) extended the schema with `tiers`/`profiles`/`spawn_sites`/`egress_policy`, where `egress_policy` is a structural field: any external destination without one fails validation. As of 2026-07-06 the file is spec_version 2.0, machine-readable, and hard-gated by pre-commit hook `model-routing` (`pipeline/hooks/check_model_routing.py`, verified passing). No runtime loader consumes it yet, and the first live routing change still needs the Phase 3 smoke eval. Full schema, spawn-site list, and validator design (AC-013/AC-014): `references/routing-schema.md`.

## Phase 3: OpenRouter Phase 2, lens relay (GATED, do not build yet)

Most prerequisites still do not exist as code (re-verified 2026-07-06): the 38-case golden eval harness (`pipeline/evals/` is absent), egress controls (send-allowlist/ZDR/kill-switch: the `egress_policy` schema field now exists and is hook-validated, but there is zero enforcement implementation in `mcp/openrouter/*.py`), and `OPENROUTER_API_KEY` (unset on this machine). Fresh OpenRouter model IDs (US-004) are the one prerequisite already done: re-verify monthly with `python3 mcp/openrouter/check_models.py`. Even the *smaller* 12-case smoke eval that would unlock Pattern B's first live caller hasn't shipped (F11, targeted v1.1).

Solution menu, ranked: (1) **Pattern B, routed `consult()` relay for cheap sub-tasks, recommended**: `routing.py`'s `routed_consult()` already exists, fail-soft, zero callers; wiring its first caller needs only the 12-case smoke eval. (2) **Pattern A, thin Claude relay for council lenses inside the Workflow substrate, gated, larger lift**: target `.claude/workflows/council-deliberate.js` doesn't exist; needs the full 38-case harness plus egress gates. (3) **Direct lens replacement without a relay, rejected** in the design doc (forfeits Workflow's deterministic orchestration). Prerequisite table, derivation obligations (fail-soft proof, token/cost model, quality eval vs all-Claude baseline), worked cost math: `references/openrouter-phase2-gate.md`.

## Wrong paths, fenced off

- **Flipping a live model in `settings.json` or a council profile without the 12-case smoke eval.** Explicit `prd.md` non-goal until F11 ships (v1.1).
- **Trusting `skills/council/registry.json` usage counts from before 2026-07-02.** Everything before commit `dc44611` was session-local, uncommitted noise (0/67 committed uses). Check `git status --short skills/council/registry.json` before trusting any count.
- **Sending council or code content through OpenRouter before the Phase 3 egress gates exist.** `openrouter_client.py` forwards `system + prompt` verbatim, zero redaction, to a third-party vendor today.
- **Editing a model ID in more than one of the three routing surfaces.** Fix it at whichever surface Phase 2 designates source of truth; the others read from it once US-005 lands.
- **Marking an AC `verified` in the contract without running its mapped test.** No pasted command + output, no `verified` status: full stop.
- **Bypassing the acceptance gate** (`--no-verify`, editing `hooks/acceptance-gate.sh`, hand-editing the contract's status column). A block is a real signal to go verify, not an obstacle.

## Validation and promotion

Every phase exit is a number: Phase 1 exit is `Progress: N/26 verified` cross-checked against `gh issue list`/`gh pr list --state merged` counts; Phase 2 exit is AC-013..016 verified plus `pre-commit run --all-files` clean; Phase 3 gate-open (not "build," just "allowed to start") is a stated harness pass rate, unit-tested egress code, a provisioned API key, and model IDs re-verified within the last month. Campaign success metrics (design.md): settings.json config conflicts → 0; permission prompts per session → -50%; spawn sites with documented routing → 100% on both accounts; telemetry hook survives a clean clone with the private repo absent → true; dormant suites resident locally → 0 with a preserved record; F11 smoke-eval pass rate → 100% before any activation. Every promotion (issue → PR → merge) routes through **mcs-change-control**'s gates.

## Gotchas

- `looper-state.md` lags `ship-state.md` and only shows the most recently *invoked* issue: the real queue lives in `ship-state.md`.
- `ship-state.md`'s per-issue Status word can be stale by minutes relative to an already-open, checks-green PR. Cross-check `gh pr list` before assuming work is still in flight.
- `skills/council/model-routing.json` (this campaign's file) and `pipeline/config/model-routing.yaml` (an unrelated, unwired governance-tier default file) share a filename fragment and nothing else: don't edit the wrong one.
- A GitHub issue's checkboxes can flip `[x]` inside an open PR's description *before* that PR merges (observed on #58/PR #70). The contract file, not the issue body, is authoritative on whether a test actually ran.
- `mcp/openrouter/check_models.py` needs live network but no API key (public catalog endpoint): a missing key blocks `consult()`, not this script.
- AC-014's routing validator is now real: `pipeline/hooks/check_model_routing.py`, wired as the hard pre-commit hook `model-routing` since PR #71/#72 (2026-07-05). Verify with `python3 pipeline/hooks/check_model_routing.py skills/council/model-routing.json`.
- `pipeline/evals/` genuinely does not exist; don't build against an assumed harness layout before it's created.
- A pinned `claude-*` ID or `[1m]` suffix reappearing in `settings.json` is a regression (shipped once, reverted by US-002/#60): treat it as P1.

## Provenance and maintenance

Last verified: 2026-07-06 (post-closeout refresh), against the live repo and GitHub (the repo always wins over anything stated here).

Re-verification commands:
- Contract progress: `tail -1 .claude/council/sessions/claude-config-model-optimization-20260702-0003/acceptance-contract.md`
- Issue/PR state: `gh issue list --label council-claude-config-model-optimization --state all --json number,state`; `gh pr list --state all --json number,title,state`
- Ship queue: `sed -n '/Issue Queue/,/^$/p' .claude/ship-state.md`
- Routing table + staleness: `cat skills/council/model-routing.json`; `python3 mcp/openrouter/check_models.py`
- OpenRouter test suite: `python3 -m pytest mcp/openrouter/tests/ -q`
- Egress code absence: `grep -rn "send_allowlist\|zdr\|kill_switch" mcp/openrouter/*.py`
- Eval harness absence: `ls pipeline/evals`
- API key: `[ -n "${OPENROUTER_API_KEY:-}" ] && echo SET || echo UNSET`
- Registry durability: `git show HEAD:skills/council/registry.json | python3 -c "import json,sys;d=json.load(sys.stdin);print(sum(s.get('uses',0) for v in d['departments'].values() for s in v['skills'].values()))"`

Full detail: `references/phase1-user-stories.md`, `references/routing-schema.md`, `references/openrouter-phase2-gate.md`.
