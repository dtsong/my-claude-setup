---
name: mcs-change-control
description: Use when about to commit or merge in this repo, edit settings.json or hooks.json, run git commit --no-verify, force-push or rewrite history, choose a commit type prefix, a TaskUpdate gets blocked, or another session touched main today. Symptoms include "acceptance gate blocked me", "which commit type", "can I --no-verify this", "is it safe to force-push". Not for live symptom triage (mcs-debugging-playbook), "has this happened before" digs (mcs-failure-archaeology), or the config/flag catalog (mcs-config-and-flags).
---

# mcs-change-control

## Overview

`~/.claude/settings.json` and `~/.claude/hooks.json` are symlinks into this repo (verified: `ls -la ~/.claude/settings.json`). Any edit to those two files is live for every new session or hook invocation the instant it hits disk, committed or not. Everything else here ships to the owner's daily driver on the next merge to `main`. Governance (pre-commit hooks) is **local-only**: CI runs zero governance checks and branch protection requires 0 approving reviews, so the person committing is the only enforcement layer that exists.

## When to use, and when NOT to

Use before committing anything, editing `settings.json`/`hooks.json`, considering `--no-verify` or a force-push, choosing a commit prefix, or resuming work another session may have touched today.

Route elsewhere: live incident triage → `mcs-debugging-playbook`; "has this been tried" chronicle → `mcs-failure-archaeology`; setting/flag catalog → `mcs-config-and-flags`; `/council`/`/ship`/`/looper` mechanics → `mcs-run-and-operate`; hook/skill-loading internals → `mcs-claude-code-platform`.

## Change classification

| Class | Path | What gates it | Care |
|---|---|---|---|
| Docs-only | `README.md`, `docs/**` | CI syntax/JSON checks only | Low |
| `skills/` content | `skills/**/*.md` | 6 pre-commit hooks (hard: frontmatter, references, isolation, context-load; warn: budget, prose), scoped `^skills/.*\.md$` | Medium, local-only |
| `.claude/skills/` content | this skill's files | **Not covered**: no hook glob targets `.claude/skills/`. Zero automated governance | Medium, manual only |
| `settings.json`/`hooks.json` | repo root | Live production deploy via symlink, on save. `settings.json` also has a hard pre-commit gate since 2026-07-05 (`settings-schema` → `check_settings.py`, PR #71/#64); `hooks.json` has none, CI only confirms JSON parses | **Highest** |
| `hooks/*.sh` | `hooks/*.sh` | CI runs `bash -n` (syntax only); blocking semantics untested | High, silent-failure prone |
| `commands/**` engine docs | `commands/_council-engine.md` etc. | No dedicated hook; read by every `/council`/`/ship`/`/looper` call | High, wide blast radius |
| `.claude/` session state | `ship-state.md`, `looper-state.md`, `council/sessions/**` | Owned by the active session; may be mid-write | Situational, see below |

## Non-negotiables

Confidence key: **documented** = verified against files/commits/issues; **inferred, owner-unconfirmed** = evidence-backed but not stated as policy anywhere.

1. **Never leave a `settings.json`/`hooks.json` edit uncommitted across a session boundary (documented).** The symlink resolves to the working-tree file, not a git ref, so an uncommitted edit is already live for the next session, and vanishes silently if reverted. Commit it or explicitly revert before you stop. Incident: `references/incident-history.md#1-settingsjson-model-pin-churn`.
2. **Never `git commit --no-verify` in this repo (documented).** Pre-commit is the only place governance hooks run. CI has two jobs (shell/JSON/installer-smoke, and gitleaks) and invokes none of the 5 governance hooks. Branch protection requires those CI checks and **0 approving reviews**. `--no-verify` skips the enforcement surface for that commit, permanently.
3. **No history rewrite or force-push without an explicit owner decision (documented facts, inferred rule).** Commit `69cdb56` moved a real person's resume data to a private repo but explicitly deferred "scrubbing history" as a separate, still-unmade decision; that content stays reachable in `origin/main` history. Pushed `origin/worktree-agent-*` branches likewise keep other private content reachable. Rewriting without checking what depends on current SHAs risks destroying an undecided trail or breaking a ref. Details: `references/incident-history.md#3-history-exposure-status`.
4. **`model` fields hold tier aliases only, never versioned model IDs.** `commands/_council-engine.md:105`, `ARCHITECTURE.md:73-74`: use `sonnet`/`opus`/`fable`/`haiku`, never a pinned `claude-*` ID. As of 2026-07-05, `settings.json`'s top-level `model` is hard-enforced by pre-commit (`check_settings.py` L1, PR #71/#64); `agents/**` frontmatter is not (see Gotcha). Re-verify: `grep -n TIER_ALIASES pipeline/hooks/check_settings.py`.

## The acceptance gate

`hooks/acceptance-gate.sh` is a **PreToolUse** hook on the `TaskUpdate` matcher (`settings.json:61-67`). On `TaskUpdate` with `status: "completed"`, it finds the **most recently modified** acceptance-contract file across `.claude/council/sessions/*/`, `.claude/academy/sessions/*/`, `.claude/prd/contract-*.md`, `.claude/acceptance-contract.md` (mtime, not filename order, so a dead session can't block live work by sorting last). Contracts older than `ACCEPTANCE_GATE_STALE_HOURS` (default **72**) are abandoned and allowed through. Otherwise, any `| pending |` or `| failed |` row prints to stderr and the hook exits **2**, denying the call.

**Not scoped to the owning session.** Any `TaskUpdate → completed` anywhere in the repo is gated while *any* fresh (<72h) contract has unmet criteria, even for unrelated work. Verified live, 2026-07-02:

```
$ echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed","taskId":"x"}}' \
  | bash hooks/acceptance-gate.sh; echo "EXIT: $?"
BLOCKED: Acceptance contract has unverified criteria.
  Verified: 9/26   Pending: 17   Failed: 0
EXIT: 2
```

If blocked by a contract that isn't yours: that's by design. Wait for it to close or the 72h window to pass. `ACCEPTANCE_GATE_STALE_HOURS` **is an owner-approval-required escape hatch, not a routine tool** (inferred, owner-unconfirmed: overriding the one interlock preventing incomplete work from being marked done isn't a unilateral call). If authorized, scope it to one invocation, never export repo-wide. Bug history: `references/incident-history.md#2-acceptance-gate-mis-wiring-four-commits`.

## Commit message conventions

Enforced by `pipeline/hooks/check_commit_msg.py` at `commit-msg` stage: `type(scope): description`.

| Type | Use for |
|---|---|
| `skill(name)` | new skill or major change |
| `skill-fix(name)` | bug fix |
| `skill-ref(name)` | refactor, no behavior change |
| `skill-eval(name)` | eval case changes |
| `skill-docs(name)` | skill docs only |
| `chore`, `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `ci`, `perf`, `build`, `revert` | standard conventional types, everything outside `skills/` |

Description ≥10 characters, no trailing period, subject ≤100 characters, `Merge ` subjects exempt. No issue reference required, though recent commits include one.

## Concurrent-session hazard

Multiple sessions have committed to `main` the same day repeatedly, including 8 commits in under 20 minutes on 2026-07-02. Pull/rebase before starting and again right before committing: state moves in minutes, not hours. Never rewrite another session's uncommitted `.claude/` state; files like `ship-state.md`/`looper-state.md` are actively written by whichever run owns them and can be stale by the time you read them; cross-check `git log`/`gh` first. If your change touches a file every session writes to (`registry.json`, `ship-state.md`), batch into one PR: four parallel PRs (#44-#47) failed to do that in March, consolidated into PR #48 instead. Detail: `references/incident-history.md#4-registryjson-conflict-precedent`.

## Gotchas

- **`PostToolUse` + non-zero exit is silent, not blocking.** This made `acceptance-gate.sh` decorative for four months: it printed to stdout, exited 1, and the harness logged "non-blocking status code" and let the call through anyway. A hook meant to stop a tool call must be `PreToolUse` + exit 2 + reason on stderr.
- **`grep -c` on zero matches exits 1, not 0.** `PENDING=$(grep -c pattern file || echo 0)` captures `"0\n0"`, breaking downstream arithmetic. Use `VAR=$(grep -c pattern file) || VAR=0`.
- **`.claude/skills/` has zero automated governance.** No pre-commit glob targets it (they cover `^skills/`, `^settings\.json$`, `^skills/council/model-routing\.json$`); nothing catches a broken reference or malformed frontmatter here except a human or `skill-audit.py --root .claude/skills`.
- **`--no-verify` skips the entire governance surface forever**, not just formatting: CI never re-runs what pre-commit would have caught.
- **A `settings.json`/`hooks.json` edit is live before you commit it**, purely from the symlink. `git status` showing it unstaged does not mean it's inert.
- **Session-state files drift out of sync with `git log`/`gh` during active work** (verified live: `looper-state.md` still showed an earlier issue `in_progress` after two PRs referencing it had already merged). Don't cite one as ground truth without cross-checking.
- **`ACCEPTANCE_GATE_STALE_HOURS` overrides the only interlock stopping unfinished work from being marked complete.** Treat like any safety-interlock override: sign-off, one call, don't leave exported.
- **Open GitHub issue state lags fixed code.** #53 is `OPEN` though its fix shipped over a month ago ("Refs #53", not "Fixes #53"). An open issue isn't proof a bug is live; check code and issue independently.
- **"Tier alias only" is enforced for `settings.json`, not for `agents/**`.** Since PR #71/#64 (2026-07-05), hard hook `settings-schema` (`check_settings.py`, scope `^settings\.json$`) rejects a pinned `claude-*` ID there. `agents/**` frontmatter is still outside every pre-commit glob; `check_frontmatter.py` never inspects `model` as a scalar, only a dict. Re-verify: `grep 'files:' .pre-commit-config.yaml`.

## Pre-merge checklist

Full checklist (18 items, by change class) in `references/pre-merge-checklist.md`. Minimum for `settings.json`/`hooks.json`: JSON parses clean, `model` is a tier alias, no dirty edit left behind, `pre-commit run --all-files` passes.

## Provenance and maintenance

Last verified: 2026-07-05, against an actively-mutating working tree (concurrent ship run merged PRs #67-#71, including US-006/#64's `settings.json` pre-commit guard). Re-check before trusting again:

- Symlinks: `ls -la ~/.claude/settings.json ~/.claude/hooks.json`.
- Model pin: `grep '"model"' settings.json` (expect a bare tier alias, no `claude-*` prefix or `[1m]` suffix; hard-gated at commit time since 2026-07-05, not just documented).
- Pre-commit scope: `grep 'files:' .pre-commit-config.yaml` (expect `skills/**/*.md` hooks anchored `^skills/`, plus two non-`skills/` entries as of 2026-07-05: `^settings\.json$` and `^skills/council/model-routing\.json$`).
- CI governance surface: `cat .github/workflows/validate.yml` (expect only shell-syntax/JSON-parse/installer-smoke/gitleaks).
- Branch protection: `gh api repos/dtsong/my-claude-setup/branches/main/protection --jq '{contexts: .required_status_checks.contexts, reviews: .required_pull_request_reviews.required_approving_review_count}'`.
- Acceptance-gate behavior: `echo '{"tool_name":"TaskUpdate","tool_input":{"status":"completed"}}' | bash hooks/acceptance-gate.sh; echo $?`.
- Stale-open issues: `gh issue view 53 --json state` (and 26, 16, 3).
- History exposure: `git log --oneline 69cdb56 -1`, `git branch -a | grep worktree-agent`.
- Commit-msg types: `grep -A2 VALID_TYPES pipeline/hooks/check_commit_msg.py`.
