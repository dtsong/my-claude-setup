---
name: mcs-diagnostics-and-tooling
description: Use when you need a hard number instead of an impression in my-claude-setup - skill/agent/command inventory counts, description-token cost, per-file or context-load token budgets, prose/checklist pattern scans, eval-tier runs, manual pre-commit validator exit codes, whether a hook actually blocks, or README-vs-reality drift. Covers pipeline/scripts/*, scripts/*, `python3 pipeline/hooks/check_*.py`, gh-based issue/PR/branch-protection queries, and this skill's own hook-contract-check.sh / doc-drift-check.sh. Not for deciding what counts as acceptance evidence (mcs-validation-and-qa) or for fixing what a tool finds (mcs-debugging-playbook).
---

## Overview

Two diagnostic layers, easy to conflate: `pipeline/scripts/` measures skill-governance compliance (budgets, context load, structural patterns); `scripts/` measures agent-coordination and repo-ops state (worktrees, task boards, telemetry). Both are read-only reports, not enforcement: `pipeline/hooks/` is what actually blocks a commit. Every number below came from running the tool today (2026-07-02) against a repo under active concurrent modification (HEAD `8b36965`); re-run before trusting a number for a decision.

## When to use, and when not

Use to: count things instead of guessing, check whether a hook you changed actually blocks (not what its comment claims), check whether a doc's "N agents/skills/commands" claim is still true, or query `gh` for issue/PR/branch-protection state.

Route elsewhere: deciding a number is "good enough" to ship → mcs-validation-and-qa; a tool found something broken and you need to fix it → mcs-debugging-playbook; the history behind a metric → mcs-failure-archaeology; the config-value catalog itself, not a tool measuring against it → mcs-config-and-flags.

## 1. pipeline/scripts/ (skill-governance measurement)

| Script | Invocation | Measures | Threshold | 2026-07-02 result |
|---|---|---|---|---|
| `skill-audit.py` | `python3 pipeline/scripts/skill-audit.py --json` | inventory count, always-loaded description-token cost, name/body dupes | flags descriptions over `--desc-token-threshold` (120) | 123 skills, 5,966 description tokens total, 0 name dupes, 0 identical bodies |
| `budget-report.py` | `python3 pipeline/scripts/budget-report.py` | per-file words/tokens vs `pipeline/config/budgets.json` target | OK <90%, WARN 90-100%, OVER >100% (warn-tier only) | 198 OK / 14 WARN / 16 OVER of 228 files (2026-07-06; highly volatile, always re-run) |
| `context-load-analysis.py` | `python3 pipeline/scripts/context-load-analysis.py` | coordinator + largest specialist load vs 5,500-token ceiling | OK / OVER | **empty table** on this repo, see Gotchas |
| `analyze-patterns.py` | `python3 pipeline/scripts/analyze-patterns.py` | prohibited prose, output-format duplication, checklists >10 items | counts only, no exit-code gate | 0 prose hits / 4 dup output formats / 24 long inline checklists |
| `check-regressions.py` | `python3 pipeline/scripts/check-regressions.py` | `eval-cases/baselines/*.json` vs `eval-results/<skill>/` | reports pass→fail regressions | "Skills checked: 0" (same layout bug as above) |
| `run-evals.sh` | `bash pipeline/scripts/run-evals.sh --tier <1\|2\|3\|all> [--targets x,y] [--model m] [--diff]` | tier1 = pre-commit hooks, free; tier2 = E2E via `claude -p`, 10-60s/case; tier3 = LLM-judge, 5-15s/skill | **tiers 2-3 shell out to `claude -p`, real spend** | tier1: 4 hard hooks passed, 2 warn hooks passed with advisories |
| `judge-skill-quality.sh` | `bash pipeline/scripts/judge-skill-quality.sh [--targets x] [--model m] [--diff]` | LLM-judge Clarity/Completeness/Actionability (1-5 each) | **spends money**, needs `claude` on PATH | writes `eval-results/judge-<ts>/results.jsonl`; not run here to avoid spend |
| `check-portability.sh` | `bash pipeline/scripts/check-portability.sh` | platform-specific content scan | advisory, always exit 0 | 351 warnings as of 2026-07-06, drifts with every doc change (mostly `skills/paperbanana/` CLI-arg lines misread as absolute paths) |
| `validate-structure.sh` | `bash pipeline/scripts/validate-structure.sh` | skill directory structure vs spec | PASS/FAIL | all checks passed today |
| `package-skill.sh` | `bash pipeline/scripts/package-skill.sh <skill-dir>` | tarball a skill | n/a | not run (writes a file) |
| `check-token-budgets.sh` | `bash pipeline/scripts/check-token-budgets.sh` | CI-style wrapper around `budget-report.py` | n/a | **not referenced anywhere in `.github/workflows/validate.yml`** (dead unless invoked manually) |

`pipeline/shell-helpers.sh` (source, don't execute): `skill-wc`, `skill-check`, `skill-budget`, `skill-audit`, `skill-load`, `skill-new`/`skill-new-suite`: full signatures and the `*-skill/`-at-root scaffold convention in `references/pipeline-shell-helpers.md`.

## 2. Manual validator runs (`pipeline/hooks/`)

`python3 pipeline/hooks/<hook>.py <file...>`, exit 1 = FAIL, warn-tier hooks always exit 0.

| Hook | Tier | Exit contract |
|---|---|---|
| `check_frontmatter.py` | hard | exit 1 on missing `name`/`description`, non-kebab `name`, description <10 words, bad `model` enum. Unknown optional fields are **WARN only**, exit 0 |
| `check_references.py` | hard | exit 1 on a broken path under any of the six bundle dirs (references, shared-references, templates, scripts, assets, examples); only inspects files literally named `SKILL.md` |
| `check_isolation.py` | hard | exit 1 if a specialist `SKILL.md` references a sibling specialist directory |
| `check_context_load.py` | hard | exit 1 if coordinator+specialist+largest-reference exceeds 5,500 tokens (or a matching `budgets.json` override) |
| `check_token_budget.py` | warn | always exit 0; WARN/INFO printed to stderr |
| `check_prose.py` | warn | always exit 0; only scans inside `## Procedure` sections |
| `check_commit_msg.py` | hard, commit-msg stage | `python3 pipeline/hooks/check_commit_msg.py <msgfile>`; exit 1 on wrong `type(scope): desc` shape |
| `check_settings.py` | hard | scoped to `settings.json` only (not `skills/*.md`, easy to miss in this table); exit 1 on schema violation or L1/L2/L3 lint failure: L1 pinned `claude-*` model instead of tier alias (`opus`/`sonnet`/`haiku`/`fable`), L2 `[1m]` context suffix present, L3 `my-claude-setup-private` path in a hook command. Verified passing 2026-07-05: `python3 pipeline/hooks/check_settings.py settings.json; echo $?` |

Known false-positive / silent-skip families (document, do not silently fix; route the actual fix to mcs-debugging-playbook): `references/validator-false-positives.md`.

## 3. scripts/ (ops / agent-coordination measurement)

| Script | Invocation | Measures | 2026-07-02 result |
|---|---|---|---|
| `skill-scorecard.sh` | `bash scripts/skill-scorecard.sh [skills-dir]` | per-skill 6-point health score (Gotchas/Description/Evals/Scripts/Assets/Scope) | 16 skills scored, avg 41% (scans one level deep only, see Gotchas) |
| `skill-usage-report.sh` | `bash scripts/skill-usage-report.sh [--days N] [--project NAME]` | `~/.claude/telemetry/skill-usage.jsonl` | file does not exist; producer hook not wired anywhere, exits 0 with a message |
| `agent-status.sh` | `bash scripts/agent-status.sh [--verbose]` | worktrees under `~/.claude-worktrees/<repo>` | "No worktrees found for my-claude-setup" today |
| `find-workspaces.sh` | `bash scripts/find-workspaces.sh [--json] [--active-only]` | active Claude sessions via `~/.claude/todos/*.json` | 0 active workspaces today |
| `task-board.sh` | `bash scripts/task-board.sh <command> [args]` | multi-agent claim board (runtime state under the user's home directory, this machine only) | commands: `acquire-lock release-lock check-stale init reset show add-task list-available list-claimed` |
| `notify-complete.sh` | `bash scripts/notify-complete.sh <branch> [summary]` | macOS `osascript`/Linux `notify-send` completion ping | not run here (fires a real notification + sound); read source first |

## 4. gh-based instruments (this machine's `gh` auth, repo `dtsong/my-claude-setup`)

```bash
gh issue list --state open                                  # all open issues
gh issue list --state open --search "council-<session-slug>" # one council session's issues
gh pr list --state all --limit 10                            # recent PR states
gh api repos/dtsong/my-claude-setup/branches/main/protection # merge-gate truth
```

2026-07-02: required checks = `validation (ubuntu-latest/macos-latest)`, `secret-scan`; `required_approving_review_count: 0`; `enforce_admins: false`. `pipeline/hooks/` governance is **not** in this list: pre-commit is local-only, bypassable with `--no-verify`, and CI never re-runs it.

## 5. New: `scripts/hook-contract-check.sh`

Feeds a crafted stdin JSON payload to any hook script and reports exit code, which stream got output, and a verdict, per the harness contract: **PreToolUse + exit 2 + stderr = blocks; anything else does not.**

```bash
bash .claude/skills/mcs-diagnostics-and-tooling/scripts/hook-contract-check.sh \
  hooks/acceptance-gate.sh PreToolUse TaskUpdate '{"status":"completed"}'
# Exit code:   2   |  Stderr: 797 bytes   |  Verdict: WOULD BLOCK (PreToolUse, exit 2, reason on stderr)

bash .claude/skills/mcs-diagnostics-and-tooling/scripts/hook-contract-check.sh \
  hooks/acceptance-gate.sh PreToolUse TaskUpdate '{"status":"in_progress"}'
# Exit code:   0   |  Stderr: 0 bytes    |  Verdict: would NOT block
```

Verdict depends only on `status` in the payload, not on live contract content.

## 6. New: `scripts/doc-drift-check.sh`

Counts `agents/*.md`, `commands/*.md` (excluding the engine file), `skills/**/SKILL.md`, and `skills/council/*` departments; diffs against README.md's directory-tree numeric claims. Always exits 0 (advisory, not a gate).

```bash
bash .claude/skills/mcs-diagnostics-and-tooling/scripts/doc-drift-check.sh
```

2026-07-02 output (all four claims currently drifted):

```
DRIFT agents       claimed=21 actual=38 delta=17
DRIFT commands     claimed=16 actual=28 delta=12
DRIFT skills       claimed=57 actual=123 delta=66
DRIFT departments  claimed=20 actual=22 delta=2
  DRIFT: 68 council SKILL.md files falls outside the "departments x 2-3 skills" range (44-66)
```

Route fixing these to mcs-docs-of-record, not this skill.

## Gotchas

- `context-load-analysis.py` and `check-regressions.py` only scan directories literally named `*-skill/` at the repo **root** (the layout `skill-new`/`skill-new-suite` scaffold). This repo's real skills live under `skills/`, so both silently print an empty/zero report on every run here. It looks like "nothing to report," not like a bug. Confirm intent (mcs-failure-archaeology) before "fixing" it.
- `pre-commit run --all-files` looks clean even when known-failing files exist: `resume-tailor`, `soc-security`, `ece`, etc. are gitignored symlinks, and `--all-files` iterates `git ls-files`, which never sees them. Run the hook directly on the path to see the real `FAIL`, e.g. `python3 pipeline/hooks/check_isolation.py skills/resume-tailor/SKILL.md`.
- All six local pre-commit hooks are scoped `files: ^skills/.*\.md$` in `.pre-commit-config.yaml`. `.claude/skills/**` (including this skill) matches nothing and gets zero automated governance validation.
- `check_frontmatter.py` only **WARNS** (exit 0) on unknown frontmatter fields like `git-workflows`'/`prompt-wizard`'s `triggers:`/`user_invocable:`. It does not hard-fail them (verified directly against `pipeline/hooks/check_frontmatter.py:135-139`); an earlier investigation note claiming a hard failure here was wrong.
- `check_frontmatter.py`/`check_references.py` both no-op on any file not literally named `SKILL.md`. A `DEPARTMENT.md` with broken links (e.g. `skills/council/accountant/DEPARTMENT.md`) always exits 0 by construction, not by evasion.
- `budgets.json`'s 25 overrides are keyed `skills/threat-model-skill/...`; real path is `skills/soc-security/skills/threat-model-skill/...`. They never match: `check_context_load.py` hard-fails soc-security's two oversized specialists (6,081, 6,026 tokens) every direct run.
- `chmod +x` is denied by `settings.json`'s global deny list (`Bash(chmod *)`), even though `.claude/settings.local.json` allows `Bash(chmod +x:*)` (deny wins). Invoke scripts via `bash <path>`; `chmod +x` them outside this permission profile before distributing.
- `skill-scorecard.sh` (16) and `skill-audit.py` (123) disagree 7x: the scorecard reads one level deep only (`skills/*/SKILL.md`), silently excluding every suite without a top-level `SKILL.md` (council, ece, data-engineering-skills, frontend-qa).

## Provenance and maintenance

Last verified 2026-07-02, `main` HEAD `8b36965`, under active concurrent modification: treat every number above as a snapshot.

Re-verify:
- Skill/description counts: `python3 pipeline/scripts/skill-audit.py --json`
- Budget summary: `python3 pipeline/scripts/budget-report.py | tail -3`
- `context-load-analysis.py` bug still present: `python3 pipeline/scripts/context-load-analysis.py | sed -n '1,10p'` (empty table = still present)
- Pre-commit scope: `grep 'files:' .pre-commit-config.yaml`
- Branch protection: `gh api repos/dtsong/my-claude-setup/branches/main/protection -q '.required_status_checks.contexts, .required_pull_request_reviews.required_approving_review_count'`
- Telemetry still unfed: `ls ~/.claude/telemetry/skill-usage.jsonl` (this machine only; expect "No such file")
- `budgets.json` ceiling/overrides: `python3 -c "import json;d=json.load(open('pipeline/config/budgets.json'));print(d['max_simultaneous_tokens'], len(d['overrides']))"`
- Doc drift: `bash .claude/skills/mcs-diagnostics-and-tooling/scripts/doc-drift-check.sh`
- Hook contract: `bash .claude/skills/mcs-diagnostics-and-tooling/scripts/hook-contract-check.sh <hook> PreToolUse TaskUpdate '{"status":"completed"}'`
- `check_settings.py` still wired and passing (added 2026-07-05, current as of that date, re-check for drift): `grep -A5 'id: settings-schema' .pre-commit-config.yaml && python3 pipeline/hooks/check_settings.py settings.json; echo $?`

This machine only: absolute paths under `/Users/danielsong`, the `my-claude-setup-private` sibling repo, `session_telemetry.py`'s location inside it.
