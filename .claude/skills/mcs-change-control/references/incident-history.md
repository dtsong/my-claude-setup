# Change-control incident history

Table of contents: [1. settings.json model-pin churn](#1-settingsjson-model-pin-churn) · [2. Acceptance-gate mis-wiring, four commits](#2-acceptance-gate-mis-wiring-four-commits) · [3. History-exposure status](#3-history-exposure-status) · [4. registry.json conflict precedent](#4-registryjson-conflict-precedent)

All SHAs and issue states verified directly (`git show`, `git log`, `gh issue view`, `gh pr view`) on 2026-07-02 against an actively-mutating repo. Re-verify before citing; this repo changes daily.

## 1. settings.json model-pin churn

Illustrates non-negotiable rules 1 and 4 in `../SKILL.md`.

- `8c0cf14` (2026-06-10 02:19): `model` set to `"fable"` (valid tier alias).
- `78fbf46` (2026-06-22 00:16): reverted to `"opus"`, no rationale in the commit body.
- Sometime before 2026-07-02: an **uncommitted** working-tree edit changed `model` to `"claude-fable-5[1m]"`, a versioned ID with a `[1m]` suffix, violating the tier-alias rule and self-contradicting `CLAUDE_CODE_DISABLE_1M_CONTEXT=1` in the same file.
- `0954f52` (2026-07-02 00:39): the dirty edit was committed *as-is*, deliberately, flagged in the commit body as a known violation pending issue #60.
- `a1a8a72` (2026-07-02 00:56, PR #68, `Implements #60`): fixed `model` back to `"opus"`, added the escalation rule to `docs/model-routing.md`. Issue #60 is now **CLOSED**.

Current state (`grep '"model"' settings.json`): `"opus"`, compliant. Lesson: a policy-violating value rode live on disk, silently, for an unknown span before anyone committed a fix. `git status` showing a file as dirty does not mean it is inert; see rule 1.

## 2. Acceptance-gate mis-wiring, four commits

`hooks/acceptance-gate.sh` failed open three separate times before it actually worked:

| Commit | Date | Bug | Fix |
|---|---|---|---|
| `299a264` | 2026-02-16 | Gate created. | n/a |
| `6bc7c1a` | 2026-03-07 | Relative hook path broke depending on CWD; `jq` hard-failed under `set -euo pipefail` on malformed input. | `$HOME`-based absolute path; jq fallbacks that exit 0 on malformed input (deliberately fail-open). |
| `4bb8bf2` | 2026-05-10 | `grep -c` exits 1 on zero matches, so `PENDING=$(grep -c ... \|\| echo 0)` captured `"0\n0"` (two values), breaking arithmetic. Malformed BRE alternation in the criteria listing. | `VAR=$(grep -c ...) \|\| VAR=0` pattern; `grep -E '\| (pending\|failed) \|'`. |
| `605112d` | 2026-06-22 | Registered as `PostToolUse`, printed to stdout, exited 1: non-blocking, so `TaskUpdate to completed` always went through regardless of unmet criteria. Contract selection took the alphabetically-last glob match, so a dead session's contract could block live work. | Moved to `PreToolUse`, reason to stderr, exit 2 (denies the tool). Contract selected by mtime. Skip contracts untouched beyond `ACCEPTANCE_GATE_STALE_HOURS` (default 72h). Refs #53. |

Issue #53 (the mis-wiring bug) is still **OPEN** as of 2026-07-02 despite the fix landing over a month earlier: the commit says "Refs #53", not "Fixes #53", so GitHub never auto-closed it. Also stale-open: #26 (the gate's own original AC design), #16, #3. An open issue is not proof a bug is still live; check the code and the issue independently.

Pattern worth noting for any hook you touch: every failure mode above was fail-open (silently let unsafe things through), never fail-closed. Nothing in this repo currently tests `acceptance-gate.sh` in CI; the only verification is the manual stdin-pipe invocation shown in `../SKILL.md`.

## 3. History-exposure status

Two open privacy questions, neither resolved, both relevant before any force-push or history rewrite:

- `69cdb56` (2026-06-10) moved `resume-tailor` (a real person's resume data) to the private sibling repo. Its own commit body: "the moved files remain in git history; scrubbing history is a separate decision." That decision has not been made; the content is still reachable from `origin/main` history.
- Six `worktree-agent-*` branches exist locally; `worktree-agent-a52e7b9f` and `worktree-agent-abe26a26` (at minimum) have matching `origin/` refs (verified via `git branch -a`). soc-security/ece content is reachable through part of this branch family, per the same June sweep that produced `69cdb56`.

Neither is "fixed"; they are open owner decisions. Do not force-push or rewrite history to "clean this up" unilaterally; that risks destroying the evidence trail for a decision that hasn't been made, or breaking a ref another session or fork (for example PR #57 from `dtsong-harness`) depends on.

## 4. registry.json conflict precedent

March 2026: PRs #44, #45, #46, #47 (four parallel `worktree-agent-*` branches, each touching `skills/council/registry.json`) were all closed **unmerged** (verified `gh pr view 44` through `47`: all `CLOSED`, not `MERGED`). Their content was consolidated into a single PR #48 instead ("roster gap resolution, 8 skill/agent additions"), specifically to avoid four separate branches racing conflicting edits to one shared, frequently-touched file.

If you're about to open a PR that touches `registry.json`, `ship-state.md`, or another file every concurrent session writes to, batching into one PR beats racing separate ones. Ask before assuming your session is the only one editing a shared-state file today; check `git log --oneline -10` for other sessions' commits first.
