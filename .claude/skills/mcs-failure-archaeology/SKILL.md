---
name: mcs-failure-archaeology
description: Use when you need the history behind a file or decision before touching it, e.g. "has this been tried", "why was this deleted", "why is this branch stale", "is this issue real", or before reviving a branch, re-adding a deleted skill/hook/model-pin, or reopening an old issue. Covers the acceptance-gate saga, Fable-5 sweep, academy removal, OpenRouter Phase 1, branch graveyard, registry.json, privacy exposure. Not for live debugging (mcs-debugging-playbook) or why a design is load-bearing today (mcs-architecture-contract).
---

# mcs-failure-archaeology

## Overview

This is the chronicle: what was tried, what broke, what was reverted, and what is settled-do-not-reopen in `my-claude-setup`. Core principle: every failure here left evidence (a SHA, an issue number, a branch); read the evidence before repeating the mistake or reviving a corpse. This skill answers "has this been tried" and "why did we delete that": it does not diagnose today's bug (mcs-debugging-playbook) or justify today's architecture (mcs-architecture-contract).

## When to use and when NOT to

Use when: about to re-add something that was deliberately removed (a hook, a skill, a model pin, a babysitting directive); about to revive or rebase a stale branch; investigating why an open GitHub issue looks unfinished; asking "why does settings.json keep changing"; scoping a history rewrite for privacy exposure; wondering if two agents editing the same file concurrently caused a past incident.

Do NOT use for: triaging a hook or command that is broken right now (`mcs-debugging-playbook`); understanding why current architecture is shaped the way it is, its invariants, or its known-weak points (`mcs-architecture-contract`); the change-classification/PR/commit rules themselves (`mcs-change-control`); Claude Code platform mechanics like hook exit codes in the abstract (`mcs-claude-code-platform`); the config/flag catalog (`mcs-config-and-flags`); what counts as evidence for a new change (`mcs-validation-and-qa`).

## The chronicle (scannable index)

Full narrative for each row lives in `references/`. Read the reference file before acting on a row.

| # | Entry | Status (dated per row; default 2026-07-02) | Root cause (one line) | Key evidence | Detail |
|---|---|---|---|---|---|
| 1 | Acceptance-gate saga | Fixed, but issue #53 still open | Fail-open by design across 3 iterations: relative path, `grep -c` arithmetic, PostToolUse+exit-1 is non-blocking | 299a264, 6bc7c1a, 4bb8bf2, 605112d, #53 | `references/01-acceptance-gate-saga.md` |
| 2 | Fable-5 modernization sweep (one night) | Settled, do not re-add removed items | Directives/hooks/pins written to babysit pre-Fable models became dead weight once auto-compaction + better model behavior shipped | 8c0cf14..9cee199 (9 commits) | `references/02-fable5-sweep-and-academy-removal.md` |
| 3 | Academy theme removal | Settled, do not resurrect | Unused 17-agent theme, -2,779 lines, dead weight | 12c34df | `references/02-fable5-sweep-and-academy-removal.md` |
| 4 | Branch graveyard | Mixed: 6 safe-delete-but-leaky, 1 stalled-decide, 4 stale-decide | Superseded worktree-agent branches re-landed under new SHAs; 4 Feb-13 branches never rebased before repo pivoted | see table in reference | `references/03-branch-graveyard.md` |
| 5 | OpenRouter Phase 1 chain | Merged, zero human review | Local Claude review loop caught 3 real bugs pre-merge; a 4th shipped anyway and needed a post-merge fix | PR #55, 898174d, PR #56/01b6081 | `references/04-openrouter-phase1-chain.md` |
| 6 | registry.json broken-instrument era | Fixed 2026-07-02 | Write path existed, nothing ever committed the writes; counts were session-local noise for 2+ months | dc44611, 729adcd | `references/05-registry-and-settings-churn.md` |
| 7 | settings.json tracking + model flip-flops | Settled 2026-07-02 (PR #68) | No single source of truth for model choice; three surfaces disagreed | b9e2ca6, abf3489, 8c0cf14, 78fbf46, 0954f52, a1a8a72/#60 | `references/05-registry-and-settings-churn.md` |
| 8 | Privacy exposure in pushed history | Open, owner-only decision (soc-security/ece); resume-tailor's live-ref exposure closed 2026-07-05, orphaned fork object remains | Internal-audit skill content (soc-security/ece) is committed then later moved but 6 pushed remote refs still hold it; resume-tailor content is NOT on `main` or any live branch, only an unreachable orphaned commit on one fork (re-verify: `git rev-list main -- skills/resume-tailor/SKILL.md`) | 59d911d, f08b295, 8073361 | `references/06-privacy-and-issues.md` |
| 9 | Stale-open issues #3, #16, #26, #53, #54 | Open, mixed reasons | Fix landed without closing issue (#53); scope superseded by newer PRD (#3, #16); design-only phase pending (#26, #54) | see reference | `references/06-privacy-and-issues.md` |
| 10 | PRs #44-47 registry.json pile-up | Settled-do-not-reopen pattern lesson | 4 parallel worktree-agent branches each edited the shared registry.json independently; closed and hand-consolidated into #48 | #44, #45, #46, #47, #48 | `references/06-privacy-and-issues.md` |
| 11 | claude-config-model-optimization campaign | Closed 2026-07-06, contract 26/26 verified, do not re-run its issues | Config drift accreted for months (pinned model vs 1M flag contradiction, imagined-TypeScript permissions, stale OpenRouter IDs, three routing surfaces); fixed as one council-driven, acceptance-gated 8-issue train | issues #58-#66, PRs #67-#74, closeout 74e34c5 | `.claude/council/sessions/claude-config-model-optimization-20260702-0003/` (contract, design, plan) |

## How to use this skill

1. Find your row in the table above.
2. Open the matching file in `references/` from the Detail column; the one-line summary is intentionally lossy.
3. Re-check the "Status" column yourself if the entry is load-bearing for a change you're about to make (this repo moves fast; see Gotchas).
4. If your question isn't in a row, it's probably not settled history: check `mcs-debugging-playbook` (is it happening right now) or ask the owner.

## Gotchas

- **Fail-open is a repeat offender.** Three separate acceptance-gate iterations (299a264 → 6bc7c1a → 4bb8bf2) each fixed one fail-open bug and introduced or left another. The lesson that finally stuck (605112d): blocking a tool call requires `PreToolUse` + `exit 2` + reason on stderr. `PostToolUse` + any non-2 exit is logged but never blocks. If you are wiring a new enforcement hook, verify this by making it fail on purpose and reading the transcript, not by reading the hook script.
- **"Deleted deliberately" is not "deleted correctly."** The June 10 sweep (item 2) removed babysitting directives, duplicate skills, and model pins for reasons documented in each commit message. Before re-adding `code-search`, `git-status`, the diagram/plot skills, a `model:` frontmatter pin, or a context-decay/cost-sink hook, read that commit message: the reason it was cut is usually still true.
- **Local branch existing does not mean content is missing from main.** 6 of the 19 local branches are worktree-agent batch branches from one 2026-03-26 00:58 sub-agent swarm; content already re-landed on main under different SHAs. Verify with `git diff <branch> <merge-commit>`, not `git diff <branch> main` (which shows noise from everything main did afterward).
- **A pushed branch is not private even if deleted locally.** 5 `worktree-agent-*` branches plus `origin/renovate/configure` are pushed to origin, reachable to anyone with repo access; deleting the local branch does nothing. Scrubbing needs a history rewrite (BFG/filter-repo) and force-push: owner-only, high-blast-radius, not authorized by this skill.
- **Zero GitHub reviews does not mean zero review.** PR #55 has 0 reviews/comments in the GitHub API, yet 3 real bugs were caught pre-merge (898174d) by a local Claude review loop. Check for a same-day fix commit, not review count.
- **An issue number in a commit ("Refs #N") does not close the issue.** #53's root cause was fixed in 605112d (2026-06-22) but the issue is still open, because the commit says "Refs", not "Fixes"/"Closes". Open issues here are not proof of unfinished work; check for a fix commit first.
- **Concurrent agents editing the same JSON file is a known incident pattern, not hypothetical.** PRs #44-47 each independently touched `skills/council/registry.json` from parallel worktree-agent branches the same night; all 4 were closed and hand-merged into one PR (#48). If you spawn N parallel agents touching a shared registry/config file, expect the same pile-up.
- **Usage-count fields on shared JSON files are not evidence by default.** `registry.json` showed `uses: 0` for every skill from 2026-04-24 through 2026-07-01 because the write path existed but nothing committed the writes (fixed 2026-07-02, dc44611). Historical claims built on registry counts before that date are void.
- **This repo mutates fast; snapshots rot in hours.** During authoring (2026-07-02) a concurrent ship run merged and closed #59 and #60 mid-write; that campaign (item 11) then completed in full by 2026-07-06. Treat every status above as a snapshot and re-run the Provenance commands before relying on it for anything consequential.

## Provenance and maintenance

Last verified: 2026-07-02 (rows 1-10), 2026-07-06 (row 11 and item-8 date note), against local `git log`/`git show`/`git branch -a` and `gh issue list` / `gh pr list` / `gh pr view --json reviews,comments` on this machine's clone.

Re-verification commands (run from repo root):

- Chronicle SHAs still exist and say what this skill claims: `git show --stat <sha>` for any SHA in the table above.
- Issue statuses (drift fastest of anything in this skill): `gh issue list --state open --limit 30` and `gh issue view <n>`.
- PR review reality (not just PR state): `gh pr view <n> --json reviews,comments`.
- registry.json committed-vs-live drift: `git show HEAD:skills/council/registry.json | python3 -c "import json,sys; print(json.load(sys.stdin)['last_updated'])"`. If this date is not today, committed counts are stale by that many days.
- Which branches are genuinely dead vs merged-under-a-different-SHA: `git diff <branch> <claimed-merge-commit>` (not `<branch> main`, which always shows noise once main has moved on).
- Which pushed refs still hold privacy-sensitive commits: `git branch -r --contains <sha>` for the SHAs listed in `references/06-privacy-and-issues.md`.
- Current model/settings state: `git show origin/main:settings.json | grep -n '"model"'` and `git show origin/main:docs/model-routing.md` (this file did not exist before 2026-07-02; it is the intended single source of truth going forward, per item 7).
