# Privacy exposure, stale-open issues, and the registry.json conflict pile-up

## Part A: Privacy exposure in pushed history (item 8)

Two distinct exposure surfaces exist here, and they are NOT equivalent severity. Corrected 2026-07-05 (an earlier draft of this file wrongly conflated them, see Gotcha below):

- `59d911d` (2026-02-21, "feat: add new skill suites and update frontend-qa skills"): added 8 skill directories including `soc-security`, plus `research-consulting`.
- `f08b295` (2026-03-17, "feat: skills best practices audit"): touches the same skill set with best-practices additions.
- `8073361` ("feat: add additional skills and command"): the single commit that added `resume-tailor` content (a real person's resume data, per the later removal commit's own words). This commit is NOT an ancestor of `main`, see below.

`69cdb56` (2026-06-10, part of the Fable-5 sweep, see `02-fable5-sweep-and-academy-removal.md`) added governance scope-constraints sections and replaced the local `resume-tailor` directory with a symlink to `my-claude-setup-private`. Its commit message states: **"the moved files remain in git history; scrubbing history is a separate decision."** Verified 2026-07-05: `git show --stat 69cdb56` shows this commit's diff touches only `skills/dbt-skill/SKILL.md` and `skills/web-security-hardening/SKILL.md`, nothing under `skills/resume-tailor/`. Treat the quoted sentence as a commit-message *assertion*, not a diff-verified fact about what `69cdb56` itself did.

**Where the exposure actually lives** (re-verified 2026-07-05):
- `59d911d` and `f08b295` (`soc-security`/`ece`/`research-consulting` content) ARE reachable today from 6 live pushed remote refs: `origin/renovate/configure`, `origin/worktree-agent-a4e4a708`, `origin/worktree-agent-a4e9c020`, `origin/worktree-agent-a52e7b9f`, `origin/worktree-agent-a750c352`, `origin/worktree-agent-abe26a26`. Re-verify: `git branch -r --contains 59d911d` and `for b in $(git branch -r); do git ls-tree -r "$b" --name-only | grep -qE 'soc-security|ece' && echo "$b"; done`. This is the real, current exposure.
- `resume-tailor` content is NOT reachable from `origin/main` and never was: `git rev-list main -- skills/resume-tailor/SKILL.md` returns nothing. The only ref that ever carried it, `origin/dependabot/github_actions/github-actions-1cd067a277` (PR #51, closed unmerged), no longer exists: `gh api repos/dtsong/my-claude-setup/branches/dependabot/github_actions/github-actions-1cd067a277` returns 404 as of 2026-07-05. It is not present on any currently-live branch of `origin` or of the one known fork, `dtsong-harness/my-claude-setup-fork` (checked every branch there with `gh api repos/dtsong-harness/my-claude-setup-fork/compare/<branch>...8073361`, all report `diverged`, i.e. not an ancestor). The commit object itself is still directly fetchable by SHA from that fork (`gh api repos/dtsong-harness/my-claude-setup-fork/commits/8073361` returns 200) even though no branch points to it: an orphaned-but-not-yet-garbage-collected object, the same category of risk Option B below already describes for deleted refs, not a separate live exposure on `main`.

**Deleting local branches does nothing here.** For the `soc-security`/`ece` content, the exposure is reachable as long as the *remote* refs exist, because anyone with clone access can `git fetch` those refs directly, or GitHub's own history/API can still surface the blobs even off `main`. Removing it for real requires a history rewrite (`git filter-repo` or BFG) across every affected ref, followed by a force-push and coordination with anyone who has already cloned. This is exactly the kind of destructive, hard-to-undo operation that is **owner-only**: do not attempt or recommend automating this without the owner explicitly signing off on scope (which refs, which paths) and the fallout (any other clones/forks become instantly out of sync). For `resume-tailor`, there is currently no live ref to delete; the only residual risk is the orphaned fork object, which the owner may still want purged via GitHub Support, but this is a materially smaller remediation than a `main`-history rewrite.

> **Gotcha (added 2026-07-05):** An earlier draft of this file claimed `resume-tailor` content was "reachable via origin/main itself... it went through main." That claim does not survive verification (`git rev-list main -- skills/resume-tailor/SKILL.md` is empty) and citing `69cdb56`'s diff as evidence for it was wrong, that commit's diff never touches resume-tailor. Lesson: a commit message describing what a prior action did is not the same as verifying it in that commit's own diff. Always check `git show --stat <sha>` before trusting a commit message's self-description.

## Part B: Stale-open issues (item 9)

| Issue | Title | What it actually is | Why it's still open |
|---|---|---|---|
| #3 | v1.0.0 release criteria | Checklist issue from the Feb 2026 "OSS adoption kit" era (installer, docs, CI required checks, branch protection, changelog). None of the checkboxes are checked. | The repo's focus visibly pivoted to personal-config-first sometime after Feb (see `03-branch-graveyard.md`'s Bucket 2 discussion); no commit or issue records a decision to deprioritize v1.0.0 criteria, so this reads as either abandoned-in-spirit or genuinely still-wanted. Owner-unconfirmed either way. |
| #16 | v1.3 compliance: bring original 16 council departments to parity | A 4-batch plan across 61 files to bring the original department set up to the governance spec level added later. | Scope is large and no batch has landed; superseded in urgency by newer work (Fable-5 sweep, OpenRouter, this session's US-001..008) but never formally closed or re-scoped. |
| #26 | [AC] Acceptance Criteria Enforcement for Council/Academy Plans | The original 4-layer design issue that `299a264` (see `01-acceptance-gate-saga.md`) partially implemented (contract artifact + hook). | At least 2 of 4 layers are real and shipped; the issue was never closed because it's tracking the full 4-layer vision, not just the hook. Partially realized by the active session's `acceptance-contract.md` + test-stubs, but that's session-scoped, not a permanent closure of #26. |
| #53 | acceptance-gate hook mis-wired | The specific PostToolUse/exit-1 bug. | Root cause fixed in `605112d` (2026-06-22), but that commit says "Refs #53", not "Fixes"/"Closes #53", so GitHub never auto-closed it. This is a **process gap, not a real open bug**: see `01-acceptance-gate-saga.md`. Verify current status with `gh issue view 53` before assuming it's still broken. |
| #54 | OpenRouter integration: MCP consult() + multi-model council lenses + cheap routing | Umbrella tracking issue for the whole OpenRouter effort. | Phase 1 (the MCP server, PR #55) is merged and closed out functionally, but Phase 2 (the lens relay letting non-Claude models sit in council deliberations) is design-only and eval-gated, so the umbrella issue correctly stays open. Not stale in the "forgotten" sense: this one is honestly still in progress. |

**General pattern**: an issue being open in this repo is not reliable evidence that the underlying problem is unfixed. Always check for a same-day or later fix commit before treating an open issue as live work (see the #53 Gotcha in the top-level SKILL.md).

## Part C: PRs #44-47, the registry.json pile-up (item 10)

On 2026-03-26, the same worktree-agent sub-agent swarm that produced the 1-commit-each branches in `03-branch-graveyard.md` also opened 4 separate PRs, each independently touching the shared `skills/council/registry.json`:

- `#44`: a11y-audit skill added to Advocate, closes #38.
- `#45`: finops-analysis skill added to Operator, closes #39.
- `#46`: distributed-patterns skill added to Architect, closes #40.
- `#47`: e2e-testing skill added to Craftsman, closes #41.

Each PR's body independently says "Updates ... DEPARTMENT.md and registry.json." Because all 4 branches forked from close to the same base and each edited the same shared JSON file (adding their own skill's usage-counter entry), merging them individually would have produced 3+ merge conflicts in sequence. Instead: **all 4 were closed** (`gh pr list` shows state `CLOSED`, not `MERGED`, for #44-47) and their content was hand-consolidated into a single PR, `#48` ("roster gap resolution: 8 skill/agent additions", merged `9e1111b`, 2026-03-26 08:31), which also folded in 2 more issues (#34/Foundry department, #35/Foundry roster registration, #36/hw-security-signoff) beyond the original 4.

**The lesson**: if you spawn N parallel agents/branches that all need to register something in a shared index file (`registry.json`, a department table, a roster list), expect them to conflict on merge. The pattern that worked here was closing the individual PRs and hand-merging into one consolidated PR rather than trying to rebase/resolve N-way conflicts individually. If you're orchestrating a similar parallel batch, either (a) have each agent's output land in agent-scoped files with a separate consolidation step, or (b) plan for exactly this closed-and-consolidated PR pattern up front instead of discovering it after 4 PRs are already open.

## Evidence commands

```bash
git branch -r --contains 59d911d
git branch -r --contains f08b295
git rev-list main -- skills/resume-tailor/SKILL.md   # empty = never on main
git log --all --oneline --diff-filter=A -- "skills/resume-tailor/*"
git show 69cdb56 --stat | grep -i resume             # empty = commit message overstates its own diff
gh api repos/dtsong/my-claude-setup/branches/dependabot/github_actions/github-actions-1cd067a277  # 404 = ref gone
gh api repos/dtsong-harness/my-claude-setup-fork/compare/main...8073361 --jq .status  # "diverged" = not reachable
gh issue view 3; gh issue view 16; gh issue view 26; gh issue view 53; gh issue view 54
gh pr view 44 --json state,body; gh pr view 45 --json state,body; gh pr view 46 --json state,body; gh pr view 47 --json state,body
gh pr view 48 --json body
```
