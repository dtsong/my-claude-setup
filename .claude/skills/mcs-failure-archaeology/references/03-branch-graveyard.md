# Branch graveyard

As of 2026-07-02, `git branch -a` lists 19 local branches plus their remotes (only `main`/a feature branch is ever checked out; this repo uses a single working tree, no persistent worktrees despite the `worktree-agent-*` naming). This file sorts them into three buckets.

## Bucket 1: superseded, content already re-landed on main (safe to delete locally)

Verify identity with `git diff <branch> <merge-commit>` (not `<branch> main`: main has moved on so much that diffing against current main always shows thousands of unrelated lines).

| Branch(es) | Head commit | Re-landed via | Verified identical to |
|---|---|---|---|
| `worktree-agent-a17b2bef`, `-a4e4a708`, `-a4e9c020`, `-a52e7b9f`, `-a750c352`, `-abe26a26` | 6 branches, each exactly 1 commit, all authored **2026-03-26 00:58** (same minute: a batch of parallel sub-agents in a worktree swarm) | PR #48 (`9e1111b`, "roster gap resolution: 8 skill/agent additions", merged 2026-03-26 08:31) after PRs #42/#43 merged individually and #44-47 were closed in favor of #48 (see item 10, `06-privacy-and-issues.md`) | Content on main: `skills/council/craftsman/e2e-testing`, `skills/council/architect/distributed-patterns`, `skills/council/forge/hw-security-signoff`, etc. |
| `feat/roster-gap-resolution` | `ec266c8`, 8 commits, 2026-03-26 | Same PR #48 wave (Foundry department + PRD) plus `d04478b` (Accountant, 22-agent roster) | Local-only, not pushed. |
| `chore/cleanup-and-new-skills` | `5b345fb`, 5 commits, 2026-04-06 | PR #49 | `git diff chore/cleanup-and-new-skills ccb93d5` = empty (verified 2026-07-02). Local-only. |
| `feat/generic-skill-audit` | `5d4132a`, 2026-05-25 | PR #50 | `git diff feat/generic-skill-audit 739c85c` = empty (verified 2026-07-02). Local-only. |
| `feat/dbt-skill` | Feb 2026 | PRs #10, #11 | Merged via 2 PRs; duplicate SHAs `f0c4247`/`3b18da2` visible in history from the merge. |
| `docs/main-change-tracking` | Feb 2026 | PR #9 | Merged. Local-only remnant (also pushed as `origin/docs/main-change-tracking`, harmless: no private content, see privacy notes). |
| `chore/v1-criteria-dependabot-codeowners` | `df40712`, 2026-02-12 | PR #4 | CODEOWNERS/Dependabot merged; its gitleaks `fetch-depth: 0` fix is present in main's `.github/workflows/validate.yml` today. Local-only. |

**Caveat before deleting**: `git branch -r --contains 59d911d` (verified 2026-07-02) returns `origin/renovate/configure`, `origin/worktree-agent-a4e4a708`, `origin/worktree-agent-a4e9c020`, `origin/worktree-agent-a52e7b9f`, `origin/worktree-agent-a750c352`, `origin/worktree-agent-abe26a26`: 5 of the 6 `worktree-agent-*` branches (all but `-a17b2bef`) plus `renovate/configure`, pushed to origin, carrying commits (`59d911d`, `f08b295`) with soc-security/ece skill content that a later commit (`bacac76`) implied was sensitive. Deleting the *local* branch does nothing for these: the content stays reachable via the *remote* ref. See `06-privacy-and-issues.md` before touching these.

## Bucket 2: genuinely stalled, unmerged content (owner decision: revive or delete)

| Branch | Head | Age (from 2026-07-02) | What it is | Why it stalled |
|---|---|---|---|---|
| `feat/observability` | `17a9ae7`, 2026-02-10, local-only | ~4.5 months | Langfuse tracing: `hooks/langfuse_hook.py` (largest file in the diff), `/observe-on`/`/observe-off` commands, `observe_gate.sh`. Net +828 lines across 5 files. | The commit message itself lists 7 explicit graduation requirements it never got: timeout wrapper, hardcoded Python path, state cleanup, hook coexistence, tiktoken comment, task categories, dual-gate docs. Never touched again after the initial commit. Possibly superseded in spirit by the `session_telemetry.py` hooks now living in `my-claude-setup-private` (settings.json hook block), but no issue or commit says so explicitly: this is an inference, owner-unconfirmed. |
| `feat/skill-matching-protocol` | `05ab659`, 2026-02-13, pushed | 87 commits behind main | `skills/skill-matching/SKILL.md` (105 lines) + a CLAUDE.md restructure into System Behaviors/Personal Preferences with intent classification and confidence scoring. | CLAUDE.md has since been rewritten twice on main (`9cba263`, `48af508`); rebasing this branch would be a rewrite, not a merge. |
| `feat/help-discovery-command` | `9f62a7d`, 2026-02-13, pushed | 87 commits behind main | `/help` discovery command, `--help` standardized across commands. | Same fork point (`088fe18`) as the other 3 Feb-13 branches; predates the academy removal, council v1.2.0 adoption, and the governance sweep. |
| `feat/post-install-docs` | `5ad2516`, 2026-02-13, pushed | 87 commits behind main | `docs/how-it-works.md` + install.sh banner. | Same as above. |
| `feat/skill-description-standardization` | `2ad3625`, 2026-02-13, pushed | 87 commits behind main | Structured skill descriptions + `[Council]` prefix across 62 files. | Same as above. |

All four Feb-13 branches share the exact same merge-base (`088fe18`) and are exactly 1 commit ahead of it, 87 commits behind main as of 2026-07-02 (re-check with `git rev-list --count <branch>..main`; this number grows every day main gets new commits). They all predate the repo's pivot from an "OSS adoption kit" framing (see `docs/road-to-v1` below) toward the current personal-config focus. No commit or issue records a conscious decision to abandon them: this is a real open question for the owner, not something this skill can resolve.

`docs/road-to-v1` (`e17398a`, 2026-02-12, local-only): a 13-line README "road to v1.0.0" section, companion to still-open issue #3. Same "OSS adoption kit era" bucket.

## Bucket 3: bot branches (no decision needed)

`renovate/configure` (local remnant of the closed PR #32), `dependabot/github_actions/github-actions-76468cb07f` (local remnant of merged PR #5), plus live remote dependabot branches for open PR #52. Automated, safe to ignore; Dependabot/Renovate manage their own branch lifecycle.

## Evidence commands

```bash
git branch -a
git log <branch> -1 --format="%h %ad %s" --date=short
git diff <branch> <claimed-merge-commit>          # should be empty for bucket 1
git rev-list --count <branch>..main                # staleness for bucket 2
git branch -r --contains <sha>                     # exposure check before deleting bucket-1 remotes
```
