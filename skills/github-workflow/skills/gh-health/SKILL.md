---
name: "GitHub Health"
description: "Repository health dashboard and status overview"
triggers:
  - "gh-health"
  - "repo health"
  - "repo status"
  - "repository status"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-only GitHub API operations — queries issues, PRs, CI status, branches, and activity metrics.
- Does not create, modify, or close any GitHub resources.
- Does not perform triage actions — use gh-triage skill for labeling and assignment.

## Input Sanitization

- Focus flags (--issues, --prs, --ci): must be recognized option names only.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-health - Repository Health Dashboard

Display a comprehensive health overview of the repository.

## Usage

```bash
/gh-health              # Full health dashboard
/gh-health --issues     # Focus on issues
/gh-health --prs        # Focus on pull requests
/gh-health --ci         # Focus on CI/Actions status
```

## Workflow

### Step 1: Gather Repository Info

```bash
# Get repo details
gh repo view --json name,owner,description,defaultBranchRef,issues,pullRequests

# Get open issues count
gh issue list --state open --json number | jq length

# Get open PRs count
gh pr list --state open --json number | jq length
```

### Step 2: Analyze Health Metrics

Check:
- Open issues (age, labels, assignment)
- Open PRs (age, review status, CI status)
- Recent activity
- Branch status
- CI/workflow health

### Step 3: Generate Dashboard

Compile all metrics into dashboard view.

## Output Format

### Full Health Dashboard

```
Repository Health Dashboard

Repository: owner/repo
Description: A cool project that does things

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📊 Overview

  Default branch: main
  Last commit: 2 hours ago
  Contributors: 12
  Stars: 456
  Forks: 78

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🐛 Issues

  Open: 23
  Closed (30d): 45

  By priority:
    🔴 Critical: 2
    🟠 High: 5
    🟡 Medium: 10
    ⚪ Low/None: 6

  Needing attention:
    ⚠️ 5 issues unlabeled
    ⚠️ 3 issues unassigned for >7 days
    ⚠️ 2 issues stale (no activity >30d)

  Action: /gh-triage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔀 Pull Requests

  Open: 8
  Merged (30d): 34

  Status breakdown:
    ✅ Ready to merge: 2
    🔄 In review: 3
    ⏳ Waiting on author: 2
    ❌ CI failing: 1

  Oldest open PR: #234 (12 days)
  Average time to merge: 2.3 days

  Action: /gh-pr-status

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🏗️ CI/Actions

  Last workflow run: 1 hour ago
  Recent runs (24h): 45

  Status:
    ✅ Build: passing
    ✅ Tests: passing
    ✅ Lint: passing
    ⚠️ Deploy: skipped (main only)

  Flaky tests: 0 detected
  Average build time: 4m 32s

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🌿 Branches

  Total: 15
  Active (commit <7d): 8
  Stale (no commit >30d): 4

  Protected: main, develop

  Cleanup candidates:
    - feat/old-feature (merged, 45 days old)
    - fix/abandoned (no commits, 60 days old)

  Action: /git-branches --stale

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📈 Activity (Last 7 Days)

  Commits: 34
  PRs opened: 12
  PRs merged: 8
  Issues opened: 15
  Issues closed: 11

  Top contributors:
    @user1: 12 commits
    @user2: 8 commits
    @user3: 6 commits

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🏥 Health Score: 85/100 (Good)

  ✅ Active development
  ✅ PRs being reviewed promptly
  ✅ CI passing consistently
  ⚠️ Some issues need triage
  ⚠️ A few stale branches

Recommendations:
  1. Triage 5 unlabeled issues: /gh-triage
  2. Review ready PRs: /gh-pr-status
  3. Clean up stale branches: /git-branches --stale
```

### Issues Focus (--issues)

```
Issue Health Report

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Summary:
  Open: 23
  Closed this month: 45
  Close rate: 66%

By Age:
  < 1 day: 3
  1-7 days: 8
  1-4 weeks: 7
  > 1 month: 5

By Label:
  bug: 12
  enhancement: 6
  documentation: 3
  question: 2
  unlabeled: 5 ⚠️

Stale Issues (>30 days, no activity):
  #123: Feature request from 45 days ago
  #124: Bug report from 32 days ago

Oldest Open Issues:
  #100: Long-standing feature request (90 days)
  #105: Complex bug to fix (75 days)

Action items:
  /gh-triage --unlabeled    # Label 5 issues
  /gh-triage --stale        # Address 2 stale issues
```

### PR Focus (--prs)

```
Pull Request Health Report

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Summary:
  Open: 8
  Merged this month: 34
  Average days to merge: 2.3

Ready to Merge (2):
  #345: Add dark mode - approved, CI passing
  #347: Fix login bug - approved, CI passing

Waiting for Review (3):
  #350: New feature - no reviewers assigned
  #351: Docs update - review requested 2 days ago
  #352: Performance fix - 1 approval, needs 1 more

Waiting on Author (2):
  #348: Refactor - changes requested
  #349: Test update - merge conflicts

CI Failing (1):
  #353: Experimental - lint errors

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Action items:
  Merge ready PRs: /gh-pr-merge 345
  Request reviews: /gh-pr-request 350
```

## Health Script

Located at: `~/.claude/skills/github-workflow/scripts/repo-health.sh`

## Integration

- Use `/gh-triage` to address issue backlog
- Use `/gh-pr-status` to check PR details
- Use `/gh-mine` to see your items
- Use `/gh-activity` for detailed activity log
