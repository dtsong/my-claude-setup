---
name: "GitHub Activity"
description: "Recent repository activity summary"
triggers:
  - "gh-activity"
  - "recent activity"
  - "what happened"
  - "repo activity"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-only operations — queries commits, PRs, issues, and releases to summarize recent repository activity.
- Does not create, modify, or close any GitHub resources.
- Does not provide health scoring — use gh-health skill for that.

## Input Sanitization

- Date values (--since): must be valid ISO 8601 date strings.
- Author identifiers: must be valid GitHub usernames — alphanumeric characters and hyphens only.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-activity - Recent Activity Summary

Show recent activity in the repository including commits, PRs, issues, and releases.

## Usage

```bash
/gh-activity                # Activity in last 24 hours
/gh-activity --week         # Activity in last 7 days
/gh-activity --month        # Activity in last 30 days
/gh-activity --since 2025-01-01  # Since specific date
/gh-activity --author @user # Activity by specific user
```

## Workflow

### Step 1: Determine Time Range

```bash
# Default: last 24 hours
SINCE=$(date -v-1d +%Y-%m-%dT%H:%M:%SZ)

# Or week
SINCE=$(date -v-7d +%Y-%m-%dT%H:%M:%SZ)

# Or month
SINCE=$(date -v-30d +%Y-%m-%dT%H:%M:%SZ)
```

### Step 2: Gather Activity

```bash
# Recent commits
git log --since="$SINCE" --format="%h %s (%an, %ar)"

# Merged PRs
gh pr list --state merged --json number,title,author,mergedAt \
    --jq ".[] | select(.mergedAt > \"$SINCE\")"

# Opened issues
gh issue list --state all --json number,title,author,createdAt,state \
    --jq ".[] | select(.createdAt > \"$SINCE\")"

# New releases
gh release list --json tagName,publishedAt,name \
    --jq ".[] | select(.publishedAt > \"$SINCE\")"
```

### Step 3: Organize Timeline

Sort all events by time and present.

## Output Format

### Activity Summary

```
Repository Activity Summary

Repository: owner/repo
Period: Last 24 hours
Generated: 2025-01-25 10:30 AM

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📊 Quick Stats

  Commits: 15
  PRs merged: 4
  PRs opened: 3
  Issues opened: 5
  Issues closed: 3
  Releases: 1

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📝 Recent Commits (15)

  main branch:
    abc1234 feat: Add dark mode toggle (@user1, 2 hours ago)
    def5678 fix: Login validation (@user2, 3 hours ago)
    ghi9012 docs: Update README (@user3, 5 hours ago)
    jkl3456 refactor: Clean up auth (@user1, 8 hours ago)
    ... and 11 more

  Active feature branches:
    feat/api-v2: 3 commits by @user4
    fix/mobile-layout: 2 commits by @user5

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔀 Pull Requests

  Merged (4):
    #345 Add dark mode support (@user1, 2 hours ago)
    #347 Fix login validation (@user2, 4 hours ago)
    #348 Update dependencies (@dependabot, 6 hours ago)
    #350 Improve error handling (@user3, 10 hours ago)

  Opened (3):
    #352 Add keyboard shortcuts (@user4, 1 hour ago)
    #353 Refactor API client (@user5, 3 hours ago)
    #354 Add accessibility features (@user6, 8 hours ago)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🐛 Issues

  Opened (5):
    #460 Bug: Login fails on Safari (@reporter1, 1 hour ago)
    #461 Feature: Add export function (@reporter2, 3 hours ago)
    #462 Question: API rate limiting (@reporter3, 5 hours ago)
    #463 Bug: Memory leak detected (@reporter4, 8 hours ago)
    #464 Feature: Dark mode request (@reporter5, 12 hours ago)

  Closed (3):
    #455 Bug: Form submission error - fixed in #345
    #456 Feature: Theme toggle - implemented in #345
    #457 Docs: Missing API examples - fixed in #350

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📦 Releases

  v1.2.0 - Dark Mode Release (4 hours ago)
    Major features:
    - Dark mode support
    - Theme persistence
    - System preference detection

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

👥 Most Active Contributors

  @user1: 5 commits, 2 PRs merged
  @user2: 3 commits, 1 PR merged
  @user3: 2 commits, 1 PR merged

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔔 Notifications

  @you were mentioned in:
    #460 Bug report (@reporter1 asked for your input)

  Reviews completed on your PRs:
    #340 approved by @reviewer1
```

### Timeline View

```
Activity Timeline (Last 24 Hours)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1 hour ago
  🐛 Issue #460 opened: Bug: Login fails on Safari
  🔀 PR #352 opened: Add keyboard shortcuts

2 hours ago
  ✅ PR #345 merged: Add dark mode support
  📝 Commit abc1234: feat: Add dark mode toggle

3 hours ago
  💬 Comment on #460 by @maintainer
  🔀 PR #353 opened: Refactor API client

4 hours ago
  📦 Release v1.2.0 published
  ✅ PR #347 merged: Fix login validation

...

23 hours ago
  🐛 Issue #458 opened: Security report
  📝 First commit of the day
```

### Author Focus

```
Activity by @user1 (Last 7 Days)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Commits: 12
PRs merged: 3
PRs opened: 4
Issues closed: 5
Reviews given: 8

Contributions:
  Mon: ████████ 8 commits
  Tue: ████ 4 commits
  Wed: ██ 2 commits
  Thu: ██████ 6 commits
  Fri: ████████████ 12 commits
  Sat: ██ 2 commits
  Sun: 0 commits

Key accomplishments:
  - Implemented dark mode feature (#345)
  - Fixed critical login bug (#347)
  - Reviewed 8 PRs from teammates
```

## Script Location

`~/.claude/skills/github-workflow/scripts/activity-summary.sh`

## Integration

- Use `/gh-health` for overall repo health
- Use `/gh-mine` to see your specific items
- Use `/gh-triage` to address new issues
