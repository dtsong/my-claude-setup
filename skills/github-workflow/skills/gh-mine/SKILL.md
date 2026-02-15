---
name: "GitHub Mine"
description: "Show my assigned and mentioned GitHub items"
triggers:
  - "gh-mine"
  - "my issues"
  - "my prs"
  - "assigned to me"
  - "my work"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-only GitHub API operations — queries issues, PRs, review requests, and mentions assigned to or involving the authenticated user.
- Does not create, modify, or close issues or PRs.
- Does not perform triage or labeling — use gh-triage skill for that.

## Input Sanitization

- Filter flags (--issues, --prs, --reviews, --mentions): must be recognized option names only.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-mine - My GitHub Items

Show issues, PRs, and mentions assigned to or involving you.

## Usage

```bash
/gh-mine                # All my items
/gh-mine --issues       # Only issues assigned to me
/gh-mine --prs          # Only PRs I'm involved with
/gh-mine --reviews      # PRs where my review is requested
/gh-mine --mentions     # Where I'm mentioned
```

## Workflow

### Step 1: Get Current User

```bash
# Get authenticated user
GH_USER=$(gh api user --jq '.login')
```

### Step 2: Fetch Assigned Items

```bash
# Issues assigned to me
gh issue list --assignee @me --state open --json number,title,labels,createdAt

# PRs I authored
gh pr list --author @me --state open --json number,title,state,reviews

# PRs where review requested
gh pr list --search "review-requested:@me" --json number,title,author

# Mentions
gh api search/issues --jq '.items' -f q="mentions:$GH_USER is:open"
```

### Step 3: Organize and Display

Group by type and priority.

## Output Format

### Full Dashboard

```
My GitHub Dashboard

User: @username

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📋 My Assigned Issues (5)

  Priority: High
    #456 Fix critical login bug
        Labels: bug, priority-high
        Assigned: 2 days ago

    #458 Security vulnerability
        Labels: security, priority-high
        Assigned: 1 day ago

  Priority: Normal
    #460 Improve error messages
        Labels: enhancement
        Assigned: 3 days ago

    #462 Documentation update
        Labels: documentation
        Assigned: 4 days ago

    #465 Add unit tests
        Labels: testing
        Assigned: 1 week ago

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

🔀 My Pull Requests (3)

  Ready to merge:
    #470 feat: Add dark mode
        Approved by @reviewer1
        CI: ✅ passing

  In review:
    #472 fix: Login validation
        Review by @reviewer2 in progress
        CI: ✅ passing

  Needs work:
    #468 refactor: Auth module
        Changes requested by @reviewer1
        CI: ✅ passing

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

👀 Reviews Requested (2)

  #475 Add caching layer - by @user1
      Files: 5 | +120 -45
      Waiting: 4 hours

  #477 Update dependencies - by @dependabot
      Files: 2 | +50 -50
      Waiting: 1 hour

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

💬 Recent Mentions (3)

  #480 Bug in production
      @maintainer mentioned you: "Can @username take a look?"
      1 hour ago

  #478 Feature discussion
      @user2 mentioned you: "@username what do you think about..."
      3 hours ago

  #476 Code review comment
      @reviewer replied to your comment
      Yesterday

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📊 Summary

  Issues assigned: 5
  PRs authored: 3
  Reviews pending: 2
  Unread mentions: 3

Priority actions:
  1. Merge ready PR #470: /gh-pr-merge 470
  2. Address changes on PR #468: /gh-pr-respond 468
  3. Complete reviews: /review-pr 475
```

### Issues Only (--issues)

```
My Assigned Issues

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#456 Fix critical login bug
  State: open
  Labels: bug, priority-high
  Created: 5 days ago
  Updated: 2 days ago
  Comments: 3

  Latest:
    @reporter (2 days ago): "Still happening in production"

  Action: Needs attention

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#458 Security vulnerability
  State: open
  Labels: security, priority-high
  Created: 3 days ago
  Updated: 1 day ago
  Comments: 5

  Latest:
    @security-team (1 day ago): "Confirmed CVE-2025-1234"

  Action: Critical - address immediately

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

[... more issues ...]

Total: 5 issues assigned to you
```

### Reviews Requested (--reviews)

```
Reviews Requested From Me

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#475 Add caching layer
  Author: @user1
  Branch: feat/caching → main
  Files changed: 5
  Additions: 120, Deletions: 45
  Requested: 4 hours ago

  Summary:
    Adds Redis caching for API responses
    Includes cache invalidation strategy

  Quick links:
    View: /gh-pr-status 475
    Review: /review-pr 475

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#477 Update dependencies
  Author: @dependabot
  Branch: dependabot/npm_and_yarn/... → main
  Files changed: 2
  Additions: 50, Deletions: 50
  Requested: 1 hour ago

  Summary:
    Updates react from 18.2.0 to 18.3.0
    Security patch included

  Quick links:
    View: /gh-pr-status 477
    Approve: /gh-pr-merge 477 (if CI passes)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Total: 2 reviews pending
```

## Script Location

`~/.claude/skills/github-workflow/scripts/my-items.sh`

## Integration

- Use `/gh-pr-status` to check specific PR
- Use `/gh-pr-respond` to address PR comments
- Use `/gh-pr-merge` to merge ready PRs
- Use `/review-pr` to review requested PRs
