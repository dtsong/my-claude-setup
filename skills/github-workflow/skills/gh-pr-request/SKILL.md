---
name: "GitHub PR Request Review"
description: "Request reviewers for a pull request"
triggers:
  - "gh-pr-request"
  - "request review"
  - "request reviewers"
  - "add reviewer"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-write operations — requests reviewers and teams for a pull request.
- Reads CODEOWNERS, file history, and team assignments to suggest reviewers.
- Does not approve or submit reviews — reviewers do that themselves.
- Does not merge PRs — use gh-pr-merge skill for that.

## Input Sanitization

- PR numbers: must be positive integers.
- Reviewer usernames: alphanumeric characters and hyphens only; must begin with `@` prefix.
- Team names: alphanumeric characters, hyphens, and forward slashes only (e.g., `team/frontend`).
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-pr-request - Request PR Reviewers

Request reviewers for a pull request with smart suggestions.

## Usage

```bash
/gh-pr-request                    # Suggest reviewers for current PR
/gh-pr-request @user1 @user2      # Request specific reviewers
/gh-pr-request 123 @user1         # Request reviewer for PR #123
/gh-pr-request --team backend     # Request team review
```

## Workflow

### Step 1: Identify PR

```bash
# Get PR for current branch
PR_NUM=$(gh pr view --json number -q '.number' 2>/dev/null)

if [ -z "$PR_NUM" ]; then
    echo "No PR found for current branch."
    echo "Create one with: /commit-push-pr"
    exit 1
fi
```

### Step 2: Analyze Changed Files

```bash
# Get files changed in PR
gh pr view $PR_NUM --json files -q '.files[].path'

# Identify code owners
# Check CODEOWNERS file if exists
cat .github/CODEOWNERS 2>/dev/null
```

### Step 3: Suggest Reviewers

Based on:
- CODEOWNERS rules
- Recent contributors to changed files
- Team assignments
- Past reviewers on similar changes

```bash
# Get recent contributors to changed files
for file in $(gh pr view $PR_NUM --json files -q '.files[].path'); do
    git log --format='%an' -n 5 -- "$file"
done | sort | uniq -c | sort -rn
```

### Step 4: Request Reviewers

```bash
# Request individual reviewers
gh pr edit $PR_NUM --add-reviewer @user1,@user2

# Request team review
gh pr edit $PR_NUM --add-reviewer team/backend
```

## Output Format

### Reviewer Suggestions

```
PR #123: Add dark mode support

Files changed:
  src/components/Theme.tsx
  src/hooks/useTheme.ts
  src/styles/dark.css

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Suggested Reviewers:

  @frontend-lead (Recommended)
    - CODEOWNER for src/components/
    - Reviewed 80% of recent frontend PRs
    - Last active: 2 hours ago

  @css-expert
    - Recent contributor to src/styles/
    - Expertise in theming
    - Last active: 1 day ago

  @senior-dev
    - General expertise
    - Available (no pending reviews)
    - Last active: 30 minutes ago

Teams:

  @team/frontend
    - Owns src/components/, src/hooks/
    - 5 members available

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Select reviewers to request:
  1. @frontend-lead (CODEOWNER - required)
  2. @css-expert
  3. @senior-dev
  4. @team/frontend
```

### Reviewers Requested

```
Requested reviewers for PR #123:

  ✓ @frontend-lead - Request sent
  ✓ @css-expert - Request sent

They will be notified and the PR will appear in their review queue.

Current review status:
  Requested: 2
  Approved: 0
  Changes requested: 0

The PR requires 1 approval to merge.
```

### Already Has Reviewers

```
PR #123 already has reviewers:

  Current reviewers:
    @reviewer1 - Review pending (requested 1 day ago)
    @reviewer2 - Approved

  Add more reviewers?
    /gh-pr-request @additional-reviewer

  Or ping existing:
    @reviewer1 - haven't reviewed yet
```

## CODEOWNERS Integration

If repository has `.github/CODEOWNERS`:

```
CODEOWNERS for changed files:

  src/components/*       @team/frontend
  src/styles/*           @css-team
  *.tsx                  @typescript-reviewers

Required reviews:
  @team/frontend (1 approval needed)

Note: CODEOWNER reviews are required for merge.
```

## Smart Suggestions

Claude considers:

| Factor | Weight |
|--------|--------|
| CODEOWNERS | Required |
| Recent file contributors | High |
| Similar past PRs | Medium |
| Availability (pending reviews) | Medium |
| Last activity | Low |

## Team Requests

```bash
# Request team review
/gh-pr-request --team frontend

# Multiple teams
/gh-pr-request --team frontend --team security
```

## Removing Reviewers

```bash
# Remove a reviewer (if needed)
gh pr edit 123 --remove-reviewer @user1
```

## Integration

- Use `/gh-pr-status` to check review status
- Use `/gh-pr-respond` to address review comments
- Use `/gh-pr-merge` when approved
- Reviewers can use `/review-pr` to review
