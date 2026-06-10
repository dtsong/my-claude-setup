---
name: "gh-pr-status"
description: "Use when checking pull request status, CI results, review state, and merge readiness."
triggers:
  - "gh-pr-status"
  - "pr status"
  - "check pr"
  - "ci status"
  - "is pr ready"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-only GitHub API operations — queries PR details, CI check results, and review status.
- Does not modify PRs, merge branches, or update code.
- Does not respond to review comments — use gh-pr-respond skill for that.

## Input Sanitization

- PR numbers: must be positive integers.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-pr-status - Check PR Status

Check the status of a pull request including CI, reviews, and merge readiness.

## Usage

```bash
/gh-pr-status             # Status of PR for current branch
/gh-pr-status 123         # Status of specific PR #123
/gh-pr-status --checks    # Focus on CI/check status
/gh-pr-status --reviews   # Focus on review status
```

## Workflow

### Step 1: Identify PR

```bash
# Get PR for current branch
BRANCH=$(git branch --show-current)
PR_NUM=$(gh pr view --json number -q '.number' 2>/dev/null)

# Or use provided PR number
PR_NUM="${1:-$PR_NUM}"

if [ -z "$PR_NUM" ]; then
    echo "No PR found for current branch."
    echo "Create one with: /commit-push-pr"
    exit 1
fi
```

### Step 2: Fetch PR Details

Using GitHub MCP:

```javascript
// Get PR details
mcp__github__get_pull_request(owner, repo, pr_number)

// Get PR status (checks)
mcp__github__get_pull_request_status(owner, repo, pr_number)

// Get reviews
mcp__github__get_pull_request_reviews(owner, repo, pr_number)

// Get review comments
mcp__github__get_pull_request_comments(owner, repo, pr_number)
```

Or using gh CLI:

```bash
# Full PR details
gh pr view $PR_NUM --json title,state,mergeable,mergeStateStatus,statusCheckRollup,reviews,reviewDecision

# Check status specifically
gh pr checks $PR_NUM
```

### Step 3: Analyze Merge Readiness

Compile status from all sources.

## Output Format

### Full Status

```
PR #123: Add dark mode support

URL: https://github.com/owner/repo/pull/123
Branch: feat/dark-mode → main
Author: @username
Created: 2 days ago
Updated: 3 hours ago

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

CI/Checks Status

  ✓ Build (3m 24s)
  ✓ Tests (5m 12s)
  ✓ Lint (1m 03s)
  ✓ Type Check (2m 15s)
  ⏳ Deploy Preview (running...)

Overall: 4/5 checks passed, 1 pending

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Review Status

  ✓ @reviewer1 - Approved (1 day ago)
  💬 @reviewer2 - Commented (6 hours ago)
      "Could we add a test for the edge case?"
  ⏳ @reviewer3 - Pending

Review decision: Changes requested → Approved
Approvals: 1 of 1 required

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Merge Readiness

  ✓ No conflicts with main
  ✓ Branch is up to date
  ✓ Required checks passed
  ✓ Required approvals met
  ⚠️ 1 unresolved conversation

Status: ALMOST READY (resolve conversation first)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Actions:
  /gh-pr-respond         # Address review comments
  /gh-pr-merge           # Merge when ready
  /gh-pr-update          # Update branch with main
```

### Checks Focus (--checks)

```
CI/Checks for PR #123

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Required Checks:

  ✓ ci/build
      Completed in 3m 24s
      Artifacts: build.zip

  ✓ ci/test
      Completed in 5m 12s
      Coverage: 87% (no change)

  ✗ ci/lint
      Failed after 1m 03s
      Error: 2 ESLint errors found
      → src/components/Theme.tsx:45
      → src/hooks/useTheme.ts:12

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Optional Checks:

  ✓ codecov/project
  ✓ deploy-preview
      URL: https://preview-123.example.com

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Summary: 2/3 required checks passed

To fix:
  1. Address lint errors in the files above
  2. Push changes: /git-push
  3. Checks will re-run automatically
```

### Reviews Focus (--reviews)

```
Reviews for PR #123

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Review History:

  1. @reviewer1 - APPROVED (2 days ago)
     "LGTM! Nice implementation."

  2. @reviewer2 - CHANGES_REQUESTED (1 day ago)
     "A few suggestions for improvement."

     Comments:
       src/components/Theme.tsx:45
       "Consider using useMemo here for performance"

       src/hooks/useTheme.ts:12
       "This could cause a memory leak - add cleanup"

  3. @reviewer1 - APPROVED (6 hours ago)
     "Thanks for addressing the feedback!"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Current Status:
  Total reviews: 3
  Approvals: 2
  Changes requested: 0 (resolved)

  Required approvals: 1 ✓
  Required reviewers: All approved ✓

Review decision: APPROVED

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Unresolved Conversations: 1

  src/components/Theme.tsx:45 (@reviewer2)
  "Consider using useMemo..."

  [Resolve] [Reply]
```

### No PR Found

```
No PR found for branch: feat/dark-mode

The branch hasn't been pushed or doesn't have a PR yet.

Options:
  /git-push              # Push branch first
  /commit-push-pr        # Create a PR

Or specify PR number:
  /gh-pr-status 123
```

## Merge State Explanations

| State | Meaning |
|-------|---------|
| `CLEAN` | Ready to merge |
| `UNSTABLE` | Checks are failing |
| `DIRTY` | Has merge conflicts |
| `BLOCKED` | Missing approvals or checks |
| `BEHIND` | Branch needs update from base |
| `UNKNOWN` | GitHub is calculating |

## Integration

- Use `/gh-pr-respond` to address review comments
- Use `/gh-pr-update` to update branch with main
- Use `/gh-pr-merge` when ready to merge
- Use `/gh-pr-request` to request more reviewers
