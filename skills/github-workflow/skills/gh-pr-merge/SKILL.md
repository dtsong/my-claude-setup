---
name: "GitHub PR Merge"
description: "Merge a pull request with strategy selection"
triggers:
  - "gh-pr-merge"
  - "merge pr"
  - "merge pull request"
  - "complete pr"
version: "1.0.0"
user_invocable: true
---

# /gh-pr-merge - Merge Pull Request

Merge a pull request with configurable merge strategy.

## Usage

```bash
/gh-pr-merge                  # Merge current branch's PR
/gh-pr-merge 123              # Merge PR #123
/gh-pr-merge --squash         # Squash and merge
/gh-pr-merge --rebase         # Rebase and merge
/gh-pr-merge --merge          # Create merge commit
/gh-pr-merge --delete-branch  # Delete branch after merge
```

## Merge Strategies

| Strategy | Command | When to Use |
|----------|---------|-------------|
| **Squash** | `--squash` | Clean single commit, hide WIP history |
| **Rebase** | `--rebase` | Linear history, preserve individual commits |
| **Merge** | `--merge` | Preserve all history, show merge point |

## Workflow

### Step 1: Pre-Merge Checks

```bash
# Get PR details
PR_NUM=$(gh pr view --json number -q '.number' 2>/dev/null)

# Check merge readiness
gh pr view $PR_NUM --json mergeable,mergeStateStatus,statusCheckRollup,reviewDecision
```

Using GitHub MCP:

```javascript
// Get PR status
const pr = await mcp__github__get_pull_request(owner, repo, pr_number);
const status = await mcp__github__get_pull_request_status(owner, repo, pr_number);
```

### Step 2: Verify Requirements

Check that:
- All required checks passed
- Required approvals obtained
- No merge conflicts
- Branch is up to date (if required)

### Step 3: Confirm and Merge

```bash
# Squash merge (recommended for feature branches)
gh pr merge $PR_NUM --squash --delete-branch

# Rebase merge
gh pr merge $PR_NUM --rebase --delete-branch

# Regular merge
gh pr merge $PR_NUM --merge
```

Using GitHub MCP:

```javascript
mcp__github__merge_pull_request(owner, repo, pr_number, {
    merge_method: "squash",  // or "rebase" or "merge"
    commit_title: "feat: Add dark mode (#123)",
    commit_message: "Detailed description..."
})
```

## Output Format

### Pre-Merge Check

```
Checking PR #123: Add dark mode support

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Merge Requirements:

  ✓ CI checks passed (5/5)
  ✓ Approved by @reviewer1
  ✓ No merge conflicts
  ✓ Branch is up to date with main
  ✓ All conversations resolved

Status: READY TO MERGE

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Merge Strategy:

  [1] Squash and merge (Recommended)
      Combines 5 commits into 1 clean commit
      Best for: feature branches, clean history

  [2] Rebase and merge
      Applies 5 commits on top of main
      Best for: preserving commit granularity

  [3] Create merge commit
      Adds merge commit, preserves all history
      Best for: long-running branches, audit trail

Select strategy [1/2/3]:
```

### Successful Merge

```
Merged PR #123: Add dark mode support

Strategy: Squash and merge
Commits squashed: 5 → 1

Final commit:
  abc1234 feat: Add dark mode support (#123)

Branch cleanup:
  ✓ Deleted remote branch: origin/feat/dark-mode
  ✓ Deleted local branch: feat/dark-mode

Linked issues:
  ✓ Closed #456 (referenced in PR)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Post-merge:
  Switched to branch: main
  Run /git-pull to get the merged changes locally

Congrats! 🎉
```

### Cannot Merge

```
Cannot merge PR #123

Issues found:

  ✗ CI checks failing
      - ci/lint failed (2 errors)
      - ci/test failed (1 failure)

  ✗ Changes requested by @reviewer1
      - Unresolved comment on src/theme.tsx

  ✗ Merge conflicts with main
      - src/components/Header.tsx

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

To fix:

  1. Fix lint errors and failing test
     /git-push after fixes

  2. Address review comments
     /gh-pr-respond

  3. Resolve merge conflicts
     /gh-pr-update or /git-merge-main

Then run /gh-pr-merge again.
```

### Squash Commit Message

When squash merging, craft a good commit message:

```
Suggested squash commit message:

Title:
  feat: Add dark mode support (#123)

Body:
  - Add theme toggle component in header
  - Support system preference detection
  - Persist theme choice in localStorage
  - Add dark color palette

  Closes #456

  Co-Authored-By: Claude <noreply@anthropic.com>

[Edit Message] [Use as-is] [Cancel]
```

## Auto-Delete Branch

After successful merge:

```bash
# Delete remote branch
git push origin --delete feat/dark-mode

# Delete local branch
git branch -d feat/dark-mode

# Update local main
git checkout main
git pull
```

## Protected Branch Rules

If repository has branch protection:

```
Branch protection rules for 'main':

  ✓ Require pull request reviews (1 approval) - Met
  ✓ Require status checks - Met
  ✗ Require branches to be up to date - Branch is 2 commits behind

Update required before merge:
  /gh-pr-update
```

## Integration

- Use `/gh-pr-status` to check readiness first
- Use `/gh-pr-respond` to address comments
- Use `/gh-pr-update` if branch is behind
- Use `/git-delete-branch` for manual cleanup
