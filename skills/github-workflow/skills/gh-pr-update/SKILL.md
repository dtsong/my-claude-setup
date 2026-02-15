---
name: "GitHub PR Update"
description: "Update PR branch with latest changes from base branch"
triggers:
  - "gh-pr-update"
  - "update pr"
  - "update pr branch"
  - "sync pr with main"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-write operations — updates a PR branch by merging or rebasing onto the base branch.
- May force-push when rebasing (uses --force-with-lease for safety).
- Does not merge PRs into the base branch — use gh-pr-merge skill for that.
- Does not modify repository settings or branch protection rules.

## Input Sanitization

- PR numbers: must be positive integers.
- Branch names: alphanumeric characters, hyphens, underscores, and forward slashes only.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-pr-update - Update PR Branch

Update a pull request's branch with the latest changes from the base branch.

## Usage

```bash
/gh-pr-update             # Update current PR's branch
/gh-pr-update 123         # Update PR #123's branch
/gh-pr-update --rebase    # Rebase instead of merge
/gh-pr-update --local     # Update locally and push
```

## When to Use

- PR shows "branch is out of date"
- Base branch has new commits you need
- CI requires branches to be up to date
- Before merging to ensure compatibility

## Workflow

### Option 1: GitHub API Update (Default)

Uses GitHub's API to update the branch without local checkout:

```bash
# Using gh CLI
gh pr update-branch $PR_NUM

# Using GitHub MCP
mcp__github__update_pull_request_branch(owner, repo, pr_number)
```

### Option 2: Local Update

For more control or when API update isn't available:

```bash
# Switch to PR branch
git checkout feat/dark-mode

# Merge main into the branch
git merge origin/main

# Or rebase onto main
git rebase origin/main

# Push updated branch
git push origin feat/dark-mode
# Or force push if rebased
git push --force-with-lease origin feat/dark-mode
```

## Output Format

### Successful Update (API)

```
Updating PR #123 branch...

Before:
  Branch: feat/dark-mode
  Behind main by: 5 commits
  Ahead of main by: 3 commits

Updating via GitHub...

After:
  ✓ Branch updated successfully
  Behind main by: 0 commits
  Ahead of main by: 8 commits (3 original + 5 merged)

New commits from main:
  abc1234 Fix security vulnerability
  def5678 Update dependencies
  ghi9012 Performance improvements
  jkl3456 Bug fix
  mno7890 Documentation update

CI checks will re-run automatically.
Check status with: /gh-pr-status
```

### Successful Update (Local)

```
Updating PR #123 branch locally...

Fetching origin/main...
Merging main into feat/dark-mode...

Merge complete! Pushed to origin.

Updated commits:
  your-commit-1 Your changes
  your-commit-2 More changes
  merge-commit Merge branch 'main' into feat/dark-mode

Branch is now up to date with main.
```

### Already Up to Date

```
PR #123 branch is already up to date with main.

No update needed.
```

### Update Failed - Conflicts

```
Cannot auto-update PR #123 branch.

Reason: Merge conflicts detected

Conflicting files:
  - src/components/Header.tsx
  - src/api/auth.ts

To resolve:

  1. Update locally:
     git checkout feat/dark-mode
     git merge origin/main

  2. Resolve conflicts:
     /git-conflicts

  3. Push resolved branch:
     /git-push

Or use rebase:
  /gh-pr-update --rebase --local
```

### Rebase Update

```
Rebasing PR #123 onto main...

Rebasing 3 commits:
  abc1234 Add theme component
  def5678 Wire up context
  ghi9012 Add styles

Rebase successful!

Note: Force push required (history rewritten)
Pushing with --force-with-lease...

Branch updated. CI will re-run.

Warning: Any local clones of this branch will need to reset:
  git fetch origin
  git reset --hard origin/feat/dark-mode
```

## Merge vs Rebase

| Method | Pros | Cons |
|--------|------|------|
| **Merge** | Safe, no force push | Adds merge commit |
| **Rebase** | Clean linear history | Requires force push |

**Recommendation**:
- Use **merge** for shared branches or if unsure
- Use **rebase** for personal branches you want clean

## Protected Branch Scenarios

If base branch has protection requiring updates:

```
Branch protection requires update before merge.

Repository setting: "Require branches to be up to date"

Options:
  /gh-pr-update          # Update branch with main
  /gh-pr-update --rebase # Rebase onto main

After update, CI will re-run (required for merge).
```

## Force Push Safety

When rebasing requires force push:

```
Rebase complete. Force push needed.

Safety checks:
  ✓ No new commits on remote since last fetch
  ✓ Using --force-with-lease (safer)
  ⚠️ Will rewrite 3 commits

This is safe because:
  - You're the only one working on this branch
  - Or: All collaborators are aware

Proceed with force push? [y/n]
```

## Integration

- Use `/gh-pr-status` to check if update is needed
- Use `/git-merge-main` for local merge approach
- Use `/git-rebase` for local rebase approach
- Use `/gh-pr-merge` after update succeeds
