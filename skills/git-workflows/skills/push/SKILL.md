---
name: "Git Push"
description: "Push commits to remote with upstream handling"
triggers:
  - "git push"
  - "push changes"
  - "push commits"
  - "push to remote"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Write operation — pushes local commits to the remote repository
- Does not create commits or modify local files — only publishes existing commits
- Does not create PRs — use github-workflow for that
- Never force-pushes automatically — `--force-with-lease` requires explicit user request

## Input Sanitization

- Flags: only `-u`, `--force-with-lease` accepted. Reject `--force` without `--with-lease`, arbitrary strings, and shell metacharacters.
- Branch names (if specified): only alphanumeric characters, hyphens, underscores, and forward slashes. Reject spaces, `..`, or null bytes.

# /git-push - Push Commits to Remote

Push local commits to remote repository with smart upstream handling.

## Usage

```bash
/git-push              # Push to tracking branch
/git-push -u           # Push and set upstream (for new branches)
/git-push --force-with-lease  # Safe force push for rebased branches
```

## Workflow

### Step 1: Pre-flight Checks

```bash
# Get current branch
BRANCH=$(git branch --show-current)

# Prevent pushing to protected branches without confirmation
if [[ "$BRANCH" == "main" || "$BRANCH" == "master" ]]; then
    echo "Warning: You're about to push directly to $BRANCH"
    # User should confirm
fi

# Check if there are commits to push
if git diff --quiet @{u}..HEAD 2>/dev/null; then
    echo "No commits to push. Branch is up to date with remote."
    exit 0
fi
```

### Step 2: Check for Upstream

```bash
# Check if upstream is configured
if ! git rev-parse --abbrev-ref --symbolic-full-name @{u} >/dev/null 2>&1; then
    echo "No upstream configured. Setting upstream to origin/$BRANCH"
    NEEDS_UPSTREAM=true
fi
```

### Step 3: Check for Divergence

```bash
# Fetch to ensure we're comparing with latest
git fetch --quiet

# Check if we're behind
BEHIND=$(git rev-list --count HEAD..@{u} 2>/dev/null || echo "0")
if [ "$BEHIND" -gt 0 ]; then
    echo "Remote has $BEHIND commits not in local."
    echo "Pull first with: /git-pull"
    exit 1
fi
```

### Step 4: Execute Push

```bash
# Standard push with upstream
if [ "$NEEDS_UPSTREAM" = true ]; then
    git push -u origin "$BRANCH"
else
    git push
fi

# For force push (after rebase)
# git push --force-with-lease
```

### Step 5: Report Result

Show what was pushed and provide next steps.

## Output Format

### Successful Push

```
Pushed to origin/feat/dark-mode

Commits pushed:
  abc1234 Add theme toggle component
  def5678 Wire up theme context
  ghi9012 Add dark mode styles

Branch is now synced with remote.

Next steps:
  /gh-pr-status        # Check if PR exists
  /commit-push-pr      # Create a PR if needed
```

### New Branch Push

```
Branch feat/new-feature pushed to origin for the first time.

Upstream set: origin/feat/new-feature

Next steps:
  /commit-push-pr      # Create a pull request
  /gh-pr-status        # Check PR status
```

### Push Rejected

```
Push rejected! Remote has changes not in local.

Remote is 2 commits ahead:
  xyz7890 Someone else's commit
  uvw1234 Another commit

Options:
  /git-pull --rebase   # Rebase your changes on top
  /git-pull            # Merge remote changes
```

### Force Push Warning

```
You're about to force push to feat/shared-branch

This will overwrite remote history!

Only do this if:
  - You just rebased and need to update the PR
  - No one else is working on this branch
  - You understand the implications

To proceed:
  git push --force-with-lease

To cancel:
  This skill will not force push automatically.
```

## Safety Features

1. **Protected branch detection**: Warns before pushing to main/master
2. **Divergence check**: Prevents push if remote has new commits
3. **No automatic force push**: Force pushes require explicit action
4. **Force-with-lease**: Recommended over `--force` for safety

## Common Scenarios

| Scenario | Command |
|----------|---------|
| Normal push | `/git-push` |
| New branch first push | `/git-push -u` |
| After rebasing | `/git-push --force-with-lease` |
| To different remote | Use `git push <remote> <branch>` |

## Integration

- Use `/commit` to create commits before pushing
- Use `/git-sync` to check remote status first
- Use `/commit-push-pr` for full commit-push-PR workflow
- Use `/gh-pr-status` after pushing to check PR status
