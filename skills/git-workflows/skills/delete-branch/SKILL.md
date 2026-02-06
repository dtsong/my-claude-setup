---
name: "Git Delete Branch"
description: "Delete local and remote branches with safety checks"
triggers:
  - "git delete branch"
  - "delete branch"
  - "remove branch"
  - "cleanup branch"
  - "git branch -d"
version: "1.0.0"
user_invocable: true
---

# /git-delete-branch - Delete Branches Safely

Delete local and/or remote branches with safety checks.

## Usage

```bash
/git-delete-branch feat/old-feature        # Delete local branch
/git-delete-branch feat/old-feature --remote  # Also delete remote
/git-delete-branch --merged                 # Delete all merged branches
/git-delete-branch --stale                  # Delete branches with gone remotes
/git-delete-branch --force feat/unmerged   # Force delete unmerged
```

## Workflow

### Step 1: Validate Branch

```bash
BRANCH="$1"

# Cannot delete current branch
CURRENT=$(git branch --show-current)
if [ "$BRANCH" = "$CURRENT" ]; then
    echo "Cannot delete current branch. Switch first:"
    echo "  /git-switch main"
    exit 1
fi

# Check if branch exists
if ! git show-ref --verify --quiet "refs/heads/$BRANCH"; then
    echo "Branch '$BRANCH' does not exist locally."
    exit 1
fi
```

### Step 2: Safety Checks

```bash
# Check if branch is merged
if ! git merge-base --is-ancestor "$BRANCH" main 2>/dev/null; then
    echo "Warning: Branch is NOT fully merged into main."
    echo "Commits that would be lost:"
    git log main.."$BRANCH" --oneline

    # Require --force for unmerged branches
    if [ "$FORCE" != true ]; then
        echo "Use --force to delete anyway."
        exit 1
    fi
fi

# Check for unpushed commits
UPSTREAM=$(git rev-parse --abbrev-ref "$BRANCH@{u}" 2>/dev/null)
if [ -n "$UPSTREAM" ]; then
    UNPUSHED=$(git rev-list --count "$UPSTREAM..$BRANCH" 2>/dev/null || echo "0")
    if [ "$UNPUSHED" -gt 0 ]; then
        echo "Warning: Branch has $UNPUSHED unpushed commits."
    fi
fi
```

### Step 3: Delete Local Branch

```bash
# Safe delete (fails if not merged)
git branch -d "$BRANCH"

# Force delete (even if not merged)
git branch -D "$BRANCH"
```

### Step 4: Delete Remote Branch (if requested)

```bash
if [ "$DELETE_REMOTE" = true ]; then
    # Check if remote exists
    if git show-ref --verify --quiet "refs/remotes/origin/$BRANCH"; then
        git push origin --delete "$BRANCH"
        echo "Deleted remote branch: origin/$BRANCH"
    else
        echo "No remote branch to delete."
    fi
fi
```

## Output Format

### Successful Deletion

```
Deleted branch: feat/old-feature

Branch was merged into main.
Local branch removed.

Remote branch: Not deleted (use --remote to delete)
```

### With Remote Deletion

```
Deleted branch: feat/old-feature

Local: Deleted
Remote: Deleted (origin/feat/old-feature)

Branch fully cleaned up.
```

### Unmerged Branch Warning

```
Cannot delete: feat/wip-feature

This branch is NOT merged into main.
You would lose these commits:

  abc1234 Work in progress
  def5678 More changes
  ghi9012 Almost done

Options:
  /git-delete-branch --force feat/wip-feature  # Delete anyway
  /git-switch feat/wip-feature                 # Continue working
  /git-merge-main                              # Merge main into it first
```

### Batch Delete Merged

```
Finding branches merged into main...

Branches to delete:
  fix/login-bug
  feat/completed-feature
  chore/old-cleanup

Delete these 3 branches? (y/n)

Deleted:
  fix/login-bug
  feat/completed-feature
  chore/old-cleanup

Kept (current or protected):
  main
  develop
```

### Stale Branch Cleanup

```
Finding stale branches (remote deleted)...

Stale branches:
  feat/abandoned [origin: gone]
  fix/obsolete [origin: gone]

Delete these 2 stale local branches? (y/n)

Deleted:
  feat/abandoned
  fix/obsolete
```

## Protected Branches

These branches cannot be deleted without explicit `--force`:

- `main`
- `master`
- `develop`
- `production`

```
Cannot delete protected branch: main

Use --force if you really mean it (not recommended).
```

## Common Patterns

```bash
# After PR is merged
/git-switch main
/git-pull
/git-delete-branch feat/merged-pr --remote

# Cleanup old branches
/git-branches --merged
/git-delete-branch --merged

# Clean stale tracking
/git-delete-branch --stale
```

## Integration

- Use `/git-branches` to see all branches and their status
- Use `/git-switch` to change to a different branch first
- Use after `/gh-pr-merge` to clean up the merged branch
