---
name: "Git Branches"
description: "List and visualize branch status"
triggers:
  - "git branches"
  - "list branches"
  - "show branches"
  - "branch status"
  - "all branches"
version: "1.0.0"
user_invocable: true
---

# /git-branches - List and Visualize Branches

Show all branches with their status, tracking info, and sync state.

## Usage

```bash
/git-branches              # List all local branches with status
/git-branches --all        # Include remote branches
/git-branches --merged     # Only show merged branches
/git-branches --no-merged  # Only show unmerged branches
/git-branches --stale      # Show branches with deleted remotes
```

## Workflow

### Step 1: Fetch Latest Remote Info

```bash
# Fetch to get accurate remote status
git fetch --all --prune --quiet
```

### Step 2: Get Branch Information

```bash
# List local branches with tracking info
git branch -vv

# For each branch, calculate ahead/behind
for branch in $(git branch --format='%(refname:short)'); do
    upstream=$(git rev-parse --abbrev-ref "$branch@{u}" 2>/dev/null)
    if [ -n "$upstream" ]; then
        ahead=$(git rev-list --count "$upstream..$branch")
        behind=$(git rev-list --count "$branch..$upstream")
        echo "$branch: $ahead ahead, $behind behind of $upstream"
    else
        echo "$branch: no upstream"
    fi
done
```

### Step 3: Check Merge Status

```bash
# Check if branch is merged into main
git branch --merged main
git branch --no-merged main
```

### Step 4: Detect Stale Branches

```bash
# Branches whose remote has been deleted
git branch -vv | grep ': gone]'
```

## Output Format

### Standard View

```
Branches (4 local, 6 remote)

* feat/dark-mode          abc1234 [origin/feat/dark-mode: ahead 2]
    Add theme toggle component

  main                    def5678 [origin/main]
    Latest release

  feat/user-auth          ghi9012 [origin/feat/user-auth: behind 3]
    Add login form

  fix/old-bug             jkl3456 [origin: gone]
    Fix deprecated (remote deleted)

Legend:
  * = current branch
  ahead N = local commits not pushed
  behind N = remote commits not pulled
  gone = remote branch deleted

Quick actions:
  /git-switch <branch>      # Switch to branch
  /git-delete-branch <name> # Delete branch
  /git-sync                 # Fetch updates
```

### Merged Branches

```
Branches merged into main:

  fix/login-bug           (merged 3 days ago)
  feat/old-feature        (merged 1 week ago)
  chore/cleanup           (merged 2 weeks ago)

These branches can be safely deleted with:
  /git-delete-branch --merged
```

### Stale Branches

```
Stale branches (remote deleted):

  feat/abandoned-feature  [origin: gone] - Remote deleted
  fix/old-bug             [origin: gone] - Remote deleted

These branches have no remote tracking anymore.
Clean up with:
  /git-delete-branch feat/abandoned-feature
  /git-delete-branch --stale  # Delete all stale
```

### All Branches (--all)

```
Local branches:
* feat/dark-mode    abc1234 [ahead 2]
  main              def5678 [up to date]

Remote branches (origin):
  origin/main
  origin/feat/dark-mode
  origin/feat/user-auth
  origin/feat/api-v2
  origin/HEAD -> origin/main

Remote branches not checked out locally:
  origin/feat/api-v2      # /git-switch feat/api-v2 to check out
```

## Visual Indicators

| Symbol | Meaning |
|--------|---------|
| `*` | Current branch |
| `ahead N` | N commits to push |
| `behind N` | N commits to pull |
| `gone` | Remote branch deleted |
| `[up to date]` | Synced with remote |
| `[no upstream]` | No remote tracking |

## Branch Health Summary

At the end of output, show summary:

```
Summary:
  Current: feat/dark-mode
  Total: 4 local, 6 remote
  Ahead: 1 branch needs push
  Behind: 1 branch needs pull
  Stale: 2 branches (remote deleted)
  Merged: 3 branches can be deleted
```

## Integration

- Use `/git-switch <branch>` to change branches
- Use `/git-delete-branch` to clean up branches
- Use `/git-sync` to update remote information
- Use `/git-pull` to sync branches that are behind
