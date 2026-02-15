---
name: "Git Sync"
description: "Fetch and show remote changes without modifying local branch"
triggers:
  - "git sync"
  - "git fetch"
  - "what's new"
  - "check upstream"
  - "sync repo"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-only operation — fetches remote refs and displays status but does not modify local branches or working tree
- Runs `git fetch --prune` which updates remote tracking refs and removes stale ones
- Does not pull, merge, rebase, or push — use pull or push skills for those actions

## Input Sanitization

- Remote name: only alphanumeric characters, hyphens, and underscores. Reject spaces, `..`, shell metacharacters, or null bytes.
- Flags: only `--all` accepted. Reject arbitrary strings.

# /git-sync - Fetch and Show Remote Changes

Fetch the latest changes from remote without modifying your local branch. Shows what's new upstream.

## Usage

```bash
/git-sync              # Fetch all remotes and show status
/git-sync origin       # Fetch specific remote
/git-sync --all        # Fetch all remotes including tags
```

## Workflow

### Step 1: Fetch Remote Changes

```bash
# Fetch from all remotes with prune
git fetch --all --prune
```

### Step 2: Show Current Status

```bash
# Get current branch
git branch --show-current

# Check remote tracking status
git status -sb
```

### Step 3: Show Commits Ahead/Behind

```bash
# Get the remote tracking branch
REMOTE_BRANCH=$(git rev-parse --abbrev-ref --symbolic-full-name @{u} 2>/dev/null)

# If tracking branch exists, show difference
if [ -n "$REMOTE_BRANCH" ]; then
    # Commits behind (on remote but not local)
    git log --oneline HEAD..$REMOTE_BRANCH

    # Commits ahead (on local but not remote)
    git log --oneline $REMOTE_BRANCH..HEAD
fi
```

### Step 4: Show Changed Files Preview

```bash
# Files that would change on pull
git diff --stat HEAD..@{u} 2>/dev/null
```

## Output Format

```
Fetched from origin, upstream

Current branch: feat/dark-mode
Tracking: origin/feat/dark-mode

Behind by 3 commits:
  abc1234 Fix theme persistence
  def5678 Update color palette
  ghi9012 Add system theme detection

Ahead by 1 commit:
  xyz7890 WIP: toggle component

Files that would change on pull:
  src/theme/colors.ts | 12 ++++++------
  src/hooks/useTheme.ts | 45 +++++++++++++++++++++++++++++++++++++++++++++

Next steps:
  /git-pull          # Pull the changes
  /git-stash         # Stash local changes first
```

## Edge Cases

### No Remote Tracking Branch
```
Branch 'feat/local-only' has no upstream tracking branch.

To set tracking:
  git branch --set-upstream-to=origin/feat/local-only

Or push with tracking:
  git push -u origin feat/local-only
```

### Already Up To Date
```
Current branch: main
Tracking: origin/main

Already up to date.
```

### Network Error
```
Failed to fetch from origin: Could not resolve host: github.com

Check your network connection and try again.
```

## Integration

- Run `/git-pull` to apply the fetched changes
- Run `/git-stash` if you have uncommitted changes to save first
- Run `/git-branches` to see status of all branches
