---
name: "Git Pull"
description: "Pull remote changes with merge or rebase strategy"
triggers:
  - "git pull"
  - "get latest"
  - "pull changes"
  - "update branch"
version: "1.0.0"
user_invocable: true
---

# /git-pull - Pull Remote Changes

Pull changes from remote with configurable strategy (merge or rebase).

## Usage

```bash
/git-pull              # Pull with default strategy (from git config)
/git-pull --rebase     # Pull with rebase
/git-pull --merge      # Pull with merge
/git-pull --ff-only    # Only fast-forward, fail if not possible
```

## Workflow

### Step 1: Pre-flight Checks

```bash
# Check for uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "You have uncommitted changes. Options:"
    echo "  1. /git-stash - Stash changes and continue"
    echo "  2. /commit - Commit changes first"
    echo "  3. Discard changes: git checkout ."
    exit 1
fi

# Verify we have a remote tracking branch
if ! git rev-parse --abbrev-ref --symbolic-full-name @{u} >/dev/null 2>&1; then
    echo "No upstream tracking branch configured."
    echo "Set with: git branch --set-upstream-to=origin/$(git branch --show-current)"
    exit 1
fi
```

### Step 2: Fetch Latest

```bash
git fetch --prune
```

### Step 3: Check Pull Status

```bash
# Count commits behind
BEHIND=$(git rev-list --count HEAD..@{u})
AHEAD=$(git rev-list --count @{u}..HEAD)

echo "Local is $BEHIND commits behind, $AHEAD commits ahead"
```

### Step 4: Execute Pull

Based on strategy requested:

```bash
# Default (from git config)
git pull

# With rebase
git pull --rebase

# With merge (explicit)
git pull --no-rebase

# Fast-forward only
git pull --ff-only
```

### Step 5: Report Result

Show what was pulled and any issues.

## Output Format

### Successful Pull

```
Pulling from origin/main...

Pulled 3 commits:
  abc1234 Fix authentication bug
  def5678 Update dependencies
  ghi9012 Improve error handling

Files updated:
  src/auth/login.ts
  package.json
  package-lock.json

Branch is now up to date with origin/main.
```

### Fast-Forward Not Possible

```
Cannot fast-forward: local and remote have diverged.

Local has 2 commits not on remote:
  xyz7890 Add new feature
  uvw1234 Fix typo

Remote has 3 commits not local:
  abc1234 Other work
  def5678 More changes
  ghi9012 Latest commit

Options:
  /git-pull --rebase   # Rebase your commits on top
  /git-pull --merge    # Create a merge commit
  /git-merge-main      # Merge main into your branch
```

### Conflicts Detected

```
Pull resulted in conflicts!

Conflicting files:
  - src/components/Header.tsx
  - src/styles/theme.css

Next steps:
  /git-conflicts       # Get help resolving conflicts
  git merge --abort    # Or abort and try a different approach
```

## Strategy Selection

| Scenario | Recommended Strategy |
|----------|---------------------|
| Feature branch, no shared commits | `--rebase` (cleaner history) |
| Shared branch, collaborating | `--merge` (preserve history) |
| Main branch, simple update | `--ff-only` (safest) |
| Unsure | Default (uses git config) |

## Integration

- Use `/git-sync` first to preview changes before pulling
- Use `/git-stash` to save uncommitted work before pulling
- Use `/git-conflicts` if pull results in conflicts
- Use `/git-abort` to cancel a failed merge/rebase
