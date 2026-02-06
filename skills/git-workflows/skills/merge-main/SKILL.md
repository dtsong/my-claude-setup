---
name: "Git Merge Main"
description: "Merge main branch into current feature branch"
triggers:
  - "git merge main"
  - "merge main"
  - "update from main"
  - "sync with main"
  - "get latest main"
version: "1.0.0"
user_invocable: true
---

# /git-merge-main - Merge Main Into Feature Branch

Merge the latest main branch into your current feature branch to get updates.

## Usage

```bash
/git-merge-main            # Merge main into current branch
/git-merge-main develop    # Merge develop instead of main
/git-merge-main --no-commit  # Merge but don't commit (for review)
```

## When to Use

- Your feature branch is behind main
- You need changes from main to continue your work
- Before creating a PR (to ensure no conflicts)
- When main has critical fixes you need

## Workflow

### Step 1: Pre-flight Checks

```bash
# Get current branch
CURRENT=$(git branch --show-current)

# Cannot merge main into main
if [ "$CURRENT" = "main" ] || [ "$CURRENT" = "master" ]; then
    echo "Already on main branch. Nothing to merge."
    echo "Did you mean /git-pull?"
    exit 1
fi

# Check for uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "You have uncommitted changes."
    echo "Options:"
    echo "  /git-stash - Stash changes first"
    echo "  /commit - Commit changes first"
    exit 1
fi
```

### Step 2: Update Main

```bash
# Fetch latest main from remote
git fetch origin main:main 2>/dev/null || git fetch origin main

# Show what will be merged
echo "Commits from main to be merged:"
git log --oneline HEAD..origin/main | head -20
```

### Step 3: Check for Potential Conflicts

```bash
# Preview merge (without committing)
if ! git merge --no-commit --no-ff origin/main 2>/dev/null; then
    echo "Merge will have conflicts."
    git merge --abort
    # Show conflicting files
    git diff --name-only --diff-filter=U
fi
```

### Step 4: Execute Merge

```bash
# Perform the merge
git merge origin/main --no-ff -m "Merge main into $CURRENT"

# Or without commit for review
git merge origin/main --no-commit --no-ff
```

### Step 5: Report Result

Show merge result and any follow-up needed.

## Output Format

### Clean Merge

```
Merging main into feat/dark-mode...

Merged 5 commits from main:
  abc1234 Fix security vulnerability
  def5678 Update dependencies
  ghi9012 Improve performance
  jkl3456 Add new API endpoint
  mno7890 Documentation updates

Files updated:
  package.json
  src/api/endpoints.ts
  src/utils/security.ts
  README.md

Merge complete! Your branch now includes all changes from main.

Next steps:
  - Test your feature still works
  - /git-push to update remote branch
```

### Already Up To Date

```
Branch feat/dark-mode is already up to date with main.

No merge needed.
```

### Merge Conflicts

```
Merge conflicts detected!

Conflicting files:
  - src/components/Header.tsx (both modified)
  - src/styles/theme.css (both modified)

To resolve:
  /git-conflicts         # Get help resolving

After resolving:
  git add <resolved-files>
  git commit

To abort:
  /git-abort
```

### No-Commit Preview

When using `--no-commit`:

```
Merge staged but not committed.

Changes from main:
  M src/api/endpoints.ts
  M package.json
  A src/utils/newHelper.ts

Review the changes, then:
  git commit -m "Merge main into feat/dark-mode"

Or abort:
  git merge --abort
```

## Best Practices

1. **Always fetch first**: Ensures you have the latest main
2. **Check status before**: No uncommitted changes
3. **Test after merge**: Ensure your feature still works
4. **Commit message**: Use descriptive merge message
5. **Consider rebase**: For cleaner history, use `/git-rebase` instead

## Merge vs Rebase

| Merge | Rebase |
|-------|--------|
| Preserves complete history | Creates linear history |
| Shows when integration happened | Looks like sequential development |
| Better for shared branches | Better for personal branches |
| Non-destructive | Rewrites commit history |

## Integration

- Use `/git-sync` first to see what's on main
- Use `/git-rebase` for cleaner history (alternative)
- Use `/git-conflicts` if merge has conflicts
- Use `/git-abort` to cancel a failed merge
