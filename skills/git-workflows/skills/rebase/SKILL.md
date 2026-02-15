---
name: "Git Rebase"
description: "Rebase current branch onto main with guidance"
triggers:
  - "git rebase"
  - "rebase onto main"
  - "rebase branch"
  - "rebase on main"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Destructive write operation — rewrites commit history by replaying commits onto a new base
- Fetches from remote to update the target branch before rebasing
- Does not push to remote — use push skill with `--force-with-lease` after rebase
- Does not resolve conflicts — use conflicts skill if rebase produces conflicts
- Should not be used on shared branches — only personal feature branches

## Input Sanitization

- Target branch name: only alphanumeric characters, hyphens, underscores, and forward slashes. Reject spaces, `..`, shell metacharacters, or null bytes.
- Flags: only `--continue`, `--abort` accepted. Reject arbitrary strings.

# /git-rebase - Rebase Onto Main

Rebase your feature branch onto the latest main for a clean, linear history.

## Usage

```bash
/git-rebase              # Rebase onto main
/git-rebase develop      # Rebase onto develop
/git-rebase --continue   # Continue after resolving conflicts
/git-rebase --abort      # Abort rebase in progress
```

## When to Use Rebase

- **Before creating a PR**: Clean history before review
- **Updating feature branch**: Alternative to merge for cleaner history
- **Personal branches**: When you're the only one working on the branch

## When NOT to Rebase

- **Shared branches**: Never rebase branches others are working on
- **Already pushed commits**: Changes history that others may have
- **After merge commits**: Can cause complex conflicts

## Workflow

### Step 1: Pre-flight Checks

```bash
CURRENT=$(git branch --show-current)

# Cannot rebase main
if [ "$CURRENT" = "main" ] || [ "$CURRENT" = "master" ]; then
    echo "Cannot rebase main onto itself."
    exit 1
fi

# Check for uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "You have uncommitted changes."
    echo "Stash or commit them first:"
    echo "  /git-stash"
    echo "  /commit"
    exit 1
fi
```

### Step 2: Update Target Branch

```bash
# Fetch latest main
git fetch origin main

# Show what will happen
COMMITS=$(git log --oneline origin/main..HEAD | wc -l)
echo "Will rebase $COMMITS commits onto origin/main"
```

### Step 3: Preview Potential Conflicts

```bash
# Files that might conflict
echo "Files modified in both branches:"
git diff --name-only origin/main...HEAD
```

### Step 4: Execute Rebase

```bash
# Standard rebase onto main
git rebase origin/main
```

### Step 5: Handle Result

On success or conflict, provide appropriate guidance.

## Output Format

### Successful Rebase

```
Rebasing feat/dark-mode onto main...

Rebased 3 commits:
  abc1234 Add theme toggle component
  def5678 Wire up theme context
  ghi9012 Add dark mode styles

New base: origin/main (xyz7890)

Your branch now has a clean, linear history!

Note: You'll need to force push to update remote:
  git push --force-with-lease

Or use: /git-push --force-with-lease
```

### Already Up To Date

```
Branch feat/dark-mode is already based on latest main.

No rebase needed.
```

### Rebase Conflicts

```
Conflict during rebase!

Currently rebasing commit: abc1234 Add theme toggle

Conflicting files:
  - src/components/Theme.tsx

To resolve:
  1. Edit the conflicting files
  2. git add <resolved-files>
  3. git rebase --continue

Or abort entirely:
  /git-abort
  (or: git rebase --abort)

Tip: Use /git-conflicts for guided resolution
```

### Continue After Conflicts

```
To continue the rebase after resolving conflicts:

  git add <resolved-files>
  git rebase --continue

Remaining commits to rebase: 2

Current status:
  [x] abc1234 Add theme toggle (resolved)
  [ ] def5678 Wire up theme context
  [ ] ghi9012 Add dark mode styles
```

## After Rebasing

Since rebase rewrites history, you need to force push:

```bash
# Safe force push (fails if remote changed)
git push --force-with-lease

# Regular force push (use carefully)
git push --force
```

**Warning**: Only force push if:
- You're the only one working on the branch
- You understand that remote history will be rewritten
- You've communicated with collaborators if any

## Rebase vs Merge Comparison

```
Before (merge):
main:    A---B---C---F---G
              \     /
feature:       D---E

After merge, feature has merge commit.

Before (rebase):
main:    A---B---C
              \
feature:       D---E

After rebase:
main:    A---B---C
                  \
feature:           D'--E'

Rebase creates linear history (D and E rebased as D' and E').
```

## Safety Tips

1. **Never rebase shared branches**: Only your personal feature branches
2. **Use force-with-lease**: Safer than `--force`
3. **Have a backup**: Know how to recover if needed
4. **Test after rebase**: Ensure everything still works

## Integration

- Use `/git-merge-main` instead for shared branches
- Use `/git-conflicts` for conflict resolution help
- Use `/git-abort` to cancel a problematic rebase
- Use `/git-push --force-with-lease` after successful rebase
