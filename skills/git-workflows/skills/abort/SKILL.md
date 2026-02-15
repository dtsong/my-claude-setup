---
name: "Git Abort"
description: "Abort failed merge, rebase, or cherry-pick operations"
triggers:
  - "git abort"
  - "abort merge"
  - "abort rebase"
  - "cancel merge"
  - "cancel rebase"
  - "undo merge"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Write operation — aborts in-progress merge, rebase, cherry-pick, or revert to restore prior HEAD state
- Does not discard committed work — only cancels uncommitted operation state
- Does not push, fetch, or interact with remotes
- Does not resolve conflicts — use conflicts skill for that

## Input Sanitization

- Operation type: must be one of `merge`, `rebase`, `cherry-pick`, `revert`, or omitted for auto-detect. Reject any other value.

# /git-abort - Abort In-Progress Operations

Safely abort a failed or unwanted merge, rebase, cherry-pick, or revert operation.

## Usage

```bash
/git-abort           # Auto-detect and abort current operation
/git-abort merge     # Explicitly abort merge
/git-abort rebase    # Explicitly abort rebase
/git-abort cherry-pick  # Abort cherry-pick
/git-abort revert    # Abort revert
```

## Workflow

### Step 1: Detect In-Progress Operation

```bash
# Check for various in-progress states
if [ -d .git/rebase-merge ] || [ -d .git/rebase-apply ]; then
    OPERATION="rebase"
elif [ -f .git/MERGE_HEAD ]; then
    OPERATION="merge"
elif [ -f .git/CHERRY_PICK_HEAD ]; then
    OPERATION="cherry-pick"
elif [ -f .git/REVERT_HEAD ]; then
    OPERATION="revert"
else
    echo "No operation in progress to abort."
    exit 0
fi

echo "Detected in-progress: $OPERATION"
```

### Step 2: Show Current State

```bash
# Show what files are in conflict
echo "Current status:"
git status --short

# Show conflicting files
echo "Conflicting files:"
git diff --name-only --diff-filter=U
```

### Step 3: Confirm and Abort

```bash
case "$OPERATION" in
    "merge")
        git merge --abort
        ;;
    "rebase")
        git rebase --abort
        ;;
    "cherry-pick")
        git cherry-pick --abort
        ;;
    "revert")
        git revert --abort
        ;;
esac
```

### Step 4: Verify Clean State

```bash
# Confirm we're back to clean state
echo "Restored to previous state."
git status --short
git log --oneline -1
```

## Output Format

### Abort Merge

```
Aborting merge...

Previous state:
  Merging main into feat/dark-mode
  Conflicts in 2 files

Merge aborted successfully!

Current state:
  Branch: feat/dark-mode
  Status: Clean working directory
  HEAD: abc1234 Your last commit before merge

What to do next:
  /git-merge-main    # Try merge again after preparation
  /git-rebase        # Try rebase instead (cleaner history)
  /git-stash         # Stash any partial work
```

### Abort Rebase

```
Aborting rebase...

Rebase was in progress:
  Rebasing feat/dark-mode onto main
  Stopped at commit def5678

Rebase aborted successfully!

Current state:
  Branch: feat/dark-mode
  Status: Clean working directory
  HEAD: ghi9012 (back to before rebase)

Your commits are restored to their original state.

Alternative approaches:
  /git-merge-main    # Merge instead of rebase
  /git-conflicts     # Get help resolving conflicts next time
```

### Abort Cherry-Pick

```
Aborting cherry-pick...

Was cherry-picking:
  Commit abc1234 from main

Cherry-pick aborted!

Current state:
  Branch: feat/dark-mode
  Status: Clean

The cherry-picked commit was not applied.
```

### No Operation to Abort

```
No operation in progress.

Current state:
  Branch: feat/dark-mode
  Status: Clean working directory

Nothing to abort.
```

## What Each Abort Does

| Operation | What Abort Does |
|-----------|-----------------|
| `merge --abort` | Removes merge state, restores HEAD |
| `rebase --abort` | Stops rebase, restores original branch state |
| `cherry-pick --abort` | Cancels cherry-pick, cleans up |
| `revert --abort` | Cancels revert, cleans up |

## When to Abort

### Abort if:
- Conflicts are too complex to resolve now
- You realize you're merging the wrong branch
- You want to try a different approach
- Something doesn't look right

### Don't abort if:
- You've already resolved some conflicts and want to keep them
- You just need more time (conflicts will wait)
- You want to save partial work (stash first)

## Recovery Tips

After aborting, you can:

1. **Try again with preparation**:
   ```bash
   /git-stash         # Save any work
   /git-sync          # Make sure you're up to date
   /git-merge-main    # Try again
   ```

2. **Use a different strategy**:
   ```bash
   # If merge had too many conflicts, try rebase
   /git-rebase

   # Or vice versa
   /git-merge-main
   ```

3. **Get help with conflicts**:
   ```bash
   /git-conflicts     # Guided conflict resolution
   ```

## Integration

- Use when `/git-merge-main` or `/git-rebase` results in conflicts
- Use `/git-conflicts` to get help before aborting
- After abort, try `/git-stash` to save any partial work
