---
name: "Git Switch"
description: "Switch branches safely with uncommitted change handling"
triggers:
  - "git switch"
  - "git checkout"
  - "switch branch"
  - "change branch"
  - "go to branch"
version: "1.0.0"
user_invocable: true
---

# /git-switch - Switch Branches Safely

Switch to a different branch with smart handling of uncommitted changes.

## Usage

```bash
/git-switch main                # Switch to main
/git-switch feat/dark-mode      # Switch to feature branch
/git-switch -                   # Switch to previous branch
/git-switch --create feat/new   # Create and switch
```

## Workflow

### Step 1: Check for Uncommitted Changes

```bash
# Check for both staged and unstaged changes
HAS_CHANGES=false
if ! git diff --quiet || ! git diff --cached --quiet; then
    HAS_CHANGES=true
fi

# Also check for untracked files
UNTRACKED=$(git ls-files --others --exclude-standard | wc -l)
```

### Step 2: Handle Uncommitted Changes

If changes exist, present options:

```bash
if [ "$HAS_CHANGES" = true ]; then
    echo "You have uncommitted changes:"
    git status --short

    # Options presented to user via AskUserQuestion:
    # 1. Stash and switch (will restore after)
    # 2. Carry changes to new branch
    # 3. Discard changes and switch
    # 4. Cancel
fi
```

### Step 3: Verify Target Branch Exists

```bash
TARGET_BRANCH="$1"

# Check local
if git show-ref --verify --quiet "refs/heads/$TARGET_BRANCH"; then
    echo "Switching to local branch: $TARGET_BRANCH"

# Check remote
elif git show-ref --verify --quiet "refs/remotes/origin/$TARGET_BRANCH"; then
    echo "Creating local tracking branch from origin/$TARGET_BRANCH"
    git checkout -b "$TARGET_BRANCH" "origin/$TARGET_BRANCH"
    exit 0

else
    echo "Branch '$TARGET_BRANCH' not found locally or on origin."
    echo "Did you mean to create it? Use: /git-branch $TARGET_BRANCH"
    exit 1
fi
```

### Step 4: Execute Switch

```bash
# Standard switch
git switch "$TARGET_BRANCH"

# Or if carrying changes
git switch "$TARGET_BRANCH"  # Changes come along if no conflict

# Previous branch shortcut
git switch -
```

### Step 5: Post-Switch Status

```bash
# Show where we are now
git status -sb

# If we stashed, offer to restore
if [ "$DID_STASH" = true ]; then
    echo "Stashed changes are available. Restore with: /git-stash pop"
fi
```

## Output Format

### Clean Switch

```
Switched to branch: feat/dark-mode

Branch status:
  Tracking: origin/feat/dark-mode
  Behind: 0 commits
  Ahead: 2 commits

Recent commits on this branch:
  abc1234 Add theme toggle
  def5678 Wire up context
```

### Switch with Stash

```
Uncommitted changes detected:
  M src/components/Header.tsx
  A src/styles/new.css

Changes stashed automatically.
Switched to branch: main

To restore your changes:
  /git-stash pop

Or keep them stashed:
  /git-stash list
```

### Switch with Carried Changes

```
Switched to branch: feat/dark-mode

Uncommitted changes carried over:
  M src/components/Header.tsx

These changes are now on feat/dark-mode (not committed).
```

### Switch Failed - Would Overwrite

```
Cannot switch to main!

Your local changes to these files would be overwritten:
  - src/components/Header.tsx

Options:
  /git-stash              # Stash changes first
  /commit                 # Commit changes first
  git checkout -- <file>  # Discard specific changes
```

## Special Shortcuts

| Command | Description |
|---------|-------------|
| `/git-switch -` | Switch to previous branch |
| `/git-switch main` | Switch to main branch |
| `/git-switch --create name` | Create new branch and switch |

## Tab Completion Helper

When branch name is partial or ambiguous, show matches:

```
Multiple branches match 'feat/':

  feat/dark-mode
  feat/user-auth
  feat/api-v2

Specify full name to switch.
```

## Integration

- Use `/git-branches` to see all available branches
- Use `/git-stash` for manual stash control
- Use `/git-branch` to create new branches
- Use `/git-sync` after switching to check for updates
