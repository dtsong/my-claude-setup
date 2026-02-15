---
name: "Git Stash"
description: "Stash management - save, pop, list, and drop stashed changes"
triggers:
  - "git stash"
  - "stash changes"
  - "save my work"
  - "stash list"
  - "pop stash"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Write operation — saves and restores uncommitted changes to/from the stash stack
- Does not create commits on any branch — stashes are stored separately
- Does not push, fetch, or interact with remotes
- `clear` subcommand is destructive — permanently deletes all stashes

## Input Sanitization

- Stash messages: reject null bytes. All other printable characters allowed.
- Stash references: must match `stash@{N}` format where N is a non-negative integer. Reject arbitrary strings, shell metacharacters, or null bytes.
- Subcommands: only `save`, `pop`, `apply`, `list`, `show`, `drop`, `clear` accepted.

# /git-stash - Stash Management

Save, restore, list, and manage stashed changes.

## Usage

```bash
/git-stash                    # Stash all changes (default)
/git-stash save "message"     # Stash with descriptive message
/git-stash pop                # Apply and remove most recent stash
/git-stash apply              # Apply stash but keep it
/git-stash list               # List all stashes
/git-stash show               # Show changes in most recent stash
/git-stash show stash@{2}     # Show changes in specific stash
/git-stash drop               # Delete most recent stash
/git-stash drop stash@{2}     # Delete specific stash
/git-stash clear              # Delete all stashes (use with caution)
```

## Workflow

### Stash Changes (Default)

```bash
# Check if there are changes to stash
if git diff --quiet && git diff --cached --quiet; then
    echo "No changes to stash."
    exit 0
fi

# Show what will be stashed
git status --short

# Stash with automatic message
git stash push -m "WIP on $(git branch --show-current): $(date '+%Y-%m-%d %H:%M')"

# Or with custom message
git stash push -m "Custom message here"
```

### Include Untracked Files

```bash
# Include untracked files
git stash push -u -m "Including untracked files"

# Include everything (even ignored files)
git stash push -a -m "Including all files"
```

### Pop Stash

```bash
# Apply most recent and remove from stash list
git stash pop

# Apply specific stash
git stash pop stash@{2}
```

### Apply Without Removing

```bash
# Apply but keep in stash list (useful for applying to multiple branches)
git stash apply

# Apply specific stash
git stash apply stash@{1}
```

### List Stashes

```bash
# List all stashes with details
git stash list --format="%gd: %s (%cr)"
```

### Show Stash Contents

```bash
# Show diff of most recent stash
git stash show -p

# Show specific stash
git stash show -p stash@{2}

# Show just file names
git stash show --name-only
```

### Drop Stash

```bash
# Remove most recent stash
git stash drop

# Remove specific stash
git stash drop stash@{2}

# Clear all stashes
git stash clear
```

## Output Format

### After Stashing

```
Stashed changes on feat/dark-mode

Changes stashed:
  M src/components/Theme.tsx
  M src/hooks/useTheme.ts
  A src/styles/dark.css

Stash saved as: stash@{0}
Message: "WIP on feat/dark-mode: 2025-01-25 10:30"

To restore: /git-stash pop
```

### Stash List

```
Your stashes:

  stash@{0}: WIP on feat/dark-mode: toggle component (2 hours ago)
  stash@{1}: WIP on main: experimental changes (1 day ago)
  stash@{2}: WIP on feat/auth: login form backup (3 days ago)

Total: 3 stashes

Commands:
  /git-stash pop           # Apply stash@{0}
  /git-stash show stash@{1}  # View stash contents
  /git-stash drop stash@{2}  # Delete specific stash
```

### Pop Result

```
Applied stash@{0} to feat/dark-mode

Restored changes:
  M src/components/Theme.tsx
  M src/hooks/useTheme.ts
  A src/styles/dark.css

Stash removed from list.
```

### Pop With Conflicts

```
Conflict while applying stash!

Conflicting files:
  - src/components/Theme.tsx

The stash was NOT dropped.

Options:
  /git-conflicts          # Resolve conflicts
  git stash drop          # Drop stash after resolving
  git checkout --theirs . # Keep current, discard stash
  git checkout --ours .   # Keep stash, discard current
```

## Tips

1. **Always use messages**: `git stash push -m "descriptive message"` makes stashes easier to manage
2. **Include untracked**: Use `-u` flag to include new files
3. **Apply vs Pop**: Use `apply` if you might need the stash again
4. **Branch-aware**: Stashes work across branches - useful for moving work

## Common Patterns

```bash
# Quick save before switching branches
/git-stash save "before switching to main"
/git-switch main

# Pull updates then restore
/git-stash
/git-pull
/git-stash pop

# Move changes to a new branch
/git-stash
/git-branch feat/new-feature
/git-switch feat/new-feature
/git-stash pop
```

## Integration

- Use before `/git-pull` if you have uncommitted changes
- Use before `/git-switch` to safely change branches
- Use `/git-stash pop` after operations complete
