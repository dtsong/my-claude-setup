---
name: "Git Conflicts"
description: "Guided conflict resolution for merge and rebase conflicts"
triggers:
  - "git conflicts"
  - "fix conflicts"
  - "resolve conflicts"
  - "merge conflicts"
  - "conflict help"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-write operation — reads conflicting files and may stage resolved files via `git add`
- Does not create commits — user must run `git merge --continue` or `git rebase --continue` after resolution
- Does not push to remote or abort operations — use abort skill to cancel, push skill to publish
- Scoped to files with active conflict markers only

## Input Sanitization

- File paths (`--file`): reject `..` traversal, null bytes, and shell metacharacters. Must be a path within the repository working tree.

# /git-conflicts - Guided Conflict Resolution

Get help resolving merge, rebase, or cherry-pick conflicts.

## Usage

```bash
/git-conflicts           # Analyze and help with current conflicts
/git-conflicts --status  # Show conflict status only
/git-conflicts --file src/component.tsx  # Focus on specific file
```

## Workflow

### Step 1: Detect Conflict State

```bash
# Check what operation is in progress
if [ -d .git/rebase-merge ] || [ -d .git/rebase-apply ]; then
    OPERATION="rebase"
elif [ -f .git/MERGE_HEAD ]; then
    OPERATION="merge"
elif [ -f .git/CHERRY_PICK_HEAD ]; then
    OPERATION="cherry-pick"
else
    echo "No conflicts detected."
    exit 0
fi
```

### Step 2: List Conflicting Files

```bash
# Get list of conflicting files
CONFLICTS=$(git diff --name-only --diff-filter=U)

echo "Conflicting files:"
echo "$CONFLICTS"

# Count conflicts
COUNT=$(echo "$CONFLICTS" | wc -l)
echo "Total: $COUNT files with conflicts"
```

### Step 3: Analyze Each Conflict

For each conflicting file, Claude will:

1. Read the file content
2. Identify conflict markers (`<<<<<<<`, `=======`, `>>>>>>>`)
3. Explain what each side changed
4. Suggest resolution strategy

### Step 4: Guide Resolution

Provide clear instructions for each file.

## Output Format

### Conflict Analysis

```
Conflict Resolution Guide

Operation: Merging main into feat/dark-mode

Conflicting files (2):

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. src/components/Header.tsx

Conflict type: Both branches modified the same lines

Your changes (HEAD):
  - Added dark mode toggle button
  - Changed header background color

Their changes (main):
  - Updated logo component
  - Changed header padding

Suggested resolution:
  Keep both changes - they affect different aspects.

  1. Keep the dark mode toggle (your change)
  2. Keep the logo update (their change)
  3. Merge the style changes carefully

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

2. src/styles/theme.css

Conflict type: Same CSS property modified differently

Your changes (HEAD):
  --header-bg: #1a1a2e;  /* dark mode */

Their changes (main):
  --header-bg: #ffffff;  /* light mode default */

Suggested resolution:
  Both are needed! Create theme variants:

  :root {
    --header-bg: #ffffff;
  }

  [data-theme="dark"] {
    --header-bg: #1a1a2e;
  }

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Next steps:
  1. Edit conflicting files (remove conflict markers)
  2. git add <resolved-files>
  3. git merge --continue  (or git rebase --continue)

Or abort:
  /git-abort
```

### Per-File Conflict Detail

When focusing on a specific file:

```
Analyzing: src/components/Header.tsx

Conflict region 1 (lines 45-62):

<<<<<<< HEAD (your changes)
import { ThemeToggle } from './ThemeToggle';

export function Header() {
  return (
    <header className="bg-slate-900 dark:bg-slate-950">
      <Logo />
      <ThemeToggle />
=======
import { NewLogo } from './NewLogo';

export function Header() {
  return (
    <header className="bg-white p-4">
      <NewLogo />
>>>>>>> main (their changes)

Analysis:
  - You added ThemeToggle import and component
  - They updated Logo to NewLogo
  - Background colors differ (you: dark, they: light default)

Resolution suggestion:
  Combine both changes:

  import { ThemeToggle } from './ThemeToggle';
  import { NewLogo } from './NewLogo';

  export function Header() {
    return (
      <header className="bg-white dark:bg-slate-950 p-4">
        <NewLogo />
        <ThemeToggle />
```

## Resolution Strategies

### Strategy 1: Accept Ours
Keep your version, discard theirs.
```bash
git checkout --ours <file>
git add <file>
```

### Strategy 2: Accept Theirs
Keep their version, discard yours.
```bash
git checkout --theirs <file>
git add <file>
```

### Strategy 3: Manual Merge
Edit file to combine both changes (most common).
```bash
# Edit file to resolve
vim <file>
git add <file>
```

### Strategy 4: Use Merge Tool
```bash
git mergetool <file>
```

## Common Conflict Patterns

| Pattern | Typical Resolution |
|---------|-------------------|
| Same line, different changes | Manual merge combining intent |
| Deleted vs modified | Decide if deletion or modification wins |
| Added file in both | Merge contents or pick one |
| Renamed differently | Pick the better name, merge content |
| Structural refactor | Usually accept refactor, reapply changes |

## After Resolving

```bash
# Mark as resolved
git add <resolved-file>

# Continue the operation
git merge --continue    # for merge
git rebase --continue   # for rebase
git cherry-pick --continue  # for cherry-pick
```

## Prevention Tips

1. **Sync often**: Regularly merge/rebase from main
2. **Small PRs**: Fewer changes = fewer conflicts
3. **Communicate**: Know what others are working on
4. **Atomic commits**: Easier to understand conflicts

## Integration

- Use `/git-abort` if conflicts are too complex
- Use `/git-merge-main` or `/git-rebase` to start merge/rebase
- After resolving, use `/git-push` to update remote
