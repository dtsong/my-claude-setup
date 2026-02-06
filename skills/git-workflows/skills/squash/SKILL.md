---
name: "Git Squash"
description: "Squash commits non-interactively for cleaner history"
triggers:
  - "git squash"
  - "squash commits"
  - "clean up commits"
  - "combine commits"
version: "1.0.0"
user_invocable: true
---

# /git-squash - Squash Commits

Combine multiple commits into fewer, cleaner commits non-interactively.

## Usage

```bash
/git-squash 3               # Squash last 3 commits into 1
/git-squash --since main    # Squash all commits since main
/git-squash --all           # Squash all commits on branch into 1
/git-squash --preview       # Show what would be squashed
```

## When to Use

- **Before PR**: Clean up WIP commits into logical units
- **After review**: Squash fixup commits
- **Messy history**: Combine related small commits
- **Before merge**: Create clean, meaningful commits

## Workflow

### Step 1: Determine Commits to Squash

```bash
# Last N commits
SQUASH_COUNT=3

# Or commits since branching from main
SQUASH_COUNT=$(git rev-list --count main..HEAD)

# Show commits that will be squashed
echo "Commits to squash:"
git log --oneline -n "$SQUASH_COUNT"
```

### Step 2: Pre-flight Checks

```bash
# Check for uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "Commit or stash your changes first."
    exit 1
fi

# Ensure we have commits to squash
if [ "$SQUASH_COUNT" -lt 2 ]; then
    echo "Need at least 2 commits to squash."
    exit 1
fi
```

### Step 3: Create Squash Commit Message

```bash
# Gather all commit messages
MESSAGES=$(git log --format="%s" -n "$SQUASH_COUNT" | tac)

# Generate combined message
BRANCH=$(git branch --show-current)
echo "Squashed commits from $BRANCH:"
echo ""
echo "$MESSAGES"
```

### Step 4: Execute Squash (Non-Interactive)

```bash
# Soft reset to keep changes staged
git reset --soft HEAD~"$SQUASH_COUNT"

# Create new commit with combined message
git commit -m "Combined message here"
```

### Step 5: Report Result

Show the squash result and next steps.

## Output Format

### Preview Mode

```
Would squash 5 commits:

  abc1234 WIP: starting feature
  def5678 More work on feature
  ghi9012 Fix typo
  jkl3456 Actually fix the bug
  mno7890 Final touches

Combined changes:
  4 files changed, 123 insertions(+), 45 deletions(-)

  src/components/Feature.tsx
  src/hooks/useFeature.ts
  src/styles/feature.css
  tests/feature.test.ts

Run without --preview to execute.
```

### Successful Squash

```
Squashed 5 commits into 1:

Before:
  abc1234 WIP: starting feature
  def5678 More work on feature
  ghi9012 Fix typo
  jkl3456 Actually fix the bug
  mno7890 Final touches

After:
  xyz7890 Add feature component with styles and tests

Files in squashed commit:
  src/components/Feature.tsx
  src/hooks/useFeature.ts
  src/styles/feature.css
  tests/feature.test.ts

Note: History was rewritten. If already pushed:
  git push --force-with-lease
```

### Squash All Since Main

```
Squashing all commits since main (7 commits)...

Before:
  (7 commits with various WIP messages)

After:
  feat: Add complete dark mode implementation

  - Theme toggle component
  - System theme detection
  - Persistent preference storage
  - Updated color palette

Ready for PR! Run:
  /git-push --force-with-lease
  /commit-push-pr
```

## Commit Message Strategies

### Option 1: Single Summary

```
feat: Add user authentication

Implements login, logout, and session management.
```

### Option 2: Bullet Points (for larger squashes)

```
feat: Add user authentication

- Add login form component
- Implement session management
- Add logout functionality
- Add remember me option
- Add password reset flow
```

### Option 3: Preserve Original Messages

```
feat: Add user authentication

Squashed commits:
- Add login form component
- Wire up authentication API
- Add session storage
- Fix validation bugs
- Add tests
```

## Interactive Alternative

For more control, use interactive rebase:

```bash
# Interactive rebase for last 5 commits
git rebase -i HEAD~5

# In editor, change 'pick' to 'squash' (or 's') for commits to combine
# Then edit the combined commit message
```

Note: Claude cannot run interactive commands, but can guide you through them.

## Safety Notes

1. **Only squash unpushed commits**: Or commits on your personal branch
2. **Never squash shared history**: Others may have based work on it
3. **Force push needed**: After squashing pushed commits
4. **Backup first**: If unsure, create a backup branch

```bash
# Create backup before squashing
git branch backup-before-squash
```

## Integration

- Use before `/git-push` to clean up history
- Use before `/commit-push-pr` for clean PRs
- Use `/git-push --force-with-lease` after squashing pushed commits
- Consider PR squash-merge instead for simple cases
