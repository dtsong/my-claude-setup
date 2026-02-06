# /g - Git Porcelain

Fast, workspace-aware git operations.

## Usage

```
/g                          # Quick status (branch, dirty, ahead/behind)
/g save                     # Smart commit (auto conventional message)
/g save "message"           # Commit with custom message
/g push                     # Push current branch to origin
/g sync                     # Pull remote changes with conflict handling
/g diff                     # Changes since last push
/g log                      # Recent commits + changelog
/g undo                     # Revert last commit (keep changes)
/g stash [pop|list]         # Stash operations
/g feat <name>              # Create feature branch
/g pr                       # Push + create PR
```

## Instructions

Parse `$ARGUMENTS` to determine the subcommand. If no arguments, run **Status** mode.

### Workspace Detection

Detect the workspace dynamically — **never hardcode paths**:

```bash
# Detect workspace from git
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || echo "")"

if [ -z "$WORKSPACE" ]; then
    echo "Not in a git repository."
    exit 1
fi

# Detect default branch
DEFAULT_BRANCH=$(git -C $WORKSPACE symbolic-ref refs/remotes/origin/HEAD 2>/dev/null | sed 's@^refs/remotes/origin/@@')
if [ -z "$DEFAULT_BRANCH" ]; then
    DEFAULT_BRANCH="main"
fi
```

---

## Mode: Status (default — `/g`)

Quick status overview. Run these in parallel:

```bash
# Branch info
BRANCH=$(git -C $WORKSPACE branch --show-current)

# Dirty state
MODIFIED=$(git -C $WORKSPACE diff --name-only | wc -l | tr -d ' ')
STAGED=$(git -C $WORKSPACE diff --cached --name-only | wc -l | tr -d ' ')
UNTRACKED=$(git -C $WORKSPACE ls-files --others --exclude-standard | wc -l | tr -d ' ')

# Ahead/behind
git -C $WORKSPACE fetch origin --quiet 2>/dev/null
AHEAD=$(git -C $WORKSPACE rev-list --count origin/$DEFAULT_BRANCH..HEAD 2>/dev/null || echo "?")
BEHIND=$(git -C $WORKSPACE rev-list --count HEAD..origin/$DEFAULT_BRANCH 2>/dev/null || echo "?")

# Last commit
LAST=$(git -C $WORKSPACE log --oneline -1)
```

Display:

```
<branch>  ↑<ahead> ↓<behind>  <modified>M <staged>S <untracked>U

  Last: <hash> <message>
```

If clean and synced:
```
<branch>  clean, synced with origin

  Last: <hash> <message>
```

---

## Mode: Save (`/g save` or `/g save "message"`)

Smart commit with conventional message generation.

### 1. Check for Changes

```bash
git -C $WORKSPACE status --porcelain
```

If no changes: "Nothing to save — working tree is clean."

### 2. Stage Relevant Files

```bash
# Get all changed + untracked files
git -C $WORKSPACE diff --name-only
git -C $WORKSPACE diff --name-only --cached
git -C $WORKSPACE ls-files --others --exclude-standard
```

Stage files selectively. **NEVER stage:**
- `.env`, `.env.local`, `.env.*`
- `credentials.json`, `secrets.*`, `*.pem`, `*.key`
- `node_modules/`, `.next/`, `dist/`, `__pycache__/`

```bash
git -C $WORKSPACE add <files...>
```

### 3. Generate Commit Message

If user provided a message (`/g save "message"`):
- Use that message, prefix with conventional type if not already present

If no message (`/g save`):
- Analyze the diff to determine type and generate descriptive message
- Use conventional commit format: `type: short description`

### 4. Commit

```bash
git -C $WORKSPACE commit -m "$(cat <<'EOF'
<type>: <description>

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
EOF
)"
```

### 5. Display Result

```
Saved  <hash> <type>: <description>
  <N> files changed, <insertions>(+), <deletions>(-)
```

---

## Mode: Push (`/g push`)

### 1. Check for Uncommitted Changes

```bash
if ! git -C $WORKSPACE diff --quiet || ! git -C $WORKSPACE diff --cached --quiet; then
    echo "WARNING: You have uncommitted changes."
fi
```

If uncommitted changes exist, ask whether to commit first.

### 2. Fetch and Check Divergence

```bash
git -C $WORKSPACE fetch origin
AHEAD=$(git -C $WORKSPACE rev-list --count origin/$DEFAULT_BRANCH..HEAD)
BEHIND=$(git -C $WORKSPACE rev-list --count HEAD..origin/$DEFAULT_BRANCH)
```

If behind > 0: "Remote has <N> new commits. Run `/g sync` first?" Ask to continue or sync first.

### 3. Push

```bash
git -C $WORKSPACE push -u origin $(git -C $WORKSPACE branch --show-current)
```

### 4. Display

```
Pushed  ↑<N> commits to origin

  <branch> → origin/<branch>
```

---

## Mode: Sync (`/g sync`)

Pull remote changes with automatic conflict handling.

### 1. Stash Uncommitted Work

```bash
STASHED=false
if ! git -C $WORKSPACE diff --quiet || ! git -C $WORKSPACE diff --cached --quiet; then
    git -C $WORKSPACE stash push -u -m "g-sync-stash-$(date +%s)"
    STASHED=true
fi
```

### 2. Fetch and Merge

```bash
git -C $WORKSPACE fetch origin

BEHIND=$(git -C $WORKSPACE rev-list --count HEAD..origin/$DEFAULT_BRANCH)
if [ "$BEHIND" -eq 0 ]; then
    echo "Already up to date with origin/$DEFAULT_BRANCH"
else
    git -C $WORKSPACE merge origin/$DEFAULT_BRANCH --no-edit
fi
```

### 3. Handle Merge Conflicts

If conflicts occur:
1. List conflicting files: `git -C $WORKSPACE diff --name-only --diff-filter=U`
2. For each file: read, understand both sides, resolve intelligently
3. Stage resolved files
4. Commit merge resolution

### 4. Restore Stash

```bash
if [ "$STASHED" = true ]; then
    git -C $WORKSPACE stash pop
fi
```

### 5. Display

```
Synced  ↓<N> commits from origin/$DEFAULT_BRANCH

  <commit summaries>

  Your uncommitted changes: restored
```

Or: "Already synced — no new commits from origin."

---

## Mode: Diff (`/g diff`)

Show all changes since last push.

```bash
git -C $WORKSPACE fetch origin

# Unpushed commits
echo "Unpushed commits:"
git -C $WORKSPACE log --oneline origin/$DEFAULT_BRANCH..HEAD

# Uncommitted changes
echo "Staged:"
git -C $WORKSPACE diff --cached --stat

echo "Unstaged:"
git -C $WORKSPACE diff --stat

echo "Untracked:"
git -C $WORKSPACE ls-files --others --exclude-standard
```

Display all sections. Summarize counts at the top.

---

## Mode: Log (`/g log`)

Recent activity overview.

```bash
# Last 15 commits with authors
git -C $WORKSPACE log --oneline --format="%h %s (%an, %ar)" -15

# Unpushed count
AHEAD=$(git -C $WORKSPACE rev-list --count origin/$DEFAULT_BRANCH..HEAD)

# Contributor activity (last 7 days)
git -C $WORKSPACE shortlog -sn --since="7 days ago" --no-merges
```

Also read CHANGELOG.md (if exists) and show latest 3 entries.

Display:

```
Recent Activity

  <hash> <message> (<author>, <time>)
  ...

  Unpushed: <N> commits

Contributors (7d):
  <N>  <Author>
```

---

## Mode: Undo (`/g undo`)

Revert the last commit, keeping changes unstaged.

### 1. Safety Check

```bash
# Block if last commit is a merge
if git -C $WORKSPACE rev-parse HEAD^2 >/dev/null 2>&1; then
    echo "Last commit is a merge — use `git revert` instead."
    exit 1
fi
```

### 2. Show What Will Be Undone

```bash
git -C $WORKSPACE log --oneline -1
git -C $WORKSPACE show --stat HEAD
```

### 3. Reset

```bash
git -C $WORKSPACE reset --soft HEAD~1
git -C $WORKSPACE reset HEAD
```

### 4. Display

```
Undone  <hash> <message>

  Changes are now unstaged. Use `/g save` to recommit.
```

---

## Mode: Stash (`/g stash`, `/g stash pop`, `/g stash list`)

### Stash Save (`/g stash`)

```bash
if git -C $WORKSPACE diff --quiet && git -C $WORKSPACE diff --cached --quiet; then
    echo "Nothing to stash."
    exit 0
fi

CHANGED=$(git -C $WORKSPACE diff --name-only | head -3 | tr '\n' ', ' | sed 's/,$//')
git -C $WORKSPACE stash push -u -m "WIP: $CHANGED ($(date +%Y-%m-%d\ %H:%M))"
```

Display: `Stashed  WIP: <files>  — Use /g stash pop to restore.`

### Stash Pop (`/g stash pop`)

```bash
git -C $WORKSPACE stash show  # Preview
git -C $WORKSPACE stash pop
```

If conflicts, resolve them. Display what was restored.

### Stash List (`/g stash list`)

```bash
git -C $WORKSPACE stash list --format="%gd: %s"
```

---

## Mode: Feature Branch (`/g feat <name>`)

Create a feature branch from an up-to-date default branch.

### 1. Sync First

```bash
git -C $WORKSPACE fetch origin
git -C $WORKSPACE merge origin/$DEFAULT_BRANCH --no-edit
```

### 2. Create Branch

```bash
BRANCH_NAME="feat/<name>"
git -C $WORKSPACE checkout -b "$BRANCH_NAME"
```

### 3. Display

```
Created  feat/<name>  from $DEFAULT_BRANCH (synced)

  Ready for development. Use `/g save` to commit, `/g pr` when done.
```

---

## Mode: Pull Request (`/g pr`)

Push and create a GitHub PR.

### 1. Verify Not on Default Branch

```bash
BRANCH=$(git -C $WORKSPACE branch --show-current)
if [ "$BRANCH" = "$DEFAULT_BRANCH" ]; then
    echo "Create a feature branch first: /g feat <name>"
    exit 1
fi
```

### 2. Push Branch

```bash
git -C $WORKSPACE push -u origin "$BRANCH"
```

### 3. Create PR

Analyze commits on this branch vs default. Draft a PR title and body:

```bash
cd $WORKSPACE && gh pr create --base $DEFAULT_BRANCH --title "<title>" --body "$(cat <<'EOF'
## Summary
<bullet points from commits>

## Test plan
<checklist>

Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

### 4. Display

```
PR Created  <url>

  <branch> → $DEFAULT_BRANCH
  <N> commits, <files> files changed
```

---

## Conventional Commit Types

| Type | Use For |
|------|---------|
| `feat:` | New feature or functionality |
| `fix:` | Bug fix |
| `refactor:` | Code restructuring (no behavior change) |
| `docs:` | Documentation only |
| `style:` | Formatting, whitespace |
| `test:` | Adding or updating tests |
| `chore:` | Config, dependencies, tooling |
| `perf:` | Performance improvement |
| `merge:` | Merge resolution |

## Pre-Commit Hook Failures

If a pre-commit hook fails:
1. Read the error message
2. Fix the issue (lint, format, type errors)
3. Re-stage fixed files
4. Create a NEW commit (never amend after hook failure)
