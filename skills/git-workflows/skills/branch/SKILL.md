---
name: "Git Branch"
description: "Create new branches with naming conventions"
triggers:
  - "git branch"
  - "new branch"
  - "create branch"
  - "start feature"
  - "start bugfix"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Write operation — creates new local branches and switches to them
- Does not push to remote — use push or sync skill for that
- Does not delete branches — use delete-branch skill for that
- Does not create PRs — use github-workflow for that

## Input Sanitization

- Branch names: only alphanumeric characters, hyphens, underscores, and forward slashes. Reject spaces, `..`, shell metacharacters, or null bytes.
- Base branch (`--from`): must be a valid existing ref. Reject shell metacharacters and `..` traversal.

# /git-branch - Create New Branch

Create a new branch with proper naming conventions, optionally from a specific base.

## Usage

```bash
/git-branch feat/dark-mode           # Create feature branch
/git-branch fix/login-bug            # Create bugfix branch
/git-branch feat/api-v2 --from main  # Create from specific base
/git-branch --suggest "add login"    # Suggest branch name from description
```

## Naming Conventions

| Prefix | Use For | Example |
|--------|---------|---------|
| `feat/` | New features | `feat/dark-mode` |
| `fix/` | Bug fixes | `fix/login-validation` |
| `refactor/` | Code refactoring | `refactor/auth-module` |
| `docs/` | Documentation | `docs/api-reference` |
| `test/` | Test additions/fixes | `test/auth-coverage` |
| `chore/` | Maintenance tasks | `chore/update-deps` |
| `hotfix/` | Urgent production fixes | `hotfix/security-patch` |

## Workflow

### Step 1: Validate Branch Name

```bash
BRANCH_NAME="$1"

# Check for valid prefix
if [[ ! "$BRANCH_NAME" =~ ^(feat|fix|refactor|docs|test|chore|hotfix)/ ]]; then
    echo "Warning: Branch name doesn't follow conventions."
    echo "Recommended prefixes: feat/, fix/, refactor/, docs/, test/, chore/, hotfix/"
fi

# Check for invalid characters
if [[ "$BRANCH_NAME" =~ [[:space:]] ]]; then
    echo "Error: Branch name cannot contain spaces. Use hyphens instead."
    exit 1
fi

# Check length
if [ ${#BRANCH_NAME} -gt 50 ]; then
    echo "Warning: Branch name is quite long. Consider shortening."
fi
```

### Step 2: Check for Uncommitted Changes

```bash
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo "You have uncommitted changes."
    echo "Options:"
    echo "  /git-stash - Stash changes first"
    echo "  /commit - Commit changes first"
    exit 1
fi
```

### Step 3: Determine Base Branch

```bash
# Default to current branch, or use specified base
BASE_BRANCH="${FROM_BRANCH:-$(git branch --show-current)}"

# Fetch to ensure we have latest
git fetch origin "$BASE_BRANCH" 2>/dev/null || true
```

### Step 4: Create and Switch to Branch

```bash
# Create branch from base
git checkout -b "$BRANCH_NAME" "$BASE_BRANCH"

# Set up tracking if base has remote
if git rev-parse --verify "origin/$BASE_BRANCH" >/dev/null 2>&1; then
    echo "Created from origin/$BASE_BRANCH (latest)"
fi
```

## Output Format

### Successful Creation

```
Created branch: feat/dark-mode

Base: main (up to date with origin/main)
Current position: abc1234 Latest commit on main

Branch is local only. To publish:
  /git-push -u

Next steps:
  - Make your changes
  - /commit to commit
  - /git-push to publish
  - /commit-push-pr to create PR
```

### Branch Name Suggestion

When using `--suggest`:

```
Suggested branch names for "add user login feature":

  1. feat/user-login (Recommended)
  2. feat/add-user-login
  3. feat/login-feature

Enter your choice or provide custom name:
```

### Branch Already Exists

```
Branch 'feat/dark-mode' already exists.

Options:
  /git-switch feat/dark-mode    # Switch to existing branch
  /git-branch feat/dark-mode-v2 # Create with different name
```

## Branch Name Generator

When `--suggest` is used, generate names based on description:

1. Extract key words from description
2. Remove stop words (a, the, and, etc.)
3. Join with hyphens
4. Add appropriate prefix
5. Limit to ~30 characters

```bash
# Example: "fix the authentication bug in login form"
# Result: fix/auth-bug-login-form
```

## Validation Rules

1. **Must have valid prefix** (warning if missing)
2. **No spaces** (use hyphens)
3. **No special characters** except `-`, `/`, `_`
4. **Reasonable length** (<50 chars recommended)
5. **Lowercase preferred** (warning if uppercase)
6. **No double hyphens or slashes**

## Tips

- Use descriptive but concise names
- Include ticket number if applicable: `feat/JIRA-123-dark-mode`
- Start from an up-to-date base: `--from main` after pulling
- One branch per feature/fix (keep scope small)

## Integration

- Use `/git-switch` to change between branches
- Use `/git-branches` to see all branches
- Use `/commit-push-pr` when ready to create PR

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/naming-conventions.md` | Branch name validation | Branch naming convention rules and prefix definitions |
