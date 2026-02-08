---
description: Implement one or more GitHub issues and create PRs. Handles branch creation, implementation, and PR submission. Supports batch implementation.
allowed-tools: Bash(git checkout:*), Bash(git checkout -b:*), Bash(git pull:*), Bash(git push:*), Bash(git add:*), Bash(git commit:*), Bash(git diff:*), Bash(git status:*), Bash(git log:*), Bash(git branch:*), Bash(git stash:*), Bash(gh issue:*), Bash(gh pr:*), Bash(uv:*), Bash(pytest:*), Read, Edit, Write, Glob, Grep
---

# Implement GitHub Issues

You are implementing GitHub issues and creating PRs for them.

## Input

$ARGUMENTS accepts multiple formats:

```
/implement 42                    # Single issue
/implement #42                   # Single issue with hash
/implement 42 43 44              # Multiple issues (separate PRs)
/implement 42,43,44              # Multiple issues (separate PRs)
/implement 42 43 44 --combined   # Multiple issues (single combined PR)
/implement 42-48                 # Range of issues (separate PRs)
/implement 42-48 --combined      # Range of issues (single combined PR)
```

## Modes

### Default Mode: Separate PRs
Each issue gets its own branch and PR. Best for unrelated issues.

### Combined Mode (`--combined`)
All issues implemented in a single branch with one PR. Best for:
- Related issues that share code
- Small issues that make sense together
- Issues within the same phase/milestone

## Git Safety Context

All work in this skill happens on **feature branches** that get submitted as **pull requests** back to main. No changes are ever made directly on main. This means all git operations (branch creation, commits, pushes, PR creation) are safe, reversible workflow steps — the user reviews and merges via the PR. Proceed with git and gh commands without additional confirmation.

## Workflow

### Step 0: Parse Input
```bash
# Extract issue numbers from input
# Handle formats: "42", "#42", "42 43 44", "42,43,44", "42-48"
# Detect --combined flag

ISSUES=(42 43 44)  # parsed list
COMBINED=false     # or true if --combined flag present
```

### Step 1: Fetch All Issue Details
```bash
# Get details for each issue
for ISSUE in "${ISSUES[@]}"; do
  gh issue view $ISSUE --json title,body,labels,milestone,state
done

# Verify all issues are open
# Verify no circular dependencies between selected issues
# Check that blocking issues (outside this batch) are closed
```

### Step 2: Create Branch(es)

**Separate PRs mode:**
```bash
# For each issue, create its own branch
for ISSUE in "${ISSUES[@]}"; do
  git checkout main
  git pull origin main
  git checkout -b feat/$ISSUE-short-description
  # ... implement and commit ...
  git checkout main
done
```

**Combined mode:**
```bash
# Single branch for all issues
git checkout main
git pull origin main

# Branch name combines issue numbers
git checkout -b feat/$FIRST_ISSUE-$LAST_ISSUE-combined-description
# Example: feat/42-44-phase1-gates
```

### Step 3: Implement Features

**Separate PRs mode:**
For each issue independently:
1. Checkout issue branch
2. Implement that issue's requirements only
3. Test
4. Commit
5. Move to next issue

**Combined mode:**
1. Stay on combined branch
2. Implement each issue's requirements
3. Commit after each issue (separate commits, or logical groupings)
4. Test the full implementation together
5. Single push at end

### Step 4: Validate Implementation
```bash
# Run linting
uv run ruff check src/

# Run tests
uv run pytest tests/ -v

# Run specific tests for new code
uv run pytest tests/test_new_feature.py -v
```

### Step 5: Commit Changes

**Separate PRs mode:**
```bash
git add .
git commit -m "feat: implement security scan gate

- Add bandit integration for Python security scanning
- Configure severity thresholds in .ai-review.yaml
- Add SecurityGateResult dataclass
- Integrate into review pipeline

Implements #42"
```

**Combined mode:**
```bash
# Option A: One commit per issue
git add src/gates/security_gate.py tests/test_security_gate.py
git commit -m "feat: implement security scan gate

Implements #42"

git add src/gates/coverage_gate.py tests/test_coverage_gate.py
git commit -m "feat: implement coverage gate

Implements #43"

# Option B: Single commit for all
git add .
git commit -m "feat: implement Phase 1 gates

- Security scan gate with bandit integration
- Coverage gate with pytest-cov support
- Dependency audit gate with pip-audit

Implements #42, #43, #44"
```

### Step 6: Push and Create PR(s)

**Separate PRs mode:**
```bash
for ISSUE in "${ISSUES[@]}"; do
  git checkout feat/$ISSUE-description
  git push -u origin HEAD
  
  gh pr create \
    --title "feat: implement $(gh issue view $ISSUE --json title -q .title)" \
    --body "## Summary
Implements #$ISSUE.

## Changes
$(git diff main --stat)

## Testing
- [ ] Unit tests passing
- [ ] Integration tested

Closes #$ISSUE" \
    --label "roadmap"
done
```

**Combined mode:**
```bash
git push -u origin HEAD

# PR references all issues
gh pr create \
  --title "feat: implement Phase 1 gates (#42, #43, #44)" \
  --body "## Summary
Implements multiple related issues in a single PR.

## Issues Addressed
$(for ISSUE in "${ISSUES[@]}"; do echo "- #$ISSUE: $(gh issue view $ISSUE --json title -q .title)"; done)

## Changes
$(git diff main --stat)

## Testing
- [ ] All unit tests passing
- [ ] Integration tested
- [ ] Each issue's acceptance criteria met

Closes #42, closes #43, closes #44" \
  --label "roadmap"
```

### Step 7: Report Completion

**Separate PRs mode:**
```
✅ Completed 3 issues with 3 PRs:

| Issue | PR | Title |
|-------|-----|-------|
| #42 | #101 | Security scan gate |
| #43 | #102 | Coverage gate |
| #44 | #103 | Dependency audit gate |
```

**Combined mode:**
```
✅ Completed 3 issues with 1 combined PR:

PR #101: feat: implement Phase 1 gates
Closes: #42, #43, #44

Commits:
- feat: implement security scan gate (#42)
- feat: implement coverage gate (#43)  
- feat: implement dependency audit gate (#44)
```

## Important Rules

1. **Always reference issues** in commits and PR body using `#N` syntax
2. **Use "Closes #N"** in PR body to auto-close issues on merge (comma-separated for multiple)
3. **Run tests before pushing** - don't create PRs with failing tests
4. **Follow existing patterns** - match code style, file organization, naming conventions
5. **Update documentation** if features are user-facing
6. **Respect dependencies** - if issue A depends on issue B, implement B first (or use --combined)
7. **Keep combined PRs focused** - don't combine unrelated issues just because you can

## Decision Guide: Separate vs Combined

**Use separate PRs when:**
- Issues are in different phases
- Issues touch completely different parts of the codebase
- You want independent review/merge cycles
- Issues have different complexity levels

**Use combined PR when:**
- Issues are in the same phase/milestone
- Issues share common code or patterns
- Issues are small and related
- Implementing one makes implementing others trivial
- You want atomic deployment of related features

## Example Usage

```bash
# Single issue
/implement 42
/implement #42

# Multiple issues, separate PRs (default)
/implement 42 43 44
/implement #42 #43 #44
/implement 42,43,44

# Multiple issues, single combined PR
/implement 42 43 44 --combined
/implement 42-44 --combined

# Issue range, separate PRs  
/implement 42-48

# Phase-based batch (all Phase 1 issues)
/implement 42 43 44 45 --combined   # All Phase 1 gates in one PR
```

## Handling Failures

**If implementation fails for one issue in a batch:**

Separate mode:
- Continue with other issues
- Report which issues succeeded/failed
- Failed issue can be retried independently

Combined mode:
- Stop and report the blocker
- Options: fix and continue, or abort and split into separate PRs
- Don't leave partial implementations uncommitted

