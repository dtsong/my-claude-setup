---
name: git-status
description: Quick git queries - status, diff, log, blame. Triggers on "git status", "what changed", "show diff", "recent commits".
model: haiku
tools: [Bash]
---

# Git Status

## Scope Constraints

- Read-only git queries: status, diff, log, blame
- Does not modify working tree, stage changes, or create commits
- Does not perform push, pull, merge, rebase, or any remote operations

## Input Sanitization

- File paths for blame/diff: reject `..` traversal, null bytes, and shell metacharacters
- Commit references: alphanumeric, hyphens, tildes, carets, and dots only

Fast git operations for checking repository state.

## Output Format

```
On branch feat/auth-flow (3 ahead of main)

Staged:
  M  src/auth/login.ts
  A  src/auth/session.ts

Unstaged:
  M  src/components/Header.tsx

Recent commits:
  a1b2c3d  feat: add session management
  d4e5f6a  fix: login redirect loop
```

## Common Commands
- `git status` - working tree state
- `git diff` - unstaged changes
- `git diff --staged` - staged changes
- `git log --oneline -10` - recent commits
- `git blame <file>` - line-by-line history
