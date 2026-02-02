---
name: git-status
description: Quick git queries - status, diff, log, blame. Triggers on "git status", "what changed", "show diff", "recent commits".
model: haiku
tools: [Bash]
---

# Git Status

Fast git operations for checking repository state.

## Common Commands
- `git status` - working tree state
- `git diff` - unstaged changes
- `git diff --staged` - staged changes
- `git log --oneline -10` - recent commits
- `git blame <file>` - line-by-line history
