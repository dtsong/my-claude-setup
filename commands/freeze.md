---
name: freeze
description: "Freeze files matching a pattern — blocks Edit/Write to matched files via a session-scoped PreToolUse hook. Use when files should not be modified (e.g., during review, or to protect config files). Invoke /freeze '*.config.js' to enable, /freeze off to disable."
---

# /freeze — File Modification Guard

Blocks Edit and Write tool calls to files matching a user-specified pattern.

## Activation

When invoked with a pattern (e.g., `/freeze '*.config.js'`):
1. Run: `bash ~/Development/my-claude-setup/hooks/freeze-mode.sh enable "<pattern>"`
2. Confirm: "Freeze mode ON — files matching `<pattern>` are protected."

## Deactivation

When invoked with `off`:
1. Run: `bash ~/Development/my-claude-setup/hooks/freeze-mode.sh disable`
2. Confirm: "Freeze mode OFF — all files are writable."

## Examples

- `/freeze '*.lock'` — protect lockfiles
- `/freeze 'src/core/**'` — protect core module
- `/freeze '.env*'` — protect environment files
- `/freeze off` — remove all freezes

## Behavior

- Frozen files return an error: "File is frozen by /freeze. Run /freeze off to unfreeze."
- Multiple `/freeze` calls are additive (patterns stack)
- Does not block Read operations — only Edit and Write
