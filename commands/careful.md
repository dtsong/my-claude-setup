---
name: careful
description: "Activate safety mode — blocks destructive commands (rm -rf, DROP TABLE, git push --force, kubectl delete) via a session-scoped PreToolUse hook. Use when working in production environments or sensitive codebases. Invoke /careful to enable, /careful off to disable."
---

# /careful — Destructive Command Guard

Activates a session-scoped PreToolUse hook that blocks dangerous commands before execution.

## Activation

When invoked, register the hook script:
1. Run: `bash ~/Development/my-claude-setup/hooks/careful-mode.sh enable`
2. Confirm: "Careful mode ON — destructive commands will be blocked."

## Deactivation

When invoked with `off`:
1. Run: `bash ~/Development/my-claude-setup/hooks/careful-mode.sh disable`
2. Confirm: "Careful mode OFF."

## What Gets Blocked

The hook intercepts Bash tool calls and blocks commands matching:
- `rm -rf`, `rm -r /` — recursive deletion
- `DROP TABLE`, `DROP DATABASE`, `TRUNCATE` — database destruction
- `git push --force`, `git push -f` — force push
- `git reset --hard` — hard reset
- `kubectl delete` — Kubernetes resource deletion
- `terraform destroy` — infrastructure destruction
- `docker system prune -a` — full Docker cleanup

## Behavior

- Blocked commands return an error message explaining why
- The user is prompted to confirm or use a safer alternative
- Does not block `--dry-run` variants of dangerous commands
