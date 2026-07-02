#!/usr/bin/env bash
# Fail-soft dispatcher for session telemetry (issue #59, AC-001..AC-003).
# Resolves the private telemetry hook from CLAUDE_TELEMETRY_HOOK; if the target
# does not exist, exits 0 silently so clones without the private repo never
# see hook errors on tool events.
HOOK_PATH="${CLAUDE_TELEMETRY_HOOK:-$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py}"
[ -f "$HOOK_PATH" ] || exit 0
exec python3 "$HOOK_PATH" "$@"
