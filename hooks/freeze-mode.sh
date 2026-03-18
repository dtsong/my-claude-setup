#!/usr/bin/env bash
set -euo pipefail

# freeze-mode.sh — PreToolUse hook for blocking writes to frozen files
# Usage: freeze-mode.sh enable "<pattern>" | disable | check

STATE_FILE="${HOME}/.claude/.freeze-patterns"

case "${1:-}" in
  enable)
    PATTERN="${2:?Pattern required. Usage: freeze-mode.sh enable '<pattern>'}"
    echo "$PATTERN" >> "$STATE_FILE"
    echo "freeze-mode: pattern '$PATTERN' added"
    ;;
  disable)
    rm -f "$STATE_FILE"
    echo "freeze-mode: all patterns cleared"
    ;;
  check)
    # Called by PreToolUse hook
    if [[ ! -f "$STATE_FILE" ]]; then
      exit 0  # No freeze active
    fi

    TOOL_NAME="${TOOL_NAME:-}"
    FILE_PATH="${FILE_PATH:-}"

    # Only check Edit and Write tools
    if [[ "$TOOL_NAME" != "Edit" && "$TOOL_NAME" != "Write" ]]; then
      exit 0
    fi

    if [[ -z "$FILE_PATH" ]]; then
      exit 0
    fi

    while IFS= read -r pattern; do
      [[ -z "$pattern" ]] && continue
      # Use bash pattern matching
      # shellcheck disable=SC2254
      case "$(basename "$FILE_PATH")" in
        $pattern)
          echo "BLOCKED by /freeze: file '$(basename "$FILE_PATH")' matches frozen pattern '$pattern'."
          echo "Run /freeze off to unfreeze."
          exit 2
          ;;
      esac
    done < "$STATE_FILE"
    exit 0
    ;;
  *)
    echo "Usage: freeze-mode.sh {enable <pattern>|disable|check}"
    exit 1
    ;;
esac
