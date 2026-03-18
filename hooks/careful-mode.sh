#!/usr/bin/env bash
set -euo pipefail

# careful-mode.sh — PreToolUse hook for blocking destructive commands
# Usage: careful-mode.sh enable|disable
# When enabled, creates a state file that a PreToolUse hook can check

STATE_FILE="${HOME}/.claude/.careful-mode"

case "${1:-}" in
  enable)
    touch "$STATE_FILE"
    echo "careful-mode: enabled"
    ;;
  disable)
    rm -f "$STATE_FILE"
    echo "careful-mode: disabled"
    ;;
  check)
    # Called by PreToolUse hook — check if command is destructive
    if [[ ! -f "$STATE_FILE" ]]; then
      exit 0  # Not in careful mode
    fi

    TOOL_NAME="${TOOL_NAME:-}"
    TOOL_INPUT="${TOOL_INPUT:-}"

    if [[ "$TOOL_NAME" != "Bash" ]]; then
      exit 0  # Only check Bash commands
    fi

    # Destructive patterns
    BLOCKED_PATTERNS=(
      'rm -rf'
      'rm -r /'
      'DROP TABLE'
      'DROP DATABASE'
      'TRUNCATE TABLE'
      'git push --force'
      'git push -f '
      'git reset --hard'
      'kubectl delete'
      'terraform destroy'
      'docker system prune -a'
    )

    for pattern in "${BLOCKED_PATTERNS[@]}"; do
      if echo "$TOOL_INPUT" | grep -qi "$pattern"; then
        # Allow --dry-run variants
        if echo "$TOOL_INPUT" | grep -qi "\-\-dry-run"; then
          exit 0
        fi
        echo "BLOCKED by /careful: detected '$pattern' in command."
        echo "Use /careful off to disable, or use --dry-run first."
        exit 2
      fi
    done
    exit 0
    ;;
  *)
    echo "Usage: careful-mode.sh {enable|disable|check}"
    exit 1
    ;;
esac
