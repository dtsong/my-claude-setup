#!/bin/bash
# run-agent.sh - Wrapper script for running Claude agents with lifecycle management
# Usage: run-agent.sh <worktree-path> <branch-name> [--keep-open]
#
# Features:
# - Runs claude with initial prompt to start task
# - Sends notification on completion
# - Auto-closes terminal after "Task complete:" commit (unless --keep-open)
# - Stays open if agent exits without completing for debugging

set -e

WORKTREE_PATH="$1"
BRANCH="$2"
KEEP_OPEN="false"

# Check for --keep-open flag
for arg in "$@"; do
    if [[ "$arg" == "--keep-open" ]]; then
        KEEP_OPEN="true"
    fi
done

if [[ -z "$WORKTREE_PATH" ]] || [[ -z "$BRANCH" ]]; then
    echo "Usage: run-agent.sh <worktree-path> <branch-name> [--keep-open]"
    exit 1
fi

cd "$WORKTREE_PATH"

echo "=== Agent: $BRANCH ==="
echo "Worktree: $WORKTREE_PATH"
echo "Keep open: $KEEP_OPEN"
echo ""

# Initial prompt for the agent
INITIAL_PROMPT="Read the .claude-task file and complete the task described there. Follow the instructions carefully. Remember to run 'npm run build' before marking the task complete."

# Run claude
claude --dangerously-skip-permissions "$INITIAL_PROMPT"
EXIT_CODE=$?

echo ""
echo "=== Agent exited with code $EXIT_CODE ==="

# Check if task was completed successfully
LAST_COMMIT=$(git log -1 --format='%s' 2>/dev/null || echo "")

if echo "$LAST_COMMIT" | grep -q "Task complete:"; then
    echo "Task completed successfully!"

    # Extract task summary from commit message
    SUMMARY=$(echo "$LAST_COMMIT" | sed 's/Task complete: //')

    # Send notification
    ~/.claude/scripts/notify-complete.sh "$BRANCH" "$SUMMARY"

    if [[ "$KEEP_OPEN" != "true" ]]; then
        echo ""
        echo "Window closing in 5 seconds..."
        echo "(Use --keep-open flag to prevent auto-close)"
        sleep 5
        exit 0
    else
        echo ""
        echo "Window staying open (--keep-open flag set)"
    fi
else
    echo ""
    echo "Agent exited without 'Task complete:' commit."
    echo "Last commit: $LAST_COMMIT"
    echo ""
    echo "Window will stay open for debugging."
    echo "Check git status and logs to understand what happened."
fi

# If we get here, keep the shell open
echo ""
echo "Press Enter to close this window..."
read -r
