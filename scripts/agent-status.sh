#!/bin/bash
# agent-status.sh - Show status of all agent worktrees
# Usage: agent-status.sh [--verbose]

VERBOSE="${1:-}"

# Get repo root and name
REPO_ROOT=$(git rev-parse --show-toplevel 2>/dev/null)
if [ -z "$REPO_ROOT" ]; then
    echo "Error: Not in a git repository"
    exit 1
fi

REPO_NAME=$(basename "$REPO_ROOT")
WORKTREE_BASE="$HOME/.claude-worktrees/$REPO_NAME"

# Check if worktree directory exists
if [ ! -d "$WORKTREE_BASE" ]; then
    echo "No worktrees found for $REPO_NAME"
    echo ""
    echo "Use /launch to start working on a task"
    exit 0
fi

# Get current time for age calculations
NOW=$(date +%s)

# Function to get relative time
relative_time() {
    local timestamp=$1
    local diff=$((NOW - timestamp))

    if [ $diff -lt 60 ]; then
        echo "just now"
    elif [ $diff -lt 3600 ]; then
        echo "$((diff / 60)) min ago"
    elif [ $diff -lt 86400 ]; then
        echo "$((diff / 3600)) hours ago"
    else
        echo "$((diff / 86400)) days ago"
    fi
}

# Function to determine status
get_status() {
    local worktree_path=$1
    local last_commit_time=$2
    local diff=$((NOW - last_commit_time))

    # Check for completion marker
    if git -C "$worktree_path" log -1 --pretty=%s 2>/dev/null | grep -q "Task complete:"; then
        echo "Complete"
        return
    fi

    # Check if stale (no commits in 2+ hours)
    if [ $diff -gt 7200 ]; then
        echo "Stale"
        return
    fi

    echo "Working"
}

# Header
echo ""
echo "Active Worktrees for $REPO_NAME:"
echo ""

# Track if any are complete
COMPLETE_BRANCHES=""

# List all worktrees
for worktree in "$WORKTREE_BASE"/*/; do
    [ -d "$worktree" ] || continue

    worktree="${worktree%/}"
    branch=$(basename "$worktree")

    # Get task from .claude-task file
    task_file="$worktree/.claude-task"
    if [ -f "$task_file" ]; then
        # Extract task (second non-empty line after "# Current Task")
        task=$(sed -n '/^# Current Task$/,/^##/{/^# Current Task$/d;/^##/d;/^$/d;p;q}' "$task_file" | head -1)
    else
        task="Unknown task"
    fi

    # Truncate task for display
    [ ${#task} -gt 35 ] && task="${task:0:32}..."

    # Get last commit time
    last_commit_epoch=$(git -C "$worktree" log -1 --pretty=%ct 2>/dev/null || echo "0")
    last_commit_rel=$(relative_time "$last_commit_epoch")

    # Determine status
    status=$(get_status "$worktree" "$last_commit_epoch")

    # Track complete branches
    [ "$status" = "Complete" ] && COMPLETE_BRANCHES="$COMPLETE_BRANCHES $branch"

    # Status emoji
    case "$status" in
        "Working")  emoji="🔄" ;;
        "Complete") emoji="✅" ;;
        "Stale")    emoji="⚠️" ;;
        *)          emoji="❓" ;;
    esac

    # Print row
    printf "%s %-20s %-35s %-10s %s\n" "$emoji" "$branch" "$task" "$status" "$last_commit_rel"

    # Verbose: show recent commits
    if [ "$VERBOSE" = "--verbose" ]; then
        echo "   Recent commits:"
        git -C "$worktree" log -3 --pretty="   - %s (%cr)" 2>/dev/null || echo "   (no commits)"
        echo ""
    fi
done

# Summary
echo ""
if [ -n "$COMPLETE_BRANCHES" ]; then
    echo "Ready to merge:$COMPLETE_BRANCHES"
    echo ""
fi

echo "Quick actions:"
echo "  /merge <branch>    - Merge completed work"
echo "  /launch \"task\"     - Start new agent"
