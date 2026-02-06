#!/bin/bash
# task-board.sh - Task board operations for multi-agent coordination
# Usage: ./task-board.sh <command> [args]

set -e

SHARED_DIR="$HOME/.claude/agent-context/shared"
BOARD_FILE="$SHARED_DIR/task-board.md"
LOCK_FILE="$SHARED_DIR/claims.lock"

# Ensure shared directory exists
mkdir -p "$SHARED_DIR"
mkdir -p "$SHARED_DIR/broadcasts"

acquire_lock() {
    local agent_id="${1:-unknown}"
    local max_attempts=3
    local attempt=0
    local lock_timeout=30  # seconds

    while [ $attempt -lt $max_attempts ]; do
        if [ -f "$LOCK_FILE" ]; then
            # Check if lock is stale
            local lock_time
            lock_time=$(stat -f "%m" "$LOCK_FILE" 2>/dev/null || stat -c "%Y" "$LOCK_FILE" 2>/dev/null)
            local now
            now=$(date +%s)
            local age=$((now - lock_time))

            if [ $age -gt $lock_timeout ]; then
                # Lock is stale, remove it
                rm -f "$LOCK_FILE"
            else
                # Lock is active, wait
                attempt=$((attempt + 1))
                echo "Lock held by another agent, waiting... (attempt $attempt/$max_attempts)" >&2
                sleep 2
                continue
            fi
        fi

        # Try to acquire lock atomically
        echo "$agent_id|$(date -Iseconds)" > "$LOCK_FILE.$$"
        if mv "$LOCK_FILE.$$" "$LOCK_FILE" 2>/dev/null; then
            echo "Lock acquired"
            return 0
        fi

        attempt=$((attempt + 1))
        sleep 1
    done

    echo "Failed to acquire lock after $max_attempts attempts" >&2
    return 1
}

release_lock() {
    if [ -f "$LOCK_FILE" ]; then
        rm -f "$LOCK_FILE"
        echo "Lock released"
    fi
}

check_stale_claims() {
    local timeout_hours="${1:-4}"
    echo "Checking for claims older than ${timeout_hours}h..."

    if [ ! -f "$BOARD_FILE" ]; then
        echo "No task board found"
        return 0
    fi

    # Extract claimed tasks and check agent activity
    # This outputs task IDs that have stale claims
    grep -A5 'status: claimed' "$BOARD_FILE" 2>/dev/null | grep 'id:' | sed 's/.*id: *"\([^"]*\)".*/\1/' || true
}

init_board() {
    local board_id="$1"
    local project_path="$2"

    if [ -z "$board_id" ] || [ -z "$project_path" ]; then
        echo "Usage: task-board.sh init <board_id> <project_path>"
        return 1
    fi

    if [ -f "$BOARD_FILE" ]; then
        echo "Task board already exists at $BOARD_FILE"
        echo "Use 'task-board.sh reset' to create a new one"
        return 1
    fi

    local timestamp
    timestamp=$(date -Iseconds)

    cat > "$BOARD_FILE" << EOF
---
board_id: "$board_id"
created: "$timestamp"
updated: "$timestamp"
project_path: "$project_path"

settings:
  auto_archive_completed: true
  claim_timeout_hours: 4
  require_workspace_match: false

active_agents: []

tasks: []

completed: []
---

## Task Board: $board_id

### How to Use
- Run \`/task-board\` to view available tasks
- Run \`/claim-task <task-id>\` to claim a task
- Run \`/complete-task\` to mark your current task done
- Run \`/sync-agents\` to see what other agents are doing

### Recent Activity
- $timestamp - Task board created for $project_path
EOF

    echo "Task board created at $BOARD_FILE"
}

reset_board() {
    if [ -f "$BOARD_FILE" ]; then
        local backup="$BOARD_FILE.backup.$(date +%s)"
        mv "$BOARD_FILE" "$backup"
        echo "Backed up existing board to $backup"
    fi
    echo "Board reset. Run 'init' to create a new one."
}

show_board() {
    if [ ! -f "$BOARD_FILE" ]; then
        echo "No task board found. Run: task-board.sh init <board_id> <project_path>"
        return 1
    fi
    cat "$BOARD_FILE"
}

add_task() {
    local task_id="$1"
    local title="$2"
    local priority="${3:-medium}"
    local description="${4:-}"

    if [ -z "$task_id" ] || [ -z "$title" ]; then
        echo "Usage: task-board.sh add-task <task_id> <title> [priority] [description]"
        return 1
    fi

    if [ ! -f "$BOARD_FILE" ]; then
        echo "No task board found. Run init first."
        return 1
    fi

    local timestamp
    timestamp=$(date -Iseconds)

    # Create a temp file with the task inserted
    local tmpfile
    tmpfile=$(mktemp)

    # Read line by line and insert task
    local inserted=false
    local in_tasks=false
    while IFS= read -r line || [[ -n "$line" ]]; do
        # Check if we're at "tasks: []" (empty tasks)
        if [[ "$line" == "tasks: []" ]]; then
            echo "tasks:"
            echo "  - id: \"$task_id\""
            echo "    title: \"$title\""
            echo "    description: \"$description\""
            echo "    priority: $priority"
            echo "    status: available"
            echo "    dependencies: []"
            echo "    created: \"$timestamp\""
            inserted=true
            continue
        fi
        # Check if we're at "tasks:" (non-empty)
        if [[ "$line" == "tasks:" ]]; then
            echo "$line"
            in_tasks=true
            continue
        fi
        # If in tasks section and hit completed:, insert before
        if [[ "$line" == "completed:"* ]] && [[ "$inserted" == false ]]; then
            echo ""
            echo "  - id: \"$task_id\""
            echo "    title: \"$title\""
            echo "    description: \"$description\""
            echo "    priority: $priority"
            echo "    status: available"
            echo "    dependencies: []"
            echo "    created: \"$timestamp\""
            echo ""
            inserted=true
        fi
        echo "$line"
    done < "$BOARD_FILE" > "$tmpfile"

    mv "$tmpfile" "$BOARD_FILE"

    # Update timestamp
    sed -i.bak "s/^updated:.*/updated: \"$timestamp\"/" "$BOARD_FILE" && rm -f "$BOARD_FILE.bak"

    echo "Task $task_id added to board"
}

list_available() {
    if [ ! -f "$BOARD_FILE" ]; then
        echo "No task board found"
        return 1
    fi

    echo "Available tasks:"
    # Extract task blocks with available status
    awk '
        /^  - id:/ { id = $0; gsub(/.*id: *"/, "", id); gsub(/".*/, "", id) }
        /title:/ { title = $0; gsub(/.*title: *"/, "", title); gsub(/".*/, "", title) }
        /status: available/ { print "  " id ": " title }
    ' "$BOARD_FILE" || echo "  (none)"
}

list_claimed() {
    if [ ! -f "$BOARD_FILE" ]; then
        echo "No task board found"
        return 1
    fi

    echo "Claimed tasks:"
    # Extract task blocks with claimed status
    awk '
        /^  - id:/ { id = $0; gsub(/.*id: *"/, "", id); gsub(/".*/, "", id) }
        /title:/ { title = $0; gsub(/.*title: *"/, "", title); gsub(/".*/, "", title) }
        /status: claimed/ { print "  " id ": " title }
    ' "$BOARD_FILE" || echo "  (none)"
}

case "${1:-help}" in
    acquire-lock)
        acquire_lock "$2"
        ;;
    release-lock)
        release_lock
        ;;
    check-stale)
        check_stale_claims "$2"
        ;;
    init)
        init_board "$2" "$3"
        ;;
    reset)
        reset_board
        ;;
    show)
        show_board
        ;;
    add-task)
        add_task "$2" "$3" "$4" "$5"
        ;;
    list-available)
        list_available
        ;;
    list-claimed)
        list_claimed
        ;;
    help|*)
        cat << EOF
task-board.sh - Task board operations for multi-agent coordination

Commands:
  acquire-lock [agent_id]    - Acquire the claims lock
  release-lock               - Release the claims lock
  check-stale [hours]        - Check for stale claims (default: 4h)
  init <board_id> <path>     - Initialize a new task board
  reset                      - Reset the task board (backs up existing)
  show                       - Display the task board
  add-task <id> <title> [priority] [desc] - Add a task
  list-available             - List available tasks
  list-claimed               - List claimed tasks

Files:
  Task Board: $BOARD_FILE
  Lock File:  $LOCK_FILE
  Broadcasts: $SHARED_DIR/broadcasts/
EOF
        ;;
esac
