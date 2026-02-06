#!/bin/bash
# agent-broadcast.sh - Broadcast and receive agent notifications
# Usage: ./agent-broadcast.sh <command> [args]

set -e

SHARED_DIR="$HOME/.claude/agent-context/shared"
BROADCASTS_DIR="$SHARED_DIR/broadcasts"
SYNC_FILE="$HOME/.claude/agent-context/.last_sync"

mkdir -p "$BROADCASTS_DIR"

send_broadcast() {
    local type="$1"
    local agent_id="$2"
    local task_id="$3"
    local task_title="$4"
    local message="$5"

    if [ -z "$type" ] || [ -z "$agent_id" ]; then
        echo "Usage: agent-broadcast.sh send <type> <agent_id> <task_id> <task_title> <message>"
        return 1
    fi

    local timestamp
    timestamp=$(date -Iseconds)
    local safe_timestamp
    safe_timestamp=$(echo "$timestamp" | tr ':' '-')
    local filename="${safe_timestamp}-${agent_id}.md"

    cat > "$BROADCASTS_DIR/$filename" << EOF
---
type: "$type"
agent_id: "$agent_id"
task_id: "$task_id"
task_title: "$task_title"
timestamp: "$timestamp"
---

## $type: $task_title

**Agent:** $agent_id
**Task:** $task_id
**Time:** $timestamp

### Details
$message
EOF

    echo "$BROADCASTS_DIR/$filename"
}

list_all() {
    if [ -d "$BROADCASTS_DIR" ] && [ "$(ls -A "$BROADCASTS_DIR" 2>/dev/null)" ]; then
        ls -lt "$BROADCASTS_DIR"/*.md 2>/dev/null | head -20
    else
        echo "No broadcasts found"
    fi
}

list_new() {
    if [ -f "$SYNC_FILE" ]; then
        local new_files
        new_files=$(find "$BROADCASTS_DIR" -name "*.md" -newer "$SYNC_FILE" -type f 2>/dev/null | sort -r)
        if [ -n "$new_files" ]; then
            echo "$new_files"
        else
            echo "No new broadcasts since last sync"
        fi
    else
        # No sync file, show last 10
        find "$BROADCASTS_DIR" -name "*.md" -type f 2>/dev/null | sort -r | head -10
    fi
}

count_new() {
    if [ -f "$SYNC_FILE" ]; then
        find "$BROADCASTS_DIR" -name "*.md" -newer "$SYNC_FILE" -type f 2>/dev/null | wc -l | tr -d ' '
    else
        find "$BROADCASTS_DIR" -name "*.md" -type f 2>/dev/null | wc -l | tr -d ' '
    fi
}

show_broadcast() {
    local file="$1"

    if [ -z "$file" ]; then
        echo "Usage: agent-broadcast.sh show <filename>"
        return 1
    fi

    # Handle both full path and just filename
    if [ -f "$file" ]; then
        cat "$file"
    elif [ -f "$BROADCASTS_DIR/$file" ]; then
        cat "$BROADCASTS_DIR/$file"
    else
        echo "Broadcast not found: $file"
        return 1
    fi
}

mark_synced() {
    touch "$SYNC_FILE"
    echo "Sync time updated: $(date -Iseconds)"
}

last_sync() {
    if [ -f "$SYNC_FILE" ]; then
        stat -f "%Sm" -t "%Y-%m-%d %H:%M:%S" "$SYNC_FILE" 2>/dev/null || \
        stat -c "%y" "$SYNC_FILE" 2>/dev/null | cut -d. -f1
    else
        echo "Never synced"
    fi
}

cleanup_old() {
    local days="${1:-7}"
    local count
    count=$(find "$BROADCASTS_DIR" -name "*.md" -mtime "+$days" -type f 2>/dev/null | wc -l | tr -d ' ')

    if [ "$count" -gt 0 ]; then
        find "$BROADCASTS_DIR" -name "*.md" -mtime "+$days" -type f -delete 2>/dev/null
        echo "Cleaned up $count broadcasts older than $days days"
    else
        echo "No broadcasts older than $days days"
    fi
}

summary() {
    echo "=== Broadcast Summary ==="
    echo "Total broadcasts: $(find "$BROADCASTS_DIR" -name "*.md" -type f 2>/dev/null | wc -l | tr -d ' ')"
    echo "New since sync: $(count_new)"
    echo "Last sync: $(last_sync)"
    echo ""
    echo "Recent broadcasts:"
    list_all | head -5
}

case "${1:-help}" in
    send)
        send_broadcast "$2" "$3" "$4" "$5" "$6"
        ;;
    list)
        list_all
        ;;
    list-new)
        list_new
        ;;
    count-new)
        count_new
        ;;
    show)
        show_broadcast "$2"
        ;;
    mark-synced)
        mark_synced
        ;;
    last-sync)
        last_sync
        ;;
    cleanup)
        cleanup_old "$2"
        ;;
    summary)
        summary
        ;;
    help|*)
        cat << EOF
agent-broadcast.sh - Broadcast notifications between agents

Commands:
  send <type> <agent_id> <task_id> <title> <message>
                            - Send a broadcast notification
  list                      - List all broadcasts
  list-new                  - List broadcasts since last sync
  count-new                 - Count new broadcasts
  show <file>               - Show a broadcast's contents
  mark-synced               - Mark current time as synced
  last-sync                 - Show last sync time
  cleanup [days]            - Remove broadcasts older than N days (default: 7)
  summary                   - Show broadcast summary

Broadcast Types:
  task_completed  - A task was completed
  task_blocked    - A task hit a blocker
  task_unblocked  - A blocked task is now available
  agent_status    - Agent status update

Directory: $BROADCASTS_DIR
EOF
        ;;
esac
