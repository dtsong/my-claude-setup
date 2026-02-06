#!/bin/bash
# find-workspaces.sh - Discover running Claude instances and their workspaces
# Usage: ./find-workspaces.sh [--json] [--active-only]

set -e

CLAUDE_DIR="$HOME/.claude"
JSON_OUTPUT=false
ACTIVE_ONLY=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --json) JSON_OUTPUT=true; shift ;;
        --active-only) ACTIVE_ONLY=true; shift ;;
        *) shift ;;
    esac
done

# Get recent active session IDs from todo files
get_active_sessions() {
    ls -lt "$CLAUDE_DIR/todos/"*.json 2>/dev/null | head -30 | while read -r line; do
        file=$(echo "$line" | awk '{print $NF}')
        basename "$file" | sed 's/-agent.*//'
    done | sort -u
}

# Find session file and extract workspace info
get_session_info() {
    local session_id="$1"
    local session_file
    session_file=$(find "$CLAUDE_DIR/projects" -name "${session_id}.jsonl" 2>/dev/null | head -1)

    if [[ -n "$session_file" ]]; then
        local cwd branch slug
        cwd=$(grep -o '"cwd":"[^"]*"' "$session_file" 2>/dev/null | tail -1 | sed 's/"cwd":"//;s/"$//')
        branch=$(grep -o '"gitBranch":"[^"]*"' "$session_file" 2>/dev/null | tail -1 | sed 's/"gitBranch":"//;s/"$//')
        slug=$(grep -o '"slug":"[^"]*"' "$session_file" 2>/dev/null | tail -1 | sed 's/"slug":"//;s/"$//')
        local last_activity
        last_activity=$(stat -f "%Sm" -t "%Y-%m-%d %H:%M" "$session_file" 2>/dev/null || stat -c "%y" "$session_file" 2>/dev/null | cut -d. -f1)

        echo "${session_id}|${cwd}|${branch}|${last_activity}|${slug}|${session_file}"
    fi
}

# Get git status for a workspace
get_git_status() {
    local workspace="$1"
    if [[ -d "$workspace" ]] && git -C "$workspace" rev-parse --git-dir &>/dev/null; then
        local status current_branch ahead behind
        status=$(git -C "$workspace" status --porcelain 2>/dev/null | wc -l | tr -d ' ')
        current_branch=$(git -C "$workspace" branch --show-current 2>/dev/null)
        ahead=$(git -C "$workspace" rev-list --count @{u}..HEAD 2>/dev/null || echo "0")
        behind=$(git -C "$workspace" rev-list --count HEAD..@{u} 2>/dev/null || echo "0")
        echo "${current_branch}|${status}|${ahead}|${behind}"
    fi
}

# Check if session is active (modified recently)
is_session_active() {
    local session_id="$1"
    local todo_file="$CLAUDE_DIR/todos/${session_id}-agent-${session_id}.json"
    if [[ -f "$todo_file" ]]; then
        local mod_time now age
        mod_time=$(stat -f "%m" "$todo_file" 2>/dev/null || stat -c "%Y" "$todo_file" 2>/dev/null)
        now=$(date +%s)
        age=$((now - mod_time))
        [[ $age -lt 7200 ]] && return 0  # Active if modified in last 2 hours
    fi
    return 1
}

# Main
main() {
    if $JSON_OUTPUT; then
        echo '{"workspaces": ['
    else
        echo "=== Active Claude Workspaces ==="
        echo ""
    fi

    local first=true
    local sessions
    sessions=$(get_active_sessions)
    local count=0

    while IFS= read -r session_id; do
        [[ -z "$session_id" ]] && continue

        local info
        info=$(get_session_info "$session_id")
        [[ -z "$info" ]] && continue

        IFS='|' read -r sid cwd branch last_activity slug session_file <<< "$info"

        # Skip if no workspace or doesn't exist
        [[ -z "$cwd" || ! -d "$cwd" ]] && continue

        # Check if active
        local is_active=false
        is_session_active "$session_id" && is_active=true

        # Skip inactive if --active-only
        $ACTIVE_ONLY && ! $is_active && continue

        # Get git info from workspace
        local git_info display_branch changes ahead behind
        git_info=$(get_git_status "$cwd")
        if [[ -n "$git_info" ]]; then
            IFS='|' read -r display_branch changes ahead behind <<< "$git_info"
        else
            display_branch="$branch"
            changes="0"
            ahead="0"
            behind="0"
        fi

        count=$((count + 1))

        if $JSON_OUTPUT; then
            $first || echo ","
            first=false
            cat << EOF
    {
      "id": $count,
      "session_id": "$sid",
      "workspace": "$cwd",
      "branch": "$display_branch",
      "slug": "$slug",
      "last_activity": "$last_activity",
      "git_changes": $changes,
      "ahead": $ahead,
      "behind": $behind,
      "active": $is_active
    }
EOF
        else
            local active_marker=""
            $is_active && active_marker=" [ACTIVE]"

            echo "[$count] $slug$active_marker"
            echo "    Workspace: $cwd"
            echo "    Branch: $display_branch"
            echo "    Last: $last_activity"
            [[ "$changes" != "0" ]] && echo "    Changes: $changes uncommitted files"
            [[ "$ahead" != "0" ]] && echo "    Ahead: $ahead commits"
            echo ""
        fi
    done <<< "$sessions"

    if $JSON_OUTPUT; then
        echo ""
        echo "], \"total\": $count}"
    else
        echo "Found $count workspace(s)"
    fi
}

main
