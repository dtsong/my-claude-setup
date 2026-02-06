#!/bin/bash
# launch-workspace.sh - Launch multi-agent Claude Code workspace
# Usage: ./launch-workspace.sh [workspace_path] [--planner-only] [--feature-count N]

set -e

SHARED_DIR="$HOME/.claude/agent-context/shared"
BOARD_FILE="$SHARED_DIR/task-board.md"
CONTEXT_FILE="$SHARED_DIR/AGENT_CONTEXT.md"

# Default settings
WORKSPACE=""
PLANNER_ONLY=false
FEATURE_COUNT=3
PLANNER_TASK="plan-001"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1" >&2; }

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --planner-only)
            PLANNER_ONLY=true
            shift
            ;;
        --feature-count)
            FEATURE_COUNT="$2"
            shift 2
            ;;
        --planner-task)
            PLANNER_TASK="$2"
            shift 2
            ;;
        --help|-h)
            cat << EOF
launch-workspace.sh - Launch multi-agent Claude Code workspace

Usage: launch-workspace.sh [workspace_path] [options]

Options:
  --planner-only         Only launch the planner agent
  --feature-count N      Number of feature agents (default: 3)
  --planner-task ID      Task ID for planner to claim (default: plan-001)
  --help, -h             Show this help message

If workspace_path is not provided, extracts project_path from task-board.md
EOF
            exit 0
            ;;
        *)
            if [[ -z "$WORKSPACE" ]]; then
                WORKSPACE="$1"
            fi
            shift
            ;;
    esac
done

# Get workspace from task board if not provided
get_workspace_from_board() {
    if [[ -f "$BOARD_FILE" ]]; then
        grep "^project_path:" "$BOARD_FILE" | head -1 | sed 's/project_path: *"//' | sed 's/"$//'
    fi
}

# Get available tasks sorted by priority
get_available_tasks() {
    if [[ -f "$BOARD_FILE" ]]; then
        awk '
            /^  - id:/ {
                id = $0; gsub(/.*id: *"/, "", id); gsub(/".*/, "", id);
                current_id = id
            }
            /priority:/ {
                priority = $0; gsub(/.*priority: */, "", priority);
                current_priority = priority
            }
            /status: available/ {
                prio_num = (current_priority == "high" ? 1 : (current_priority == "medium" ? 2 : 3))
                print prio_num " " current_id
            }
        ' "$BOARD_FILE" | sort -n | cut -d' ' -f2
    fi
}

# Validate workspace
validate_workspace() {
    local ws="$1"
    if [[ ! -d "$ws" ]]; then
        log_error "Workspace does not exist: $ws"
        return 1
    fi
    return 0
}

# Generate AppleScript
generate_applescript() {
    local workspace="$1"
    shift
    local available_tasks=("$@")

    # Planner prompt (escaped for AppleScript)
    local planner_prompt="You are the PLANNER AGENT for this multi-agent workspace.

STARTUP SEQUENCE:
1. Read the shared context: cat ~/.claude/agent-context/shared/AGENT_CONTEXT.md
2. Read the project context: cat ${workspace}/CLAUDE.md
3. View task board: /task-board
4. Claim your task: /claim-task ${PLANNER_TASK}

YOUR ROLE: Macro planning, architecture decisions, break down features into subtasks for the feature agents. Add new tasks using: ~/.claude/scripts/task-board.sh add-task"

    # Start AppleScript
    cat << 'APPLESCRIPT_START'
tell application "Terminal"
    activate
    delay 0.5

APPLESCRIPT_START

    # Window 1: Planner
    cat << APPLESCRIPT_PLANNER
    -- Window 1: Planner Agent
    do script "cd '${workspace}' && claude"
    delay 3

    tell application "System Events"
        tell process "Terminal"
            keystroke "$(echo "$planner_prompt" | sed 's/"/\\"/g' | tr '\n' ' ')"
            delay 0.3
            keystroke return
        end tell
    end tell

APPLESCRIPT_PLANNER

    if [[ "$PLANNER_ONLY" == "true" ]]; then
        echo "end tell"
        return
    fi

    # Window 2: Feature Agents
    cat << 'APPLESCRIPT_FEATURE_START'
    delay 1

    -- Window 2: Feature Agents
    tell application "System Events"
        tell process "Terminal"
            keystroke "n" using command down
        end tell
    end tell
    delay 0.5

APPLESCRIPT_FEATURE_START

    # Feature agent tabs
    for i in $(seq 1 $FEATURE_COUNT); do
        local task_id="${available_tasks[$((i-1))]:-}"
        local claim_cmd=""
        if [[ -n "$task_id" ]]; then
            claim_cmd="/claim-task ${task_id}"
        else
            claim_cmd="/task-board  -- then claim an available task"
        fi

        local feature_prompt="You are FEATURE AGENT #${i} for this multi-agent workspace.

STARTUP SEQUENCE:
1. Read shared context: cat ~/.claude/agent-context/shared/AGENT_CONTEXT.md
2. View task board: /task-board
3. Claim task: ${claim_cmd}

YOUR ROLE: Implement your claimed task following existing patterns. Run /complete-task when done. Use /sync-agents to check on other agents."

        if [[ $i -eq 1 ]]; then
            cat << APPLESCRIPT_FEAT1
    -- Feature Agent 1
    do script "cd '${workspace}' && claude" in front window
    delay 3

    tell application "System Events"
        tell process "Terminal"
            keystroke "$(echo "$feature_prompt" | sed 's/"/\\"/g' | tr '\n' ' ')"
            delay 0.3
            keystroke return
        end tell
    end tell

APPLESCRIPT_FEAT1
        else
            cat << APPLESCRIPT_FEATN
    delay 1

    -- Feature Agent ${i}
    tell application "System Events"
        tell process "Terminal"
            keystroke "t" using command down
        end tell
    end tell
    delay 0.5

    do script "cd '${workspace}' && claude" in front window
    delay 3

    tell application "System Events"
        tell process "Terminal"
            keystroke "$(echo "$feature_prompt" | sed 's/"/\\"/g' | tr '\n' ' ')"
            delay 0.3
            keystroke return
        end tell
    end tell

APPLESCRIPT_FEATN
        fi
    done

    echo "end tell"
}

# Main
main() {
    log_info "Multi-Agent Workspace Launcher"
    echo ""

    # Check macOS
    if [[ "$(uname -s)" != "Darwin" ]]; then
        log_error "This script only works on macOS with Terminal.app"
        exit 1
    fi

    # Get workspace
    if [[ -z "$WORKSPACE" ]]; then
        WORKSPACE=$(get_workspace_from_board)
        if [[ -z "$WORKSPACE" ]]; then
            log_error "No workspace provided and couldn't extract from task board"
            log_error "Usage: launch-workspace.sh [workspace_path]"
            exit 1
        fi
        log_info "Using workspace from task board: $WORKSPACE"
    fi

    # Validate
    if ! validate_workspace "$WORKSPACE"; then
        exit 1
    fi

    # Get available tasks
    local available_tasks=()
    if [[ -f "$BOARD_FILE" ]]; then
        while IFS= read -r task; do
            [[ -n "$task" ]] && available_tasks+=("$task")
        done < <(get_available_tasks)
    fi

    # Show config
    echo ""
    log_info "Launch Configuration:"
    echo "  Workspace: $WORKSPACE"
    echo "  Planner Task: $PLANNER_TASK"
    if [[ "$PLANNER_ONLY" == "true" ]]; then
        echo "  Mode: Planner Only"
    else
        echo "  Feature Agents: $FEATURE_COUNT"
        echo "  Available Tasks: ${available_tasks[*]:-none}"
    fi
    echo ""

    # Generate and run AppleScript
    log_info "Launching agents..."
    local applescript
    applescript=$(generate_applescript "$WORKSPACE" "${available_tasks[@]}")

    echo "$applescript" | osascript

    echo ""
    log_info "Launch complete!"
    echo ""
    echo "Windows opened:"
    echo "  - Window 1: Planner Agent (claiming $PLANNER_TASK)"
    if [[ "$PLANNER_ONLY" != "true" ]]; then
        echo "  - Window 2: Feature Agents ($FEATURE_COUNT tabs)"
    fi
    echo ""
    echo "Give agents ~10 seconds to initialize, then they'll start working."
}

main
