#!/bin/bash
# launch-agent.sh - Launch Claude agent(s) in a worktree
# Usage: launch-agent.sh "<task>" "<branch>" [num_agents] [--keep-open]
#
# Options:
#   --keep-open    Keep terminal window open after task completes (default: auto-close)

set -e

TASK="$1"
BRANCH="$2"
NUM_AGENTS="${3:-1}"
KEEP_OPEN=""

# Check for --keep-open flag
for arg in "$@"; do
    if [[ "$arg" == "--keep-open" ]]; then
        KEEP_OPEN="--keep-open"
        # If it was passed as $3, reset NUM_AGENTS to default
        if [[ "$3" == "--keep-open" ]]; then
            NUM_AGENTS=1
        fi
    fi
done

# Handle case where num_agents is the flag
if [[ "$NUM_AGENTS" == "--keep-open" ]]; then
    NUM_AGENTS=1
fi

# Validate inputs
if [ -z "$TASK" ] || [ -z "$BRANCH" ]; then
    echo "Usage: launch-agent.sh \"<task>\" \"<branch>\" [num_agents] [--keep-open]"
    exit 1
fi

# Get the repo root and name
REPO_ROOT=$(git rev-parse --show-toplevel 2>/dev/null)
if [ -z "$REPO_ROOT" ]; then
    echo "Error: Not in a git repository"
    exit 1
fi

REPO_NAME=$(basename "$REPO_ROOT")
WORKTREE_BASE="$HOME/.claude-worktrees/$REPO_NAME"
WORKTREE_PATH="$WORKTREE_BASE/${BRANCH//\//-}"

# Create worktree base directory
mkdir -p "$WORKTREE_BASE"

# Check if branch/worktree already exists
if [ -d "$WORKTREE_PATH" ]; then
    echo "Worktree already exists: $WORKTREE_PATH"
    echo "Resuming work on existing branch..."
else
    # Create the worktree with a new branch
    echo "Creating worktree: $WORKTREE_PATH"
    git worktree add -b "$BRANCH" "$WORKTREE_PATH" 2>/dev/null || \
    git worktree add "$WORKTREE_PATH" "$BRANCH" 2>/dev/null || \
    git worktree add -b "$BRANCH" "$WORKTREE_PATH"
fi

# Create agent prompt file for the task
PROMPT_FILE="$WORKTREE_PATH/.claude-task"
cat > "$PROMPT_FILE" << EOF
# Current Task

$TASK

## Instructions

1. Read CLAUDE.md for project context
2. Plan your approach using TodoWrite
3. Implement the solution
4. **REQUIRED: Run \`npm run build\` and fix ALL errors before completing**
5. Run \`npm run test:ci\` if tests exist
6. Commit your work with clear, descriptive commit messages
7. When done, make a final commit with message: "Task complete: <brief summary>"

## Quality Gates

- Build MUST pass before marking complete
- No TypeScript errors
- No unhandled console errors

## Branch

Working on: $BRANCH
EOF

# Function to launch a single agent
launch_agent() {
    local agent_num=$1
    local agent_suffix=""
    [ "$NUM_AGENTS" -gt 1 ] && agent_suffix=" (Agent $agent_num)"

    # Create the terminal title
    local title="Claude: ${BRANCH}${agent_suffix}"

    # Path to wrapper script
    local WRAPPER_SCRIPT="$HOME/.claude/scripts/run-agent.sh"

    # Launch in new terminal tab (macOS)
    if [ "$(uname)" = "Darwin" ]; then
        # Use run-agent.sh wrapper for lifecycle management (auto-close, notifications)
        osascript << APPLESCRIPT
tell application "Terminal"
    activate
    do script "'$WRAPPER_SCRIPT' '$WORKTREE_PATH' '$BRANCH' $KEEP_OPEN"
end tell
APPLESCRIPT
    else
        # Linux fallback - try common terminal emulators
        if command -v gnome-terminal &> /dev/null; then
            gnome-terminal --title="$title" -- bash -c "'$WRAPPER_SCRIPT' '$WORKTREE_PATH' '$BRANCH' $KEEP_OPEN"
        elif command -v xterm &> /dev/null; then
            xterm -title "$title" -e "'$WRAPPER_SCRIPT' '$WORKTREE_PATH' '$BRANCH' $KEEP_OPEN" &
        else
            echo "Could not find terminal emulator. Please manually run:"
            echo "  $WRAPPER_SCRIPT '$WORKTREE_PATH' '$BRANCH' $KEEP_OPEN"
        fi
    fi
}

# Launch agent(s)
echo ""
echo "Launching $NUM_AGENTS agent(s)..."
echo ""

for i in $(seq 1 $NUM_AGENTS); do
    launch_agent $i
    [ "$NUM_AGENTS" -gt 1 ] && sleep 1  # Stagger launches
done

echo "Branch: $BRANCH"
echo "Worktree: $WORKTREE_PATH"
echo "Task file: $PROMPT_FILE"
echo ""
echo "Agent(s) launched! Use:"
echo "  /status              - Check progress"
echo "  /merge $BRANCH   - Merge when complete"
