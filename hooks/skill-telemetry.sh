#!/usr/bin/env bash
set -euo pipefail

# skill-telemetry.sh — PreToolUse hook for logging skill activations
# Logs to ~/.claude/telemetry/skill-usage.jsonl
#
# Environment variables (set by Claude Code hook system):
#   TOOL_NAME — the tool being invoked
#   TOOL_INPUT — JSON string of tool parameters

TELEMETRY_DIR="${HOME}/.claude/telemetry"
TELEMETRY_FILE="${TELEMETRY_DIR}/skill-usage.jsonl"

# Only track Skill tool invocations
TOOL_NAME="${TOOL_NAME:-}"
if [[ "$TOOL_NAME" != "Skill" ]]; then
  exit 0
fi

# Ensure telemetry directory exists
mkdir -p "$TELEMETRY_DIR"

# Extract skill name from tool input
TOOL_INPUT="${TOOL_INPUT:-}"
SKILL_NAME=""
if command -v jq &>/dev/null; then
  SKILL_NAME=$(echo "$TOOL_INPUT" | jq -r '.skill // empty' 2>/dev/null || echo "")
fi

if [[ -z "$SKILL_NAME" ]]; then
  # Fallback: grep for skill field
  SKILL_NAME=$(echo "$TOOL_INPUT" | grep -oP '"skill"\s*:\s*"\K[^"]+' 2>/dev/null || echo "unknown")
fi

# Log entry
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
WORKING_DIR=$(pwd)
PROJECT=$(basename "$WORKING_DIR")

echo "{\"timestamp\":\"$TIMESTAMP\",\"skill\":\"$SKILL_NAME\",\"project\":\"$PROJECT\",\"cwd\":\"$WORKING_DIR\"}" >> "$TELEMETRY_FILE"

# Silent — don't interfere with skill execution
exit 0
