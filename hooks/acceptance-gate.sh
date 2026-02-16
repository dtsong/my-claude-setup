#!/usr/bin/env bash
# acceptance-gate.sh — PostToolUse enforcement hook
# Blocks task completion when acceptance criteria are unverified.
#
# Fires on: TaskUpdate (to completed)
# Reads: acceptance-contract.md from active session or .claude/prd/
# Exits: 0 = allow, non-zero = block

set -euo pipefail

# Parse hook input from stdin (JSON with tool_name, tool_input, etc.)
INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty')
TOOL_INPUT=$(echo "$INPUT" | jq -r '.tool_input // empty')

# Only gate on TaskUpdate → completed
if [[ "$TOOL_NAME" != "TaskUpdate" ]]; then
  exit 0
fi

STATUS=$(echo "$TOOL_INPUT" | jq -r '.status // empty')
if [[ "$STATUS" != "completed" ]]; then
  exit 0
fi

# Find the active acceptance contract
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
CONTRACT=""

# Check active council sessions
for dir in "$WORKSPACE"/.claude/council/sessions/*/; do
  if [[ -f "${dir}acceptance-contract.md" ]]; then
    # Check if session is active (most recent by modification time)
    CONTRACT="${dir}acceptance-contract.md"
  fi
done

# Check active academy sessions
if [[ -z "$CONTRACT" ]]; then
  for dir in "$WORKSPACE"/.claude/academy/sessions/*/; do
    if [[ -f "${dir}acceptance-contract.md" ]]; then
      CONTRACT="${dir}acceptance-contract.md"
    fi
  done
fi

# Check .claude/prd/ symlinks
if [[ -z "$CONTRACT" ]]; then
  for f in "$WORKSPACE"/.claude/prd/contract-*.md; do
    if [[ -f "$f" ]]; then
      CONTRACT="$f"
      break
    fi
  done
fi

# Check ralf's contract location
if [[ -z "$CONTRACT" && -f "$WORKSPACE/.claude/acceptance-contract.md" ]]; then
  CONTRACT="$WORKSPACE/.claude/acceptance-contract.md"
fi

# No contract found — nothing to enforce
if [[ -z "$CONTRACT" ]]; then
  exit 0
fi

# Parse contract for unverified criteria
PENDING=$(grep -c '| pending |' "$CONTRACT" 2>/dev/null || echo 0)
FAILED=$(grep -c '| failed |' "$CONTRACT" 2>/dev/null || echo 0)
PENDING_MANUAL=$(grep -c '| pending-manual |' "$CONTRACT" 2>/dev/null || echo 0)
VERIFIED=$(grep -c '| verified |' "$CONTRACT" 2>/dev/null || echo 0)

UNVERIFIED=$((PENDING + FAILED))

if [[ "$UNVERIFIED" -gt 0 ]]; then
  TOTAL=$((VERIFIED + PENDING + FAILED + PENDING_MANUAL))
  echo "BLOCKED: Acceptance contract has unverified criteria."
  echo ""
  echo "  Contract: $CONTRACT"
  echo "  Verified: $VERIFIED/$TOTAL"
  echo "  Pending:  $PENDING"
  echo "  Failed:   $FAILED"
  if [[ "$PENDING_MANUAL" -gt 0 ]]; then
    echo "  Manual:   $PENDING_MANUAL (allowed)"
  fi
  echo ""
  echo "Unverified criteria:"
  grep '| pending \|| failed |' "$CONTRACT" | while IFS='|' read -r _ id criterion method status _; do
    id=$(echo "$id" | xargs)
    criterion=$(echo "$criterion" | xargs)
    status=$(echo "$status" | xargs)
    echo "  - $id: $criterion [$status]"
  done
  echo ""
  echo "Resolve all criteria before marking work as complete."
  exit 1
fi

# All criteria verified (or pending-manual) — allow completion
exit 0
