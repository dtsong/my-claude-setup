#!/usr/bin/env bash
# acceptance-gate.sh — PreToolUse enforcement hook
# Blocks task completion when acceptance criteria are unverified.
#
# Fires on: PreToolUse / TaskUpdate (to completed)
# Reads: acceptance-contract.md from active session or .claude/prd/
# Exits: 0 = allow, 2 = block (deny the tool; stderr reason is fed to Claude).
#        PreToolUse + exit 2 prevents the TaskUpdate from running; any other
#        non-zero is a non-blocking error, so the block message MUST go to
#        stderr with exit 2 — never stdout with exit 1.

set -euo pipefail

# Parse hook input from stdin (JSON with tool_name, tool_input, etc.)
INPUT=$(cat)
TOOL_NAME=$(echo "$INPUT" | jq -r '.tool_name // empty' 2>/dev/null) || exit 0
TOOL_INPUT=$(echo "$INPUT" | jq -r '.tool_input // empty' 2>/dev/null) || exit 0

# Only gate on TaskUpdate → completed
if [[ "$TOOL_NAME" != "TaskUpdate" ]]; then
  exit 0
fi

STATUS=$(echo "$TOOL_INPUT" | jq -r '.status // empty' 2>/dev/null) || exit 0
if [[ "$STATUS" != "completed" ]]; then
  exit 0
fi

# Find the active acceptance contract
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

# Sessions older than this (no contract activity) are treated as abandoned and
# not enforced — a stale session must never block a newer one. Override via env.
STALE_HOURS="${ACCEPTANCE_GATE_STALE_HOURS:-72}"

# Portable mtime (epoch seconds): macOS `stat -f`, GNU `stat -c`, else 0.
mtime() { stat -f %m "$1" 2>/dev/null || stat -c %Y "$1" 2>/dev/null || echo 0; }

# Gather every candidate contract across known locations. nullglob so unmatched
# globs vanish; the bare ralf path is filtered by the -f test in the loop below.
shopt -s nullglob
CANDIDATES=(
  "$WORKSPACE"/.claude/council/sessions/*/acceptance-contract.md
  "$WORKSPACE"/.claude/academy/sessions/*/acceptance-contract.md
  "$WORKSPACE"/.claude/prd/contract-*.md
  "$WORKSPACE"/.claude/acceptance-contract.md
)
shopt -u nullglob

# Enforce the MOST RECENTLY MODIFIED contract (the active session). Selecting by
# mtime — not glob/alphabetical order — is what stops a dead session from
# blocking live work in the same repo.
CONTRACT=""
NEWEST=0
for f in "${CANDIDATES[@]}"; do
  [[ -f "$f" ]] || continue
  m=$(mtime "$f")
  if [[ "$m" -gt "$NEWEST" ]]; then
    NEWEST="$m"
    CONTRACT="$f"
  fi
done

# No contract found — nothing to enforce
if [[ -z "$CONTRACT" ]]; then
  exit 0
fi

# Staleness guard: an active contract not touched within STALE_HOURS is treated
# as an abandoned session and does not block.
AGE_HOURS=$(( ( $(date +%s) - NEWEST ) / 3600 ))
if [[ "$AGE_HOURS" -ge "$STALE_HOURS" ]]; then
  exit 0
fi

# Parse contract for unverified criteria
# Note: `grep -c` exits 1 on zero matches, so `|| echo 0` would append a
# second value. Assign a fallback via a separate `||` clause instead.
PENDING=$(grep -c '| pending |' "$CONTRACT" 2>/dev/null) || PENDING=0
FAILED=$(grep -c '| failed |' "$CONTRACT" 2>/dev/null) || FAILED=0
PENDING_MANUAL=$(grep -c '| pending-manual |' "$CONTRACT" 2>/dev/null) || PENDING_MANUAL=0
VERIFIED=$(grep -c '| verified |' "$CONTRACT" 2>/dev/null) || VERIFIED=0

UNVERIFIED=$((PENDING + FAILED))

if [[ "$UNVERIFIED" -gt 0 ]]; then
  TOTAL=$((VERIFIED + PENDING + FAILED + PENDING_MANUAL))
  # Block message goes to stderr: PreToolUse + exit 2 denies the tool and
  # surfaces stderr to Claude. stdout here would be ignored by the harness.
  exec 1>&2
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
  grep -E '\| (pending|failed) \|' "$CONTRACT" | while IFS='|' read -r _ id criterion method status _; do
    id=$(echo "$id" | xargs)
    criterion=$(echo "$criterion" | xargs)
    status=$(echo "$status" | xargs)
    echo "  - $id: $criterion [$status]"
  done
  echo ""
  echo "Resolve all criteria before marking work as complete."
  exit 2
fi

# All criteria verified (or pending-manual) — allow completion
exit 0
