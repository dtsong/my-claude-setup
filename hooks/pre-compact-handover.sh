#!/bin/bash
# pre-compact-handover.sh — Auto-save session context before compaction
# Fires on PreCompact hook to preserve decisions and context
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Read JSON from stdin
INPUT="$(cat)"

# ── Parse fields from JSON without jq ────────────────────────────────────────
get_json_string() {
  echo "$INPUT" | grep -o "\"$1\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" | head -1 | sed 's/.*:[[:space:]]*"\([^"]*\)"/\1/' || true
}

TRANSCRIPT_PATH="$(get_json_string transcript_path)"
CWD="$(get_json_string cwd)"
TRIGGER="$(get_json_string trigger)"

# Only fire on auto-compaction, not manual /compact
if [[ "$TRIGGER" != "auto" ]]; then
  exit 0
fi

# Validate transcript exists
if [[ -z "$TRANSCRIPT_PATH" || ! -f "$TRANSCRIPT_PATH" ]]; then
  exit 0
fi

# Determine workspace root
WORKSPACE="$(git -C "$CWD" rev-parse --show-toplevel 2>/dev/null || echo "$CWD")"

# Build output path
TIMESTAMP="$(date +%Y-%m-%d-%H%M)"
OUTDIR="$WORKSPACE/memory"
OUTFILE="$OUTDIR/HANDOVER-${TIMESTAMP}-auto.md"

# Debounce: skip if file already exists for this minute
if [[ -f "$OUTFILE" ]]; then
  exit 0
fi

mkdir -p "$OUTDIR"

# Gather session context
BRANCH="$(git -C "$WORKSPACE" branch --show-current 2>/dev/null || echo 'unknown')"
RECENT_COMMITS="$(git -C "$WORKSPACE" log --oneline -5 2>/dev/null || echo 'none')"

# Extract last 500 lines of transcript (most recent context)
TRANSCRIPT_TAIL="$(tail -500 "$TRANSCRIPT_PATH")"

# Build the summarization prompt
PROMPT="You are summarizing a Claude Code session transcript for handover to a future session. The transcript is JSONL format piped via stdin.

Write a concise handover document in markdown. Include these sections:

# Auto-Handover — $(date +%Y-%m-%d)
## Session Summary (2-3 sentences)
## What Was Done (bulleted changes)
## Key Decisions Made (with rationale — most important section)
## Pitfalls & Gotchas (errors, dead ends)
## Open Questions (unresolved items)
## Next Steps (ordered priority)

Context:
- Branch: $BRANCH
- Recent commits: $RECENT_COMMITS

Rules:
- Target 40-80 lines
- Focus on DECISIONS and RATIONALE, not just actions
- If the session was trivial, say so briefly
- Do NOT include the raw transcript — only your synthesis"

# Use claude -p with sonnet to summarize the session
SUMMARY="$(echo "$TRANSCRIPT_TAIL" | claude -p --model sonnet "$PROMPT" 2>/dev/null)" || true

# If claude -p failed or returned empty, create a minimal fallback
if [[ -z "$SUMMARY" ]]; then
  SUMMARY="# Auto-Handover — $TIMESTAMP

## Session Summary
Auto-compaction triggered but summary generation failed. Check transcript for details.

## Session Context
- **Branch**: $BRANCH
- **Transcript**: $TRANSCRIPT_PATH
- **Recent commits**:
$RECENT_COMMITS"
fi

# Write the handover file
echo "$SUMMARY" > "$OUTFILE"

# Report to user via stderr
echo "Auto-handover saved: memory/HANDOVER-${TIMESTAMP}-auto.md" >&2

exit 0
