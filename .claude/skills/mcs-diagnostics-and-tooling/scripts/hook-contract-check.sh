#!/usr/bin/env bash
# hook-contract-check.sh: probe a Claude Code hook script's actual blocking
# behavior instead of trusting its comments.
#
# Claude Code's hook contract (see hooks/acceptance-gate.sh header, this repo):
#   PreToolUse + exit 2 + reason on STDERR  = tool call is denied ("blocks").
#   Every other combination (exit 0, exit 1, PostToolUse, reason on STDOUT)
#   is non-blocking: the harness logs it and lets the tool call proceed.
# This is exactly the bug class behind incidents 4bb8bf2 and 605112d in this
# repo's history (see mcs-failure-archaeology): a hook that "looks like" it
# blocks (exit 1, or prints an error) but does not, because the harness only
# denies on PreToolUse + exit 2.
#
# Usage:
#   hook-contract-check.sh <hook-script> <event> <tool-name> <json-tool-input>
#
# Args:
#   hook-script      Path to the hook executable (bash or python3, must be
#                     runnable directly or via its shebang).
#   event             Hook event name to embed in the payload, e.g. PreToolUse,
#                     PostToolUse. Informational only for hooks that don't
#                     branch on it (this script derives the verdict from
#                     event + exit code, not from what the hook itself claims).
#   tool-name         Value for .tool_name in the payload, e.g. TaskUpdate.
#   json-tool-input   Raw JSON object (single shell arg, quote it) for
#                     .tool_input, e.g. '{"status":"completed"}'.
#
# Output: exit code, stdout byte count, stderr byte count, first stderr line,
# and a verdict line. Never writes outside stdout. Read-only: does not
# mutate the hook script, the repo, or any acceptance contract.
#
# Example:
#   ./hook-contract-check.sh ../../../hooks/acceptance-gate.sh PreToolUse \
#     TaskUpdate '{"status":"completed"}'

set -euo pipefail

if [ $# -ne 4 ]; then
  echo "Usage: $0 <hook-script> <event> <tool-name> <json-tool-input>" >&2
  echo "Example: $0 hooks/acceptance-gate.sh PreToolUse TaskUpdate '{\"status\":\"completed\"}'" >&2
  exit 1
fi

HOOK_SCRIPT="$1"
EVENT="$2"
TOOL_NAME="$3"
TOOL_INPUT_JSON="$4"

if [ ! -f "$HOOK_SCRIPT" ]; then
  echo "ERROR: hook script not found: $HOOK_SCRIPT" >&2
  exit 1
fi
if [ ! -x "$HOOK_SCRIPT" ]; then
  echo "ERROR: hook script not executable: $HOOK_SCRIPT (chmod +x it first)" >&2
  exit 1
fi

# Validate the tool-input JSON fragment early so a malformed payload fails
# fast with a clear message instead of a confusing hook-side jq error.
if ! echo "$TOOL_INPUT_JSON" | jq empty >/dev/null 2>&1; then
  echo "ERROR: <json-tool-input> is not valid JSON: $TOOL_INPUT_JSON" >&2
  exit 1
fi

PAYLOAD=$(jq -n \
  --arg event "$EVENT" \
  --arg tool "$TOOL_NAME" \
  --argjson input "$TOOL_INPUT_JSON" \
  '{hook_event_name: $event, tool_name: $tool, tool_input: $input}')

STDOUT_FILE=$(mktemp)
STDERR_FILE=$(mktemp)
trap 'rm -f "$STDOUT_FILE" "$STDERR_FILE"' EXIT

set +e
echo "$PAYLOAD" | "$HOOK_SCRIPT" >"$STDOUT_FILE" 2>"$STDERR_FILE"
EXIT_CODE=$?
set -e

STDOUT_BYTES=$(wc -c <"$STDOUT_FILE" | tr -d ' ')
STDERR_BYTES=$(wc -c <"$STDERR_FILE" | tr -d ' ')
FIRST_STDERR_LINE=$(head -1 "$STDERR_FILE" 2>/dev/null || true)

echo "=== hook-contract-check ==="
echo "Hook:        $HOOK_SCRIPT"
echo "Event:       $EVENT"
echo "Payload:     $PAYLOAD"
echo "Exit code:   $EXIT_CODE"
echo "Stdout:      ${STDOUT_BYTES} bytes"
echo "Stderr:      ${STDERR_BYTES} bytes"
if [ -n "$FIRST_STDERR_LINE" ]; then
  echo "Stderr[0]:   $FIRST_STDERR_LINE"
fi

if [ "$EVENT" = "PreToolUse" ] && [ "$EXIT_CODE" -eq 2 ] && [ "$STDERR_BYTES" -gt 0 ]; then
  echo "Verdict:     WOULD BLOCK (PreToolUse, exit 2, reason on stderr)"
else
  echo "Verdict:     would NOT block (harness only denies on PreToolUse + exit 2 + stderr)"
fi
