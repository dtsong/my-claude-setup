#!/usr/bin/env bash
# Fail-soft dispatcher for session telemetry (issue #59, AC-001..AC-003).
# Contract: never exit 2 (a blocking code in the Claude Code hooks protocol,
# and on Stop it would prevent Claude from stopping). Missing DEFAULT hook =
# fresh clone without the private repo = fully silent exit 0. Anything the
# owner would want to know about (explicit env var mistyped, private repo
# present but hook gone, python3 missing, hook crashed) warns on stderr;
# real failures exit 1 (non-blocking, visible), never the child's raw code.
DEFAULT_HOOK="$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py"
HOOK_PATH="${CLAUDE_TELEMETRY_HOOK:-$DEFAULT_HOOK}"

if [ ! -r "$HOOK_PATH" ]; then
  if [ -n "${CLAUDE_TELEMETRY_HOOK:-}" ]; then
    echo "telemetry-dispatch: CLAUDE_TELEMETRY_HOOK is set but target is missing or unreadable: $HOOK_PATH" >&2
  elif [ -d "${DEFAULT_HOOK%/hooks/*}" ]; then
    echo "telemetry-dispatch: private repo present but hook missing: $HOOK_PATH" >&2
  fi
  exit 0
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "telemetry-dispatch: python3 not found on PATH; skipping session telemetry" >&2
  exit 1
fi

python3 "$HOOK_PATH" "$@"
status=$?
if [ "$status" -ne 0 ]; then
  echo "telemetry-dispatch: session_telemetry.py failed (exit $status, hook=$HOOK_PATH)" >&2
  exit 1
fi
exit 0
