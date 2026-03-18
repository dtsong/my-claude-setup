#!/usr/bin/env bash
set -euo pipefail

# skill-usage-report.sh — Analyze skill usage telemetry
# Usage: skill-usage-report.sh [--days N] [--project NAME]

TELEMETRY_FILE="${HOME}/.claude/telemetry/skill-usage.jsonl"
DAYS=30
PROJECT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --days) DAYS="$2"; shift 2 ;;
    --project) PROJECT="$2"; shift 2 ;;
    *) echo "Usage: skill-usage-report.sh [--days N] [--project NAME]"; exit 1 ;;
  esac
done

if [[ ! -f "$TELEMETRY_FILE" ]]; then
  echo "No telemetry data found at $TELEMETRY_FILE"
  echo "Enable telemetry by adding skill-telemetry.sh as a PreToolUse hook."
  exit 0
fi

if ! command -v jq &>/dev/null; then
  echo "ERROR: jq required for report generation"
  echo "Install: brew install jq"
  exit 1
fi

CUTOFF=$(date -u -v-${DAYS}d +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || date -u -d "${DAYS} days ago" +"%Y-%m-%dT%H:%M:%SZ")

echo "=== Skill Usage Report ==="
echo "Period: last $DAYS days (since $CUTOFF)"
echo ""

FILTER=".timestamp >= \"$CUTOFF\""
if [[ -n "$PROJECT" ]]; then
  FILTER="$FILTER and .project == \"$PROJECT\""
  echo "Project: $PROJECT"
  echo ""
fi

echo "--- Top Skills by Usage ---"
jq -r "select($FILTER) | .skill" "$TELEMETRY_FILE" 2>/dev/null | sort | uniq -c | sort -rn | head -20

echo ""
echo "--- Usage by Project ---"
jq -r "select($FILTER) | .project" "$TELEMETRY_FILE" 2>/dev/null | sort | uniq -c | sort -rn | head -10

echo ""
echo "--- Daily Activity ---"
jq -r "select($FILTER) | .timestamp[:10]" "$TELEMETRY_FILE" 2>/dev/null | sort | uniq -c | sort

TOTAL=$(jq -r "select($FILTER) | .skill" "$TELEMETRY_FILE" 2>/dev/null | wc -l | tr -d ' ')
echo ""
echo "Total invocations: $TOTAL"
