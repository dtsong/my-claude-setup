#!/usr/bin/env bash
# check-token-budgets.sh — CI safety net: run token budget checks on ALL files.
# Bash 3.2 compatible (no associative arrays, no mapfile).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BUDGET_SCRIPT="$REPO_ROOT/pipeline/hooks/check_token_budget.py"

if [ ! -f "$BUDGET_SCRIPT" ]; then
  echo "FAIL: Budget check script not found at $BUDGET_SCRIPT" >&2
  exit 1
fi

echo "=== Token Budget Check (CI Safety Net) ==="
echo ""

# Collect all SKILL.md files
FILES=""
while IFS= read -r f; do
  FILES="$FILES $f"
done <<EOF
$(find "$REPO_ROOT" -name 'SKILL.md' -not -path '*/node_modules/*' -not -path '*/.git/*')
EOF

# Collect all references/*.md files
while IFS= read -r f; do
  [ -n "$f" ] || continue
  FILES="$FILES $f"
done <<EOF
$(find "$REPO_ROOT" -path '*/references/*.md' -not -path '*/node_modules/*' -not -path '*/.git/*')
EOF

# Collect all shared-references/**/*.md files
while IFS= read -r f; do
  [ -n "$f" ] || continue
  FILES="$FILES $f"
done <<EOF
$(find "$REPO_ROOT/shared-references" -name '*.md' -not -path '*/node_modules/*' -not -path '*/.git/*' 2>/dev/null || true)
EOF

FILE_COUNT=0
for f in $FILES; do
  FILE_COUNT=$((FILE_COUNT + 1))
done

echo "Checking $FILE_COUNT files..."
echo ""

# shellcheck disable=SC2086
if python3 "$BUDGET_SCRIPT" $FILES; then
  echo ""
  echo "PASSED: All files within token budgets"
  exit 0
else
  echo ""
  echo "FAILED: Some files exceed token budgets"
  exit 1
fi
