#!/usr/bin/env bash
set -euo pipefail

# Run SQLFluff linting and dbt compile check
# Usage: dbt-lint-check.sh [model-path]

MODEL_PATH="${1:-models/}"

echo "=== dbt Compile Check ==="
if command -v dbt &>/dev/null; then
  if dbt compile --select "$MODEL_PATH" 2>&1; then
    echo "PASS: dbt compile succeeded"
  else
    echo "FAIL: dbt compile failed"
    exit 1
  fi
else
  echo "SKIP: dbt not found (install with pip install dbt-core)"
fi

echo ""
echo "=== SQLFluff Lint ==="
if command -v sqlfluff &>/dev/null; then
  if sqlfluff lint "$MODEL_PATH" --dialect snowflake 2>&1; then
    echo "PASS: No SQLFluff issues"
  else
    echo "WARN: SQLFluff issues found (see above)"
  fi
else
  echo "SKIP: sqlfluff not found (install with pip install sqlfluff)"
fi
