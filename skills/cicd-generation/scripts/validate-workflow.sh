#!/usr/bin/env bash
set -euo pipefail

# Validate GitHub Actions workflow files with actionlint
# Usage: validate-workflow.sh <workflow-file>

WORKFLOW="${1:?.github/workflows/*.yml path required}"

if ! command -v actionlint &>/dev/null; then
  echo "ERROR: actionlint not found"
  echo "Install: brew install actionlint (macOS) or go install github.com/rhysd/actionlint/cmd/actionlint@latest"
  exit 1
fi

echo "Validating: $WORKFLOW"
if actionlint "$WORKFLOW"; then
  echo "PASS: $WORKFLOW is valid"
else
  echo "FAIL: $WORKFLOW has errors (see above)"
  exit 1
fi
