#!/usr/bin/env bash
set -euo pipefail

# Lint Dockerfile with hadolint
# Usage: dockerfile-lint.sh [Dockerfile path]

DOCKERFILE="${1:-Dockerfile}"

if [[ ! -f "$DOCKERFILE" ]]; then
  echo "ERROR: $DOCKERFILE not found"
  exit 1
fi

if ! command -v hadolint &>/dev/null; then
  echo "ERROR: hadolint not found"
  echo "Install: brew install hadolint (macOS) or docker run --rm -i hadolint/hadolint < $DOCKERFILE"
  exit 1
fi

echo "Linting: $DOCKERFILE"
if hadolint "$DOCKERFILE"; then
  echo "PASS: No issues found"
else
  echo ""
  echo "FAIL: Issues found (see above)"
  exit 1
fi
