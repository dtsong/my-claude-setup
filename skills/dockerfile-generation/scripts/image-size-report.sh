#!/usr/bin/env bash
set -euo pipefail

# Build Docker image and report size
# Usage: image-size-report.sh [Dockerfile path] [context dir]

DOCKERFILE="${1:-Dockerfile}"
CONTEXT="${2:-.}"
IMAGE_TAG="size-check-$(date +%s)"

if [[ ! -f "$DOCKERFILE" ]]; then
  echo "ERROR: $DOCKERFILE not found"
  exit 1
fi

if ! command -v docker &>/dev/null; then
  echo "ERROR: docker not found"
  exit 1
fi

echo "Building image from $DOCKERFILE..."
if ! docker build -t "$IMAGE_TAG" -f "$DOCKERFILE" "$CONTEXT" --quiet; then
  echo "FAIL: Build failed"
  exit 1
fi

echo ""
echo "=== Image Size Report ==="
docker images "$IMAGE_TAG" --format "table {{.Repository}}\t{{.Tag}}\t{{.Size}}"
echo ""

# Show layer breakdown
echo "=== Layer Breakdown ==="
docker history "$IMAGE_TAG" --format "table {{.CreatedBy}}\t{{.Size}}" --no-trunc | head -20

# Cleanup
docker rmi "$IMAGE_TAG" >/dev/null 2>&1 || true
echo ""
echo "Temporary image cleaned up."
