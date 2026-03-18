#!/usr/bin/env bash
set -euo pipefail

# Pin GitHub Action versions from tags to SHA hashes
# Usage: pin-action-versions.sh <workflow-file>
# Output: prints replacement suggestions (does not modify file)

WORKFLOW="${1:?.github/workflows/*.yml path required}"

if ! command -v gh &>/dev/null; then
  echo "ERROR: gh CLI not found"
  echo "Install: brew install gh"
  exit 1
fi

echo "Scanning $WORKFLOW for unpinned action references..."
echo ""

# Extract action references like actions/checkout@v4
grep -oP 'uses:\s*\K[^@]+@[^\s]+' "$WORKFLOW" 2>/dev/null | sort -u | while IFS='@' read -r action ref; do
  # Skip already-pinned (40-char hex)
  if [[ "$ref" =~ ^[0-9a-f]{40}$ ]]; then
    echo "PINNED: $action@$ref"
    continue
  fi

  # Resolve tag to SHA
  SHA=$(gh api "repos/$action/git/ref/tags/$ref" --jq '.object.sha' 2>/dev/null || echo "")
  if [[ -z "$SHA" ]]; then
    echo "WARN: Could not resolve $action@$ref — check if tag exists"
  else
    echo "PIN:  $action@$ref"
    echo "  ->  $action@$SHA  # $ref"
  fi
done

echo ""
echo "Done. Apply changes manually or use sed."
