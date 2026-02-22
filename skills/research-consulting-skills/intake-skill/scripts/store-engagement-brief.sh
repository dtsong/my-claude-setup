#!/usr/bin/env bash
# Store confirmed engagement brief in knowledge base
# Usage: store-engagement-brief.sh <engagement_id> <brief_path> <kb_root>
set -euo pipefail

ENGAGEMENT_ID="${1:?Usage: store-engagement-brief.sh <engagement_id> <brief_path> <kb_root>}"
BRIEF_PATH="${2:?Brief path required}"
KB_ROOT="${3:?Knowledge base root required}"

# Validate engagement_id format
if [[ ! "$ENGAGEMENT_ID" =~ ^[0-9]{4}-[0-9]{2}-[a-z0-9-]+-[a-z0-9-]+$ ]]; then
  echo "ERROR: engagement_id must match YYYY-MM-[a-z0-9-]+-[a-z0-9-]+" >&2
  exit 1
fi

# Validate brief path exists and is a regular file
if [[ ! -f "$BRIEF_PATH" ]]; then
  echo "ERROR: Brief file not found: $BRIEF_PATH" >&2
  exit 1
fi

# Validate paths don't contain traversal attempts
for path_var in "$BRIEF_PATH" "$KB_ROOT"; do
  if [[ "$path_var" == *".."* ]]; then
    echo "ERROR: Path traversal detected in: $path_var" >&2
    exit 1
  fi
done

# Validate KB_ROOT exists or can be created
if [[ -e "$KB_ROOT" ]] && [[ ! -d "$KB_ROOT" ]]; then
  echo "ERROR: KB_ROOT exists but is not a directory: $KB_ROOT" >&2
  exit 1
fi

TARGET_DIR="${KB_ROOT}/engagements/${ENGAGEMENT_ID}"
mkdir -p "${TARGET_DIR}/research-findings" "${TARGET_DIR}/assessment-result" "${TARGET_DIR}/deliverables"
cp "${BRIEF_PATH}" "${TARGET_DIR}/engagement-brief.md"
echo "Stored engagement brief at ${TARGET_DIR}/engagement-brief.md"
