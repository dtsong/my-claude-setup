#!/usr/bin/env bash
# package-skill.sh — Package a skill directory into a distributable tarball.
# Bash 3.2 compatible (no associative arrays, no mapfile).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

if [ $# -lt 1 ]; then
  echo "Usage: $0 <skill-directory>" >&2
  echo "  Example: $0 threat-model-skill/" >&2
  exit 1
fi

SKILL_INPUT="$1"

# Resolve skill directory path
if [ -d "$REPO_ROOT/$SKILL_INPUT" ]; then
  SKILL_DIR="$REPO_ROOT/$SKILL_INPUT"
elif [ -d "$SKILL_INPUT" ]; then
  SKILL_DIR="$(cd "$SKILL_INPUT" && pwd)"
else
  echo "FAIL: Skill directory not found: $SKILL_INPUT" >&2
  exit 1
fi

SKILL_NAME="$(basename "$SKILL_DIR")"

# Verify SKILL.md exists
if [ ! -f "$SKILL_DIR/SKILL.md" ]; then
  echo "FAIL: $SKILL_NAME/SKILL.md not found" >&2
  exit 1
fi

# Create dist directory
DIST_DIR="$REPO_ROOT/dist"
mkdir -p "$DIST_DIR"

echo "=== Packaging: $SKILL_NAME ==="

# Build file list for the tarball
INCLUDE_PATHS=""

# Always include SKILL.md
INCLUDE_PATHS="$SKILL_NAME/SKILL.md"

# Include references/ if exists
if [ -d "$SKILL_DIR/references" ]; then
  INCLUDE_PATHS="$INCLUDE_PATHS $SKILL_NAME/references"
fi

# Include scripts/ if exists
if [ -d "$SKILL_DIR/scripts" ]; then
  INCLUDE_PATHS="$INCLUDE_PATHS $SKILL_NAME/scripts"
fi

# Include skills/ if exists (for suites)
if [ -d "$SKILL_DIR/skills" ]; then
  INCLUDE_PATHS="$INCLUDE_PATHS $SKILL_NAME/skills"
fi

# Extract version from frontmatter if available
VERSION="0.0.0"
if grep -q '^version:' "$SKILL_DIR/SKILL.md" 2>/dev/null; then
  VERSION="$(grep '^version:' "$SKILL_DIR/SKILL.md" | head -1 | sed 's/^version:[[:space:]]*//' | sed 's/[[:space:]]*$//')"
fi

# Build file list for manifest
FILE_LIST="["
FIRST=true
for inc_path in $INCLUDE_PATHS; do
  full_path="$REPO_ROOT/$inc_path"
  if [ -f "$full_path" ]; then
    if [ "$FIRST" = true ]; then
      FILE_LIST="$FILE_LIST\"$inc_path\""
      FIRST=false
    else
      FILE_LIST="$FILE_LIST, \"$inc_path\""
    fi
  elif [ -d "$full_path" ]; then
    while IFS= read -r f; do
      [ -n "$f" ] || continue
      rel_f="${f#$REPO_ROOT/}"
      if [ "$FIRST" = true ]; then
        FILE_LIST="$FILE_LIST\"$rel_f\""
        FIRST=false
      else
        FILE_LIST="$FILE_LIST, \"$rel_f\""
      fi
    done <<EOF
$(find "$full_path" -type f -not -name '.DS_Store' -not -path '*/.git/*')
EOF
  fi
done
FILE_LIST="$FILE_LIST]"

# Write manifest
MANIFEST_PATH="$SKILL_DIR/manifest.json"
cat > "$MANIFEST_PATH" <<MANIFEST
{
  "name": "$SKILL_NAME",
  "version": "$VERSION",
  "files": $FILE_LIST
}
MANIFEST

echo "  Created manifest: $SKILL_NAME/manifest.json"

# Add manifest to include paths
INCLUDE_PATHS="$INCLUDE_PATHS $SKILL_NAME/manifest.json"

# Create tarball (exclude eval-cases, .git, node_modules)
TARBALL="$DIST_DIR/${SKILL_NAME}-${VERSION}.tar.gz"

# shellcheck disable=SC2086
tar -czf "$TARBALL" \
  -C "$REPO_ROOT" \
  --exclude='eval-cases' \
  --exclude='.git' \
  --exclude='node_modules' \
  --exclude='.DS_Store' \
  $INCLUDE_PATHS

# Clean up manifest from skill directory
rm -f "$MANIFEST_PATH"

echo "  Packaged: $TARBALL"

# Print tarball contents
echo "  Contents:"
tar -tzf "$TARBALL" | while IFS= read -r entry; do
  echo "    $entry"
done

echo ""
echo "=== Done ==="
