#!/usr/bin/env bash
# check-portability.sh — Advisory scan for platform-specific content in SKILL.md files.
# Flags issues but does NOT fail (exit 0 always). Bash 3.2 compatible.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WARNINGS=0

warn() {
  echo "  WARN: $1" >&2
  WARNINGS=$((WARNINGS + 1))
}

echo "=== Portability Check (Advisory) ==="
echo ""

# Scan all SKILL.md files
while IFS= read -r skill_file; do
  [ -n "$skill_file" ] || continue
  rel_path="${skill_file#$REPO_ROOT/}"
  echo "Scanning $rel_path ..."

  line_num=0
  while IFS= read -r line; do
    line_num=$((line_num + 1))

    # Skip frontmatter delimiters and empty lines
    case "$line" in
      "---"|"") continue ;;
    esac

    # Check for absolute paths (starting with / but not in code fences or URLs)
    case "$line" in
      *"http://"*|*"https://"*|*'```'*) ;;
      *)
        # Match lines containing space-slash-word patterns typical of absolute paths
        if echo "$line" | grep -qE '(^|[[:space:]])/[a-zA-Z]'; then
          warn "$rel_path:$line_num: possible absolute path: $line"
        fi
        ;;
    esac

    # Check for OS-specific commands
    if echo "$line" | grep -qE '\b(xdg-open|pbcopy|pbpaste|wslpath|cmd\.exe|powershell)\b'; then
      warn "$rel_path:$line_num: OS-specific command: $line"
    fi

    # Check for macOS-specific 'open' command (but not in generic text)
    if echo "$line" | grep -qE '(^|[[:space:]])open[[:space:]]+(https?://|[./])'; then
      warn "$rel_path:$line_num: possible macOS 'open' command: $line"
    fi

    # Check for platform-specific references
    if echo "$line" | grep -qiE '\b(darwin|win32|windows-only|macos-only|linux-only)\b'; then
      warn "$rel_path:$line_num: platform-specific reference: $line"
    fi

  done < "$skill_file"

done <<EOF
$(find "$REPO_ROOT" -name 'SKILL.md' -not -path '*/node_modules/*' -not -path '*/.git/*' -not -path '*/pipeline/*')
EOF

echo ""
echo "=== Summary ==="

if [ "$WARNINGS" -gt 0 ]; then
  echo "Advisory: $WARNINGS portability warning(s) found"
else
  echo "Clean: No portability issues detected"
fi

# Always exit 0 — this is advisory only
exit 0
