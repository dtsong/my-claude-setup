#!/bin/bash
# install.sh — Symlink this repo into ~/.claude/ so commands, agents, skills,
# hooks, and workspaces are available in every Claude Code session.
#
# Safe to re-run (idempotent). Uses `ln -sf` so existing symlinks are updated.
# Does NOT delete or overwrite regular files — only creates/updates symlinks.
set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_DIR="$HOME/.claude"

# ── Uninstall mode ───────────────────────────────────────────────────────────
if [[ "${1:-}" == "--uninstall" ]]; then
  echo "Removing symlinks from $CLAUDE_DIR..."
  removed=0
  for item in CLAUDE.md settings.json hooks.json commands skills agents scripts hooks workspaces; do
    target="$CLAUDE_DIR/$item"
    if [[ -L "$target" ]]; then
      rm "$target"
      echo "  removed $target"
      removed=$((removed + 1))
    fi
  done
  if [[ $removed -eq 0 ]]; then
    echo "  No symlinks found — nothing to remove."
  else
    echo "Done. Removed $removed symlink(s)."
  fi
  exit 0
fi

# ── Install mode ─────────────────────────────────────────────────────────────
mkdir -p "$CLAUDE_DIR"

# Warn if CLAUDE.md exists as a regular file (not a symlink)
if [[ -f "$CLAUDE_DIR/CLAUDE.md" && ! -L "$CLAUDE_DIR/CLAUDE.md" ]]; then
  echo "Warning: $CLAUDE_DIR/CLAUDE.md is a regular file (not a symlink)."
  echo "  It will be backed up to $CLAUDE_DIR/CLAUDE.md.bak before linking."
  cp "$CLAUDE_DIR/CLAUDE.md" "$CLAUDE_DIR/CLAUDE.md.bak"
fi

items=(
  "CLAUDE.md"
  "settings.json"
  "hooks.json"
  "commands"
  "skills"
  "agents"
  "scripts"
  "hooks"
  "workspaces"
)

echo "Linking $REPO_DIR → $CLAUDE_DIR"
for item in "${items[@]}"; do
  ln -sf "$REPO_DIR/$item" "$CLAUDE_DIR/$item"
  echo "  $CLAUDE_DIR/$item → $REPO_DIR/$item"
done

echo ""
echo "Done. $(echo "${items[@]}" | wc -w | tr -d ' ') symlinks created."
echo "Run 'claude' to verify."
