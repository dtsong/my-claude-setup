#!/bin/bash
REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_DIR="$HOME/.claude"
mkdir -p "$CLAUDE_DIR"
ln -sf "$REPO_DIR/CLAUDE.md" "$CLAUDE_DIR/CLAUDE.md"
ln -sf "$REPO_DIR/settings.json" "$CLAUDE_DIR/settings.json"
ln -sf "$REPO_DIR/commands" "$CLAUDE_DIR/commands"
ln -sf "$REPO_DIR/skills" "$CLAUDE_DIR/skills"
echo "Symlinks created. Run 'claude' to verify."
