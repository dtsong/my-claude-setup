#!/bin/bash
# Git Workflow Status Script
# Shows comprehensive status for git workflows

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Check if we're in a git repo
if ! git rev-parse --is-inside-work-tree &>/dev/null; then
    echo -e "${RED}Not a git repository${NC}"
    exit 1
fi

echo "Git Workflow Status"
echo "==================="
echo ""

# Current branch
CURRENT_BRANCH=$(git branch --show-current)
echo -e "${BLUE}Current branch:${NC} $CURRENT_BRANCH"

# Check for uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo -e "${YELLOW}Uncommitted changes:${NC}"
    git status --short
    echo ""
fi

# Check for untracked files
UNTRACKED=$(git ls-files --others --exclude-standard | wc -l | tr -d ' ')
if [ "$UNTRACKED" -gt 0 ]; then
    echo -e "${YELLOW}Untracked files:${NC} $UNTRACKED"
fi

# Check upstream status
UPSTREAM=$(git rev-parse --abbrev-ref --symbolic-full-name @{u} 2>/dev/null || echo "none")
if [ "$UPSTREAM" != "none" ]; then
    echo -e "${BLUE}Tracking:${NC} $UPSTREAM"

    # Fetch to get accurate counts
    git fetch --quiet 2>/dev/null || true

    AHEAD=$(git rev-list --count @{u}..HEAD 2>/dev/null || echo "0")
    BEHIND=$(git rev-list --count HEAD..@{u} 2>/dev/null || echo "0")

    if [ "$AHEAD" -gt 0 ]; then
        echo -e "${GREEN}Ahead:${NC} $AHEAD commits"
    fi
    if [ "$BEHIND" -gt 0 ]; then
        echo -e "${YELLOW}Behind:${NC} $BEHIND commits"
    fi
    if [ "$AHEAD" -eq 0 ] && [ "$BEHIND" -eq 0 ]; then
        echo -e "${GREEN}Up to date${NC}"
    fi
else
    echo -e "${YELLOW}No upstream tracking branch${NC}"
fi

echo ""

# Check for in-progress operations
if [ -d .git/rebase-merge ] || [ -d .git/rebase-apply ]; then
    echo -e "${RED}Rebase in progress${NC}"
    echo "  Run: git rebase --continue, --skip, or --abort"
fi

if [ -f .git/MERGE_HEAD ]; then
    echo -e "${RED}Merge in progress${NC}"
    echo "  Run: git merge --continue or --abort"
fi

if [ -f .git/CHERRY_PICK_HEAD ]; then
    echo -e "${RED}Cherry-pick in progress${NC}"
    echo "  Run: git cherry-pick --continue or --abort"
fi

# Check stash
STASH_COUNT=$(git stash list | wc -l | tr -d ' ')
if [ "$STASH_COUNT" -gt 0 ]; then
    echo -e "${BLUE}Stashes:${NC} $STASH_COUNT"
fi

echo ""

# Show recent commits
echo -e "${BLUE}Recent commits:${NC}"
git log --oneline -5

echo ""
echo "Quick actions:"
echo "  /git-sync    - Fetch remote changes"
echo "  /git-pull    - Pull changes"
echo "  /git-push    - Push commits"
echo "  /git-stash   - Manage stashes"
