#!/bin/bash
# Safe Push Script
# Performs pre-push checks before pushing

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

FORCE_FLAG=""
SET_UPSTREAM=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -f|--force)
            FORCE_FLAG="--force-with-lease"
            shift
            ;;
        -u|--set-upstream)
            SET_UPSTREAM=true
            shift
            ;;
        *)
            shift
            ;;
    esac
done

# Check if we're in a git repo
if ! git rev-parse --is-inside-work-tree &>/dev/null; then
    echo -e "${RED}Not a git repository${NC}"
    exit 1
fi

BRANCH=$(git branch --show-current)

echo "Pre-push checks for $BRANCH"
echo "=========================="
echo ""

# Check 1: Protected branches
if [[ "$BRANCH" == "main" || "$BRANCH" == "master" ]]; then
    echo -e "${YELLOW}Warning: Pushing to protected branch '$BRANCH'${NC}"
    if [ -n "$FORCE_FLAG" ]; then
        echo -e "${RED}Force push to $BRANCH is not allowed${NC}"
        exit 1
    fi
fi

# Check 2: Uncommitted changes
if ! git diff --quiet || ! git diff --cached --quiet; then
    echo -e "${YELLOW}Warning: You have uncommitted changes${NC}"
    git status --short
    echo ""
fi

# Check 3: Check upstream
UPSTREAM=$(git rev-parse --abbrev-ref --symbolic-full-name @{u} 2>/dev/null || echo "")

if [ -z "$UPSTREAM" ]; then
    echo -e "${YELLOW}No upstream tracking branch${NC}"
    if [ "$SET_UPSTREAM" = true ]; then
        echo "Will set upstream to origin/$BRANCH"
        PUSH_CMD="git push -u origin $BRANCH"
    else
        echo "Use -u flag to set upstream, or run:"
        echo "  git push -u origin $BRANCH"
        exit 1
    fi
else
    echo -e "${GREEN}Tracking:${NC} $UPSTREAM"

    # Fetch to check for remote changes
    echo "Fetching remote..."
    git fetch --quiet

    # Check if we're behind
    BEHIND=$(git rev-list --count HEAD..@{u} 2>/dev/null || echo "0")
    if [ "$BEHIND" -gt 0 ]; then
        echo -e "${RED}Remote has $BEHIND commits not in local${NC}"
        if [ -z "$FORCE_FLAG" ]; then
            echo "Pull first or use --force flag"
            exit 1
        else
            echo -e "${YELLOW}Force push will overwrite these commits${NC}"
        fi
    fi

    PUSH_CMD="git push $FORCE_FLAG"
fi

# Check 4: Commits to push
AHEAD=$(git rev-list --count @{u}..HEAD 2>/dev/null || git rev-list --count HEAD 2>/dev/null || echo "0")
if [ "$AHEAD" -eq 0 ]; then
    echo -e "${GREEN}No commits to push${NC}"
    exit 0
fi

echo -e "${BLUE}Commits to push:${NC} $AHEAD"
git log --oneline @{u}..HEAD 2>/dev/null || git log --oneline -$AHEAD

echo ""
echo -e "${GREEN}All checks passed. Pushing...${NC}"
echo ""

# Execute push
if [ "$SET_UPSTREAM" = true ] && [ -z "$UPSTREAM" ]; then
    git push -u origin "$BRANCH"
else
    git push $FORCE_FLAG
fi

echo ""
echo -e "${GREEN}Push successful!${NC}"
