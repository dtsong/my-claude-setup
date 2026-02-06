#!/bin/bash
# My Items Script
# Shows GitHub items assigned to or involving the current user

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Check if gh is available
if ! command -v gh &>/dev/null; then
    echo -e "${RED}GitHub CLI (gh) is required${NC}"
    exit 1
fi

# Get current user
USER=$(gh api user --jq '.login')
echo "My GitHub Items (@$USER)"
echo "========================="
echo ""

# Assigned issues
echo -e "${BLUE}Assigned Issues${NC}"
ISSUES=$(gh issue list --assignee @me --state open --json number,title,labels,createdAt)
ISSUE_COUNT=$(echo "$ISSUES" | jq length)

if [ "$ISSUE_COUNT" -eq 0 ]; then
    echo "  No issues assigned"
else
    echo "$ISSUES" | jq -r '.[] | "  #\(.number) \(.title)"' | head -10
    if [ "$ISSUE_COUNT" -gt 10 ]; then
        echo "  ... and $((ISSUE_COUNT - 10)) more"
    fi
fi
echo ""

# My PRs
echo -e "${BLUE}My Pull Requests${NC}"
PRS=$(gh pr list --author @me --state open --json number,title,reviewDecision,statusCheckRollup)
PR_COUNT=$(echo "$PRS" | jq length)

if [ "$PR_COUNT" -eq 0 ]; then
    echo "  No open PRs"
else
    echo "$PRS" | jq -r '.[] | "  #\(.number) \(.title) [\(.reviewDecision // "pending")]"' | head -10
fi
echo ""

# Reviews requested
echo -e "${BLUE}Reviews Requested${NC}"
REVIEWS=$(gh pr list --search "review-requested:@me" --json number,title,author 2>/dev/null || echo "[]")
REVIEW_COUNT=$(echo "$REVIEWS" | jq length)

if [ "$REVIEW_COUNT" -eq 0 ]; then
    echo "  No reviews requested"
else
    echo "$REVIEWS" | jq -r '.[] | "  #\(.number) \(.title) by @\(.author.login)"' | head -10
fi
echo ""

# Summary
echo -e "${BLUE}Summary${NC}"
echo "  Issues assigned: $ISSUE_COUNT"
echo "  PRs authored: $PR_COUNT"
echo "  Reviews pending: $REVIEW_COUNT"
