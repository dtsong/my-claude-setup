#!/bin/bash
# Repository Health Check Script
# Generates a health report for the repository

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

# Check if authenticated
if ! gh auth status &>/dev/null; then
    echo -e "${RED}Not authenticated with GitHub CLI${NC}"
    echo "Run: gh auth login"
    exit 1
fi

echo "Repository Health Report"
echo "========================"
echo ""

# Get repo info
REPO=$(gh repo view --json nameWithOwner -q '.nameWithOwner')
echo -e "${BLUE}Repository:${NC} $REPO"
echo ""

# Issues stats
echo -e "${BLUE}Issues${NC}"
OPEN_ISSUES=$(gh issue list --state open --json number | jq length)
CLOSED_ISSUES=$(gh issue list --state closed --limit 100 --json number | jq length)
echo "  Open: $OPEN_ISSUES"
echo "  Recently closed: $CLOSED_ISSUES"

# Unlabeled issues
UNLABELED=$(gh issue list --state open --label "" --json number | jq length)
if [ "$UNLABELED" -gt 0 ]; then
    echo -e "  ${YELLOW}Unlabeled: $UNLABELED${NC}"
fi

echo ""

# PR stats
echo -e "${BLUE}Pull Requests${NC}"
OPEN_PRS=$(gh pr list --state open --json number | jq length)
MERGED_PRS=$(gh pr list --state merged --limit 100 --json number | jq length)
echo "  Open: $OPEN_PRS"
echo "  Recently merged: $MERGED_PRS"

# PRs needing attention
NEEDS_REVIEW=$(gh pr list --search "review:required" --json number 2>/dev/null | jq length || echo "0")
if [ "$NEEDS_REVIEW" -gt 0 ]; then
    echo -e "  ${YELLOW}Needs review: $NEEDS_REVIEW${NC}"
fi

echo ""

# Branch stats
echo -e "${BLUE}Branches${NC}"
LOCAL_BRANCHES=$(git branch | wc -l | tr -d ' ')
REMOTE_BRANCHES=$(git branch -r | wc -l | tr -d ' ')
echo "  Local: $LOCAL_BRANCHES"
echo "  Remote: $REMOTE_BRANCHES"

# Stale branches
STALE=$(git for-each-ref --sort=committerdate --format='%(refname:short) %(committerdate:relative)' refs/heads/ | head -5)
echo "  Oldest branches:"
echo "$STALE" | while read line; do
    echo "    $line"
done

echo ""

# Recent activity
echo -e "${BLUE}Recent Activity (7 days)${NC}"
WEEK_AGO=$(date -v-7d +%Y-%m-%d 2>/dev/null || date -d '7 days ago' +%Y-%m-%d)
COMMITS=$(git log --since="$WEEK_AGO" --oneline | wc -l | tr -d ' ')
echo "  Commits: $COMMITS"

# Contributors this week
echo "  Top contributors:"
git log --since="$WEEK_AGO" --format='%an' | sort | uniq -c | sort -rn | head -3 | while read line; do
    echo "    $line"
done

echo ""

# Health score calculation
SCORE=100

# Deduct for unlabeled issues
if [ "$UNLABELED" -gt 5 ]; then
    SCORE=$((SCORE - 10))
fi

# Deduct for many open issues
if [ "$OPEN_ISSUES" -gt 50 ]; then
    SCORE=$((SCORE - 10))
fi

# Deduct for stale PRs
if [ "$OPEN_PRS" -gt 10 ]; then
    SCORE=$((SCORE - 5))
fi

# Show score
echo -e "${BLUE}Health Score:${NC} $SCORE/100"

if [ "$SCORE" -ge 90 ]; then
    echo -e "${GREEN}Excellent! Repository is well maintained.${NC}"
elif [ "$SCORE" -ge 70 ]; then
    echo -e "${YELLOW}Good, but some items need attention.${NC}"
else
    echo -e "${RED}Needs attention. Consider triaging issues and PRs.${NC}"
fi
