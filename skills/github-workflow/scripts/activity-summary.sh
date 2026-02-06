#!/bin/bash
# Activity Summary Script
# Shows recent repository activity

set -e

# Colors
BLUE='\033[0;34m'
NC='\033[0m'

# Default to last 24 hours
SINCE="${1:-1 day ago}"

echo "Repository Activity"
echo "==================="
echo "Period: Since $SINCE"
echo ""

# Get date in ISO format
if [[ "$OSTYPE" == "darwin"* ]]; then
    SINCE_DATE=$(date -v-1d +%Y-%m-%dT%H:%M:%SZ)
else
    SINCE_DATE=$(date -d "$SINCE" +%Y-%m-%dT%H:%M:%SZ)
fi

# Recent commits
echo -e "${BLUE}Recent Commits${NC}"
COMMITS=$(git log --since="$SINCE" --oneline 2>/dev/null | wc -l | tr -d ' ')
echo "  Total: $COMMITS"
if [ "$COMMITS" -gt 0 ]; then
    echo "  Latest:"
    git log --since="$SINCE" --format="    %h %s (%an)" | head -5
fi
echo ""

# Check if gh is available
if command -v gh &>/dev/null && gh auth status &>/dev/null 2>&1; then
    # Merged PRs
    echo -e "${BLUE}Merged Pull Requests${NC}"
    MERGED=$(gh pr list --state merged --json number,title,mergedAt --jq "[.[] | select(.mergedAt > \"$SINCE_DATE\")] | length")
    echo "  Total: $MERGED"
    if [ "$MERGED" -gt 0 ]; then
        gh pr list --state merged --json number,title,author --jq ".[] | \"  #\\(.number) \\(.title) (@\\(.author.login))\"" | head -5
    fi
    echo ""

    # Opened issues
    echo -e "${BLUE}New Issues${NC}"
    NEW_ISSUES=$(gh issue list --state all --json number,createdAt --jq "[.[] | select(.createdAt > \"$SINCE_DATE\")] | length")
    echo "  Total: $NEW_ISSUES"
    if [ "$NEW_ISSUES" -gt 0 ]; then
        gh issue list --state all --json number,title,author --jq ".[] | \"  #\\(.number) \\(.title)\"" | head -5
    fi
    echo ""
else
    echo "(GitHub CLI not available - showing git data only)"
fi

# Contributors
echo -e "${BLUE}Active Contributors${NC}"
git log --since="$SINCE" --format='%an' 2>/dev/null | sort | uniq -c | sort -rn | head -5 | while read count name; do
    echo "  $name: $count commits"
done
