#!/bin/bash
# Release Notes Generator Script
# Generates changelog from merged PRs and commits

set -e

# Colors
BLUE='\033[0;34m'
NC='\033[0m'

# Get the range
SINCE_TAG="${1:-$(git describe --tags --abbrev=0 2>/dev/null || echo "")}"
UNTIL_TAG="${2:-HEAD}"

if [ -z "$SINCE_TAG" ]; then
    echo "No previous tag found. Generating notes for all commits."
    SINCE_TAG=$(git rev-list --max-parents=0 HEAD)
fi

echo "Release Notes"
echo "============="
echo "From: $SINCE_TAG"
echo "To: $UNTIL_TAG"
echo ""

# Count commits
COMMIT_COUNT=$(git rev-list --count "$SINCE_TAG..$UNTIL_TAG")
echo "Commits: $COMMIT_COUNT"
echo ""

# Categorize by conventional commit type
echo -e "${BLUE}## Features${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%s" | grep -E "^feat(\(.*\))?:" | sed 's/^feat\(.*\): /- /' || echo "None"
echo ""

echo -e "${BLUE}## Bug Fixes${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%s" | grep -E "^fix(\(.*\))?:" | sed 's/^fix\(.*\): /- /' || echo "None"
echo ""

echo -e "${BLUE}## Documentation${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%s" | grep -E "^docs(\(.*\))?:" | sed 's/^docs\(.*\): /- /' || echo "None"
echo ""

echo -e "${BLUE}## Performance${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%s" | grep -E "^perf(\(.*\))?:" | sed 's/^perf\(.*\): /- /' || echo "None"
echo ""

echo -e "${BLUE}## Other Changes${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%s" | grep -vE "^(feat|fix|docs|perf|refactor|test|chore)(\(.*\))?:" | sed 's/^/- /' | head -10 || echo "None"
echo ""

# Contributors
echo -e "${BLUE}## Contributors${NC}"
git log "$SINCE_TAG..$UNTIL_TAG" --format="%an" | sort | uniq | sed 's/^/- @/' | head -20
echo ""

echo "---"
echo "Full diff: $SINCE_TAG...$UNTIL_TAG"
