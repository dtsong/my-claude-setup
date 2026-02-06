---
name: "GitHub Changelog"
description: "Generate changelog from merged PRs and commits"
triggers:
  - "gh-changelog"
  - "changelog"
  - "release notes"
  - "what changed"
version: "1.0.0"
user_invocable: true
---

# /gh-changelog - Generate Changelog

Generate a changelog from merged PRs and commits since the last release.

## Usage

```bash
/gh-changelog                  # Changelog since last tag
/gh-changelog --since v1.0.0   # Since specific version
/gh-changelog --since v1.0.0 --until v1.1.0  # Between versions
/gh-changelog --format md      # Markdown output (default)
/gh-changelog --format json    # JSON output
/gh-changelog --pr-only        # Only include PR information
```

## Workflow

### Step 1: Determine Range

```bash
# Get latest tag
LATEST_TAG=$(git describe --tags --abbrev=0 2>/dev/null)

# Or use specified version
SINCE="${SINCE_TAG:-$LATEST_TAG}"
UNTIL="${UNTIL_TAG:-HEAD}"

echo "Generating changelog: $SINCE..$UNTIL"
```

### Step 2: Gather Merged PRs

```bash
# Get merged PRs since last tag
gh pr list --state merged --base main --json number,title,author,labels,mergedAt \
    --jq ".[] | select(.mergedAt > \"$SINCE_DATE\")"

# Or parse from git log
git log $SINCE..$UNTIL --merges --format="%s" | grep -oE '#[0-9]+'
```

### Step 3: Categorize Changes

Based on PR labels or conventional commits:

```
feat:     → Features
fix:      → Bug Fixes
docs:     → Documentation
perf:     → Performance
refactor: → Refactoring
test:     → Tests
chore:    → Maintenance
```

### Step 4: Generate Output

Format into structured changelog.

## Output Format

### Standard Changelog

```
Changelog: v1.1.0 → HEAD

Generated: 2025-01-25
Commits: 23
PRs merged: 8

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Features

- Add dark mode support (#123) - @user1
  Adds system theme detection and manual toggle

- Improve theme persistence (#124) - @user2
  Saves theme preference to localStorage

- Add keyboard shortcuts (#130) - @user3
  Adds Ctrl+K command palette

## Bug Fixes

- Fix login validation (#125) - @user4
  Properly validates email format

- Fix memory leak in theme hook (#127) - @user1
  Adds proper cleanup in useEffect

- Fix mobile responsive layout (#129) - @user5
  Fixes header overflow on small screens

## Performance

- Optimize bundle size (#126) - @user6
  Reduces initial load by 30%

## Documentation

- Update API documentation (#128) - @user7
  Adds examples for new endpoints

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Contributors

Thanks to all contributors for this release!

@user1, @user2, @user3, @user4, @user5, @user6, @user7

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Full diff: https://github.com/owner/repo/compare/v1.1.0...HEAD
```

### Markdown Output

```markdown
## Changelog

### Features
- Add dark mode support ([#123](https://github.com/owner/repo/pull/123)) - @user1
- Improve theme persistence ([#124](https://github.com/owner/repo/pull/124)) - @user2
- Add keyboard shortcuts ([#130](https://github.com/owner/repo/pull/130)) - @user3

### Bug Fixes
- Fix login validation ([#125](https://github.com/owner/repo/pull/125)) - @user4
- Fix memory leak in theme hook ([#127](https://github.com/owner/repo/pull/127)) - @user1
- Fix mobile responsive layout ([#129](https://github.com/owner/repo/pull/129)) - @user5

### Performance
- Optimize bundle size ([#126](https://github.com/owner/repo/pull/126)) - @user6

### Documentation
- Update API documentation ([#128](https://github.com/owner/repo/pull/128)) - @user7

### Contributors
@user1, @user2, @user3, @user4, @user5, @user6, @user7

**Full Changelog**: [v1.1.0...HEAD](https://github.com/owner/repo/compare/v1.1.0...HEAD)
```

### JSON Output

```json
{
  "from": "v1.1.0",
  "to": "HEAD",
  "generated": "2025-01-25T10:30:00Z",
  "categories": {
    "features": [
      {
        "pr": 123,
        "title": "Add dark mode support",
        "author": "user1",
        "labels": ["enhancement"]
      }
    ],
    "fixes": [...],
    "performance": [...],
    "documentation": [...]
  },
  "contributors": ["user1", "user2", ...],
  "stats": {
    "commits": 23,
    "prs": 8,
    "files_changed": 45
  }
}
```

### Breaking Changes Section

If breaking changes detected:

```
## ⚠️ Breaking Changes

- **API change**: `getTheme()` now returns Promise (#131)
  Migration: Change `const theme = getTheme()` to `const theme = await getTheme()`

- **Config format**: Theme config moved to separate file (#132)
  Migration: Move theme settings from `config.json` to `theme.config.json`
```

## Category Detection

### From PR Labels

| Label | Category |
|-------|----------|
| `enhancement`, `feature` | Features |
| `bug`, `fix` | Bug Fixes |
| `documentation` | Documentation |
| `performance` | Performance |
| `breaking-change` | Breaking Changes |

### From Conventional Commits

| Prefix | Category |
|--------|----------|
| `feat:` | Features |
| `fix:` | Bug Fixes |
| `docs:` | Documentation |
| `perf:` | Performance |
| `BREAKING CHANGE:` | Breaking Changes |

## Uncategorized Changes

For PRs/commits that don't match categories:

```
## Other Changes

- Update dependencies (#140) - @dependabot
- Refactor internal utilities (#141) - @user8
- Add more tests (#142) - @user9
```

## Script Location

The changelog generation script is at:
`~/.claude/skills/github-workflow/scripts/release-notes.sh`

## Integration

- Use before `/gh-release` to prepare release notes
- Use `/gh-tag` to tag the release
- Output can be copied directly into GitHub release
