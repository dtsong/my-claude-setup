---
name: "GitHub Tag"
description: "Create semantic version tags"
triggers:
  - "gh-tag"
  - "create tag"
  - "new tag"
  - "version tag"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-write operations — creates, lists, pushes, and deletes git tags.
- Does not create GitHub releases — use gh-release skill for that.
- Does not modify repository settings or branch protections.
- Tags are local until explicitly pushed to the remote.

## Input Sanitization

- Tag names: must match semver format (e.g., `v1.2.3`, `v1.0.0-beta.1`) with alphanumeric characters, dots, and hyphens only.
- Tag messages: reject null bytes.
- Commit references: must be valid hex SHA prefixes or HEAD.

# /gh-tag - Create Version Tags

Create semantic version tags for releases.

## Usage

```bash
/gh-tag                    # Interactive, suggest next version
/gh-tag v1.2.0             # Create specific tag
/gh-tag v1.2.0 --push      # Create and push immediately
/gh-tag --list             # List existing tags
/gh-tag --delete v1.2.0    # Delete a tag
```

## Workflow

### Step 1: Analyze Current State

```bash
# Get all tags sorted by version
git tag --sort=-v:refname | head -10

# Get latest tag
LATEST=$(git describe --tags --abbrev=0 2>/dev/null)
echo "Latest tag: $LATEST"

# Count commits since last tag
COMMITS=$(git rev-list $LATEST..HEAD --count 2>/dev/null || echo "0")
echo "Commits since: $COMMITS"
```

### Step 2: Suggest Next Version

Analyze commits since last tag:

```bash
# Check for conventional commit types
git log $LATEST..HEAD --format="%s" | while read msg; do
    case "$msg" in
        BREAKING*|*!:*)
            echo "MAJOR" ;;
        feat:*|feat\(*\):*)
            echo "MINOR" ;;
        fix:*|fix\(*\):*)
            echo "PATCH" ;;
    esac
done | sort | uniq -c
```

### Step 3: Create Tag

```bash
# Lightweight tag (just a pointer)
git tag v1.2.0

# Annotated tag (recommended - includes metadata)
git tag -a v1.2.0 -m "Version 1.2.0 - Feature description"

# Tag specific commit
git tag -a v1.2.0 abc1234 -m "Version 1.2.0"
```

### Step 4: Push Tag

```bash
# Push single tag
git push origin v1.2.0

# Push all tags
git push origin --tags
```

## Output Format

### Version Suggestion

```
Tag Creation

Current state:
  Latest tag: v1.1.0
  Commits since: 15
  Current branch: main

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Commit Analysis (since v1.1.0):

  feat: 3 commits (new features)
    - Add dark mode support
    - Add theme persistence
    - Add system theme detection

  fix: 5 commits (bug fixes)
    - Fix login validation
    - Fix memory leak
    - ...

  Other: 7 commits
    - docs, chore, refactor, etc.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Suggested versions:

  [1] v1.2.0 (Recommended)
      Minor bump - new features without breaking changes

  [2] v1.1.1
      Patch bump - if only counting bug fixes

  [3] v2.0.0
      Major bump - if there are breaking changes

  [4] Custom version

Select option:
```

### Tag Created

```
Created tag: v1.2.0

Details:
  Tag: v1.2.0
  Commit: abc1234 (HEAD of main)
  Message: Version 1.2.0 - Dark mode and performance improvements
  Type: Annotated

The tag is local only.

To push:
  git push origin v1.2.0

Or create a release (will push tag automatically):
  /gh-release v1.2.0
```

### Tag Pushed

```
Tag v1.2.0 pushed to origin.

The tag is now available on GitHub:
  https://github.com/owner/repo/releases/tag/v1.2.0

Next steps:
  /gh-release v1.2.0    # Create a release for this tag
```

### List Tags

```
Tags (showing last 10):

  v1.1.0    3 days ago     abc1234  Performance improvements
  v1.0.1    2 weeks ago    def5678  Bug fixes
  v1.0.0    1 month ago    ghi9012  Initial stable release
  v0.9.0    2 months ago   jkl3456  Beta release
  ...

Total: 15 tags

Commands:
  /gh-tag v1.2.0       # Create new tag
  /gh-release v1.1.0   # Create release for existing tag
  /gh-tag --delete v0.9.0  # Delete old tag
```

### Delete Tag

```
Delete tag v0.9.0?

This will delete:
  - Local tag: v0.9.0
  - Remote tag: origin/v0.9.0 (if --remote specified)

Note: If a release exists for this tag, it will become a "draft"
release without a tag.

Proceed? [y/n]

Deleted local tag: v0.9.0
Deleted remote tag: origin/v0.9.0
```

## Semantic Versioning

```
MAJOR.MINOR.PATCH
  │     │     │
  │     │     └── Bug fixes, patches
  │     └──────── New features, backwards compatible
  └────────────── Breaking changes

Examples:
  v1.0.0   - First stable release
  v1.1.0   - New feature added
  v1.1.1   - Bug fix
  v2.0.0   - Breaking API change

Pre-release:
  v1.0.0-alpha.1
  v1.0.0-beta.1
  v1.0.0-rc.1
```

## Best Practices

1. **Always use annotated tags** for releases (`-a` flag)
2. **Use consistent format**: `v1.2.3` or `1.2.3`
3. **Tag on main/release branch**: Not feature branches
4. **Include descriptive message**: What's in this version
5. **Don't delete published tags**: Can break others' references

## Conventional Commits → Version

| Commit Type | Version Impact |
|-------------|---------------|
| `feat:` | Minor version |
| `fix:` | Patch version |
| `BREAKING CHANGE:` | Major version |
| `docs:`, `chore:` | No version change |

## Integration

- Use `/gh-release` to create full release after tagging
- Use `/gh-changelog` to see what's included since last tag
- Tag after merging all PRs for a release
