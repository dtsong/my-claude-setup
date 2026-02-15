---
name: "GitHub Release"
description: "Create a GitHub release with changelog"
triggers:
  - "gh-release"
  - "new release"
  - "create release"
  - "publish release"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Read-write operations — creates GitHub releases, generates release notes, and uploads assets.
- Creates tags if they do not already exist.
- Does not modify repository settings, branch protections, or code.
- Does not generate standalone changelogs — use gh-changelog skill for that.

## Input Sanitization

- Version/tag identifiers: must match semver format (e.g., `v1.2.3`, `v1.0.0-rc.1`) with alphanumeric characters, dots, and hyphens only.
- Release title and notes: reject null bytes.
- Asset file paths: reject shell metacharacters and path traversal sequences (`../`).

# /gh-release - Create GitHub Release

Create a GitHub release with auto-generated or custom release notes.

## Usage

```bash
/gh-release                      # Interactive release creation
/gh-release v1.2.0               # Create release for existing tag
/gh-release v1.2.0 --draft       # Create as draft
/gh-release v1.2.0 --prerelease  # Mark as pre-release
/gh-release --latest             # Mark as latest release
/gh-release --generate-notes     # Auto-generate from PRs
```

## Workflow

### Step 1: Determine Version

```bash
# Get latest tag
LATEST_TAG=$(git describe --tags --abbrev=0 2>/dev/null || echo "v0.0.0")
echo "Latest release: $LATEST_TAG"

# Suggest next version based on changes
# Analyze commits since last tag for conventional commit types
COMMITS=$(git log $LATEST_TAG..HEAD --format="%s")

# Suggest version bump
# feat: -> minor, fix: -> patch, BREAKING: -> major
```

### Step 2: Generate Release Notes

Option A: Auto-generate from PRs

```bash
gh release create $VERSION --generate-notes
```

Option B: Use /gh-changelog output

```bash
/gh-changelog --since $LATEST_TAG
# Use output as release notes
```

Option C: Custom release notes

Use template and fill in details.

### Step 3: Create Release

```bash
# Create release with notes
gh release create v1.2.0 \
    --title "v1.2.0 - Feature Name" \
    --notes-file release-notes.md

# As draft (for review first)
gh release create v1.2.0 --draft

# As pre-release (alpha/beta/rc)
gh release create v1.2.0-beta.1 --prerelease
```

### Step 4: Attach Assets (Optional)

```bash
# Upload build artifacts
gh release upload v1.2.0 dist/app.zip dist/app.tar.gz
```

## Output Format

### Interactive Creation

```
Create New Release

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Version Selection:

  Current latest: v1.1.0
  Commits since: 23

  Suggested versions:
    [1] v1.2.0 (minor) - New features added
    [2] v1.1.1 (patch) - Bug fixes only
    [3] v2.0.0 (major) - Breaking changes

  Select version or enter custom:

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Release Title:
  Default: v1.2.0
  Custom: v1.2.0 - Dark Mode & Performance

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Release Notes:

  [1] Auto-generate from merged PRs (Recommended)
  [2] Use /gh-changelog output
  [3] Write custom notes
  [4] Use template

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Release Type:
  [x] Latest release
  [ ] Pre-release
  [ ] Draft (review before publishing)
```

### Successful Release

```
Created release v1.2.0!

URL: https://github.com/owner/repo/releases/tag/v1.2.0

Details:
  Tag: v1.2.0
  Title: v1.2.0 - Dark Mode & Performance
  Type: Latest release
  Created: Just now

Release Notes:
  ## What's Changed

  ### New Features
  * Add dark mode support by @user1 in #123
  * Improve theme system by @user2 in #124

  ### Bug Fixes
  * Fix login validation by @user3 in #125

  ### Performance
  * Optimize bundle size by @user4 in #126

  **Full Changelog**: v1.1.0...v1.2.0

Assets: None attached

Post-release:
  - Announce in #releases channel
  - Update documentation
  - Monitor for issues
```

### Draft Release

```
Created draft release v1.2.0

URL: https://github.com/owner/repo/releases/tag/v1.2.0

Status: DRAFT (not published)

The release is saved but not visible to users.

To publish:
  gh release edit v1.2.0 --draft=false

Or edit on GitHub:
  https://github.com/owner/repo/releases/edit/v1.2.0
```

## Release Notes Template

`~/.claude/skills/github-workflow/templates/release-notes.md`:

```markdown
## What's New in v{{version}}

### Highlights
- [Major feature or change]

### New Features
{{#each features}}
- {{this.title}} (#{{this.pr}})
{{/each}}

### Bug Fixes
{{#each fixes}}
- {{this.title}} (#{{this.pr}})
{{/each}}

### Breaking Changes
{{#if breaking}}
{{#each breaking}}
- {{this.description}}
{{/each}}
{{else}}
None
{{/if}}

### Contributors
{{#each contributors}}
- @{{this}}
{{/each}}

**Full Changelog**: {{previous_tag}}...{{version}}
```

## Semantic Versioning Guide

| Change Type | Version Bump | Example |
|-------------|--------------|---------|
| Breaking changes | Major | v1.0.0 → v2.0.0 |
| New features | Minor | v1.0.0 → v1.1.0 |
| Bug fixes | Patch | v1.0.0 → v1.0.1 |
| Pre-release | Suffix | v1.0.0-beta.1 |

## Pre-release Workflow

```bash
# Alpha releases (early testing)
/gh-release v1.2.0-alpha.1 --prerelease

# Beta releases (feature complete)
/gh-release v1.2.0-beta.1 --prerelease

# Release candidates (final testing)
/gh-release v1.2.0-rc.1 --prerelease

# Final release
/gh-release v1.2.0
```

## Integration

- Use `/gh-tag` to create tag first (if not using release to create)
- Use `/gh-changelog` to generate release notes
- Use after `/gh-pr-merge` to release merged changes
