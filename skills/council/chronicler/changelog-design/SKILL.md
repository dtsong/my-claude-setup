---
name: "Changelog Design"
department: "chronicler"
description: "Changelog entries and migration guides for breaking changes with version strategy"
version: 1
triggers:
  - "changelog"
  - "migration guide"
  - "upgrade"
  - "breaking change"
  - "release notes"
  - "deprecation"
  - "semver"
---

# Changelog Design

## Purpose

Create structured changelog entries and migration guides that enable consumers to understand changes, assess impact, and upgrade safely. Produces versioned changelogs following Keep a Changelog format with step-by-step migration instructions for breaking changes.

## Inputs

- List of changes (commits, PRs, or feature descriptions)
- Current version number
- Consumer types (library users, API consumers, internal teams)
- Previous changelog entries (for format consistency)

## Process

### Step 1: Categorize All Changes

Classify each change by impact:
- **Breaking**: Requires consumer action to upgrade — API changes, removed features, changed behavior
- **Feature**: New capability with no impact on existing behavior — additive APIs, new options
- **Fix**: Bug resolution — corrected behavior, error handling improvements
- **Deprecation**: Future removal warning — still works but will be removed in a future version
- **Internal**: No consumer impact — refactoring, dependency updates, test improvements
- Flag any change where the category is ambiguous and err toward higher impact classification

### Step 2: Describe Each Change with Full Context

Write each changelog entry with:
- **What changed**: Precise description of the change (not the PR title — the user-facing impact)
- **Why**: Motivation for the change — what problem it solves or what improvement it brings
- **Who is affected**: Which consumers or use cases are impacted
- **Before/After**: For behavior changes, show what the old behavior was and what the new behavior is
- Link to relevant PR, issue, or discussion for additional context

### Step 3: Write Migration Steps for Breaking Changes

For each breaking change, provide a complete migration guide:
- **Step-by-step instructions**: Numbered steps from old code to new code
- **Before/after code examples**: Show the exact code change needed (not just description)
- **Automated migration**: Codemod or find-and-replace pattern if applicable
- **Partial migration support**: Can consumers upgrade incrementally, or is it all-or-nothing?
- **Testing the migration**: How to verify the upgrade was successful
- **Estimated effort**: Time estimate for migrating (minutes, hours, or days)

### Step 4: Define Version Strategy

Determine version bump based on changes:
- **Major (X.0.0)**: Breaking changes present — any consumer code may need modification
- **Minor (0.X.0)**: New features, no breaking changes — upgrade is safe, new capabilities available
- **Patch (0.0.X)**: Bug fixes only — upgrade is safe, existing behavior corrected
- If multiple change categories exist, the highest impact category determines the version bump
- Consider pre-release versions (alpha, beta, rc) for high-risk changes needing early feedback

### Step 5: Plan Communication

Design the release communication:
- **Changelog entry**: Formatted entry for CHANGELOG.md (Keep a Changelog format)
- **Migration guide**: Standalone document for breaking changes (linked from changelog)
- **Upgrade notification**: How consumers are informed — release notes, email, in-app notification
- **Deprecation timeline**: For deprecated features, when will they be removed? (Minimum 1 major version)
- **Support period**: How long will the previous version receive bug fixes?

### Step 6: Validate Migration Path

Verify the upgrade experience:
- **Incremental upgrade**: Can consumers upgrade from any previous version, or only from N-1?
- **Breaking change clusters**: Are multiple breaking changes better released together or separately?
- **Dependency conflicts**: Does this upgrade force consumers to update other dependencies?
- **Rollback safety**: Can consumers downgrade if the upgrade causes issues?
- **CI verification**: Run consumer-perspective tests against the new version to catch missed breaking changes

## Output Format

```markdown
# Changelog: v[X.Y.Z]

**Release date**: [YYYY-MM-DD]
**Version bump**: [Major | Minor | Patch] — [one-line reason]

## Breaking Changes

### [Change title]

[Description of what changed and why]

**Who is affected**: [which consumers/use cases]

**Before**:
```[language]
// old code
```

**After**:
```[language]
// new code
```

**Migration steps**:
1. [Step 1]
2. [Step 2]
3. [Verify by running ...]

---

## Features

- **[Feature name]**: [Description] ([#PR](link))

## Fixes

- **[Fix description]**: [What was wrong, what's corrected] ([#PR](link))

## Deprecations

- **[Deprecated item]**: Use [replacement] instead. Will be removed in v[X+1].0.0. ([#PR](link))

---

## Migration Guide

### Prerequisites
- [Required version of dependencies]
- [Backup/snapshot recommendation]

### Step-by-Step Upgrade

1. Update dependency: `[package manager command]`
2. [Breaking change 1 migration steps with code]
3. [Breaking change 2 migration steps with code]
4. Run tests: `[test command]`
5. Verify: [smoke test or manual check]

### Estimated Migration Effort
- **Small projects**: [time estimate]
- **Large projects**: [time estimate]

## Communication Plan

| Channel | Content | Timing |
|---------|---------|--------|
| CHANGELOG.md | Full changelog | On release |
| GitHub Release | Highlights + migration link | On release |
| [notification channel] | Breaking change summary | 1 week before release |
```

## Quality Checks

- [ ] Every change is categorized (breaking, feature, fix, deprecation, internal)
- [ ] Breaking changes have before/after code examples
- [ ] Migration guide provides step-by-step instructions with verification
- [ ] Version bump follows semver correctly based on change categories
- [ ] Deprecations include replacement guidance and removal timeline
- [ ] Communication plan covers all consumer notification channels
- [ ] Migration path is validated — consumers can upgrade incrementally
- [ ] Changelog follows Keep a Changelog format consistently

## Evolution Notes
<!-- Observations appended after each use -->
