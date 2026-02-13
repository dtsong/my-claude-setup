---
description: Generate GitHub issues from a roadmap document. Creates issues with labels, milestones, and dependency references.
argument-hint: "[--help] <roadmap-file>"
allowed-tools: Bash(gh:*), Read, Write, Glob
---

# Create GitHub Issues from Roadmap

You are creating GitHub issues from a structured roadmap document.

## Help Flag

If the argument is `--help`, show a brief usage summary and exit:
```
/create-issues [--help] <roadmap-file>
Generate GitHub issues from a roadmap document. Creates issues with labels, milestones, and dependency references.
```
Then say: `Run /help create-issues for full details.`

## Instructions

1. **Read the roadmap file** specified in $ARGUMENTS (default: `docs/ROADMAP.md`)

2. **For each task/section in the roadmap**, create a GitHub issue with:
   - Title: `[Phase X.Y] Task description`
   - Body: Full requirements from roadmap section
   - Labels: `phase-1`, `phase-2`, etc. + `gate`, `review`, `dashboard`, `mcp` as appropriate
   - Milestone: Create milestones for each phase if they don't exist

3. **Track dependencies** by adding "Blocked by #N" in issue body where N is the issue number of the dependency

4. **Issue body template**:
```markdown
## Overview
[Brief description from roadmap]

## Requirements
[Bullet points from roadmap]

## Files to Create/Modify
- [ ] `path/to/file.py`
- [ ] `tests/test_file.py`

## Config Changes
[Any .ai-review.yaml additions]

## Dependencies
- Blocked by #N (if applicable)

## Acceptance Criteria
- [ ] Implementation complete
- [ ] Tests passing
- [ ] Documentation updated
```

5. **Create issues in dependency order** so you can reference blocking issues by number

6. **Output a summary** mapping issue numbers to task IDs when complete

## Commands

```bash
# Check if gh CLI is authenticated
gh auth status

# Create a milestone
gh api repos/{owner}/{repo}/milestones -f title="Phase 1: Additional Gates" -f state="open"

# Create an issue
gh issue create --title "[1.1] Security Scan Gate" --body "..." --label "phase-1,gate" --milestone "Phase 1: Additional Gates"

# List created issues
gh issue list --label "roadmap"
```

## Example Usage

```
/create-issues docs/ROADMAP.md
```
