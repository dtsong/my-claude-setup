---
name: "GitHub Workflow"
description: "GitHub interactions for issues, PRs, releases, and repository management"
triggers:
  - "github workflow"
  - "github help"
  - "gh operations"
user_invocable: true
---

# GitHub Workflow

A comprehensive suite of GitHub workflow skills using the `gh` CLI and GitHub MCP tools.

## Available Skills

### Issue Management
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/gh-issue` | Create/link/close issues | `gh-issue`, `create issue` |
| `/gh-triage` | Batch label and prioritize | `gh-triage`, `triage issues` |

### Pull Request Workflow
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/gh-pr-status` | Check PR status, CI, merge readiness | `gh-pr-status`, `pr status` |
| `/gh-pr-request` | Request reviewers | `gh-pr-request`, `request review` |
| `/gh-pr-respond` | View/respond to review comments | `gh-pr-respond`, `pr comments` |
| `/gh-pr-merge` | Merge PR with strategy | `gh-pr-merge`, `merge pr` |
| `/gh-pr-update` | Update PR branch with base | `gh-pr-update`, `update pr` |

### Releases & Tags
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/gh-release` | Create release with changelog | `gh-release`, `new release` |
| `/gh-tag` | Semantic version tagging | `gh-tag`, `create tag` |
| `/gh-changelog` | Generate changelog from PRs | `gh-changelog`, `release notes` |

### Repository Status
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/gh-health` | Repository health dashboard | `gh-health`, `repo status` |
| `/gh-mine` | My assigned/mentioned items | `gh-mine`, `my issues` |
| `/gh-activity` | Recent activity summary | `gh-activity`, `what happened` |

## Quick Reference

```bash
# Issue workflow
/gh-issue create       # Create new issue
/gh-triage             # Triage open issues

# PR workflow
/gh-pr-status          # Check current PR
/gh-pr-request @user   # Request review
/gh-pr-respond         # Handle comments
/gh-pr-merge           # Merge when ready

# Release workflow
/gh-changelog          # Generate notes
/gh-tag v1.2.0         # Create tag
/gh-release            # Create release

# Dashboard
/gh-health             # Repo overview
/gh-mine               # My items
/gh-activity           # Recent activity
```

## Related Skills

- `/commit` - Create commits with conventional messages
- `/commit-push-pr` - Full commit, push, and PR workflow
- `/git-*` - Local git operations
- `/review-pr` - Review pull requests
