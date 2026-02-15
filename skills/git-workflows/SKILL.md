---
name: "Git Workflows"
description: "Local git operations for syncing, branching, merging, and conflict resolution"
triggers:
  - "git workflow"
  - "git help"
  - "git operations"
user_invocable: true
---

# Git Workflows

A comprehensive suite of git workflow skills for local repository operations.

## Input Sanitization

- Branch names: alphanumeric, hyphens, underscores, forward slashes, and dots only — reject `..`, shell metacharacters, or null bytes
- Remote names: alphanumeric and hyphens only
- File paths for stash/diff: reject `..` traversal, null bytes, and shell metacharacters

## Available Skills

### Sync & Remote Operations
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/git-sync` | Fetch and show remote changes | `git sync`, `what's new upstream` |
| `/git-pull` | Pull with merge/rebase strategy | `git pull`, `get latest` |
| `/git-push` | Push with upstream handling | `git push`, `push changes` |

### Stash Management
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/git-stash` | Save/pop/list stashed changes | `git stash`, `save my work` |

### Branch Operations
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/git-branch` | Create branches with naming conventions | `git branch`, `new branch` |
| `/git-switch` | Switch branches safely | `git switch`, `checkout branch` |
| `/git-branches` | List and visualize branch status | `git branches`, `list branches` |
| `/git-delete-branch` | Delete local/remote with safety | `delete branch`, `cleanup branch` |

### Integration & Merging
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/git-merge-main` | Merge main into feature branch | `merge main`, `update from main` |
| `/git-rebase` | Rebase onto main with guidance | `git rebase`, `rebase onto main` |
| `/git-squash` | Squash commits non-interactively | `git squash`, `clean up commits` |

### Conflict & Recovery
| Skill | Purpose | Invoke |
|-------|---------|--------|
| `/git-abort` | Abort failed merge/rebase/cherry-pick | `git abort`, `cancel merge` |
| `/git-conflicts` | Guided conflict resolution | `git conflicts`, `fix conflicts` |

## Quick Reference

```bash
# Sync workflow
/git-sync              # See what's new
/git-pull              # Get changes
/git-push              # Push changes

# Branch workflow
/git-branch feat/xyz   # Create branch
/git-switch main       # Switch branch
/git-branches          # See all branches

# Integration
/git-merge-main        # Update from main
/git-rebase            # Rebase on main
/git-squash            # Clean up history
```

## Related Skills

- `/commit` - Create commits with conventional messages
- `/commit-push-pr` - Full commit, push, and PR workflow
- `/gh-pr-*` - GitHub PR operations
