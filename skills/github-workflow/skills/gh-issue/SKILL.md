---
name: "GitHub Issue"
description: "Create, link, and manage GitHub issues with templates"
triggers:
  - "gh-issue"
  - "create issue"
  - "new issue"
  - "github issue"
  - "open issue"
version: "1.0.0"
user_invocable: true
---

## Scope Constraints

- Creates, views, closes, and links GitHub issues via gh CLI or GitHub MCP.
- Does not modify repository settings, branch protections, or code.
- Does not create PRs — use gh-pr-request or commit-push-pr skills for that.
- Does not perform batch triage — use gh-triage skill for bulk labeling.

## Input Sanitization

- Issue numbers: must be positive integers.
- Label names: reject null bytes and shell metacharacters (`; & | $ \` \\ < >`).
- Issue title and body text: reject null bytes.
- Repository identifier: inferred from local git context; if provided, must match `owner/repo` format with alphanumeric characters and hyphens only.

# /gh-issue - Create and Manage Issues

Create, view, link, and manage GitHub issues with template support.

## Usage

```bash
/gh-issue create              # Interactive issue creation
/gh-issue create --bug        # Create bug report
/gh-issue create --feature    # Create feature request
/gh-issue create --task       # Create task
/gh-issue view 123            # View issue #123
/gh-issue close 123           # Close issue #123
/gh-issue link 123            # Link current branch to issue
```

## Workflow

### Create Issue

#### Step 1: Gather Information

Use AskUserQuestion to collect:

1. **Issue Type**: Bug / Feature / Task
2. **Title**: Brief summary
3. **Description**: Detailed explanation
4. **Labels** (optional): bug, enhancement, documentation, etc.
5. **Assignees** (optional): Who should work on it

#### Step 2: Apply Template

Based on issue type, use appropriate template:

**Bug Template** (`~/.claude/skills/github-workflow/templates/issue-bug.md`):
```markdown
## Description
[What happened]

## Steps to Reproduce
1. [Step 1]
2. [Step 2]
3. [Step 3]

## Expected Behavior
[What should happen]

## Actual Behavior
[What actually happens]

## Environment
- OS: [e.g., macOS 14.0]
- Browser: [e.g., Chrome 120]
- Version: [e.g., v1.2.3]

## Additional Context
[Screenshots, logs, etc.]
```

**Feature Template** (`~/.claude/skills/github-workflow/templates/issue-feature.md`):
```markdown
## Summary
[Brief description of the feature]

## Motivation
[Why is this feature needed?]

## Proposed Solution
[How should this work?]

## Alternatives Considered
[Other approaches and why they weren't chosen]

## Additional Context
[Mockups, examples, references]
```

**Task Template** (`~/.claude/skills/github-workflow/templates/issue-task.md`):
```markdown
## Task
[What needs to be done]

## Acceptance Criteria
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]

## Notes
[Additional context or constraints]
```

#### Step 3: Create Issue

Use GitHub MCP or gh CLI:

```bash
# Using gh CLI
gh issue create --title "Title" --body "Body" --label "bug"

# Using GitHub MCP
mcp__github__create_issue(
    owner="owner",
    repo="repo",
    title="Issue title",
    body="Issue body",
    labels=["bug"]
)
```

### View Issue

```bash
gh issue view 123

# Or with MCP
mcp__github__get_issue(owner="owner", repo="repo", issue_number=123)
```

### Close Issue

```bash
gh issue close 123 --comment "Fixed in PR #456"

# Or with MCP
mcp__github__update_issue(
    owner="owner",
    repo="repo",
    issue_number=123,
    state="closed"
)
```

### Link Issue to Branch

Add issue reference to branch commits:

```bash
# Get current branch
BRANCH=$(git branch --show-current)

# If branch name contains issue number (feat/123-dark-mode)
ISSUE_NUM=$(echo "$BRANCH" | grep -oE '[0-9]+' | head -1)

echo "Branch $BRANCH linked to issue #$ISSUE_NUM"
echo "Commits will reference this issue automatically."
```

## Output Format

### Issue Created

```
Created issue #456: Fix login validation bug

URL: https://github.com/owner/repo/issues/456

Details:
  Type: Bug
  Labels: bug, priority-high
  Assignees: @username

Next steps:
  /git-branch fix/456-login-validation  # Create linked branch
  /gh-triage                              # Triage more issues
```

### Issue View

```
Issue #456: Fix login validation bug

State: Open
Created: 2 days ago by @reporter
Labels: bug, priority-high
Assignees: @username

Description:
  Login form accepts empty email addresses when it shouldn't.

Comments (3):
  @user1 (1 day ago): I can reproduce this.
  @user2 (12 hours ago): Working on a fix.
  @user3 (2 hours ago): PR #789 addresses this.

Related PRs:
  #789 (open) - Fix email validation

Actions:
  /gh-pr-status 789    # Check PR status
  /gh-issue close 456  # Close when fixed
```

## Common Labels

| Label | Use For |
|-------|---------|
| `bug` | Something isn't working |
| `enhancement` | New feature or request |
| `documentation` | Documentation improvements |
| `good first issue` | Good for newcomers |
| `help wanted` | Extra attention needed |
| `priority-high` | Urgent issues |
| `wontfix` | Won't be worked on |

## Branch Naming with Issues

When creating branches for issues, include the issue number:

```bash
/git-branch feat/123-dark-mode     # Feature for issue #123
/git-branch fix/456-login-bug      # Bug fix for issue #456
```

This enables:
- Automatic linking in GitHub
- Easy navigation between issue and code
- Commit message linking: "Fix #456"

## Integration

- Use `/git-branch feat/123-feature` to create linked branch
- Use `/gh-triage` to batch label issues
- Use `/commit` with "Fixes #123" in message to auto-close
- Use `/gh-pr-status` to check PR linked to issue
