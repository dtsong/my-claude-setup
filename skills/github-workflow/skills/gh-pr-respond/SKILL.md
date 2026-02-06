---
name: "GitHub PR Respond"
description: "View and respond to PR review comments"
triggers:
  - "gh-pr-respond"
  - "pr comments"
  - "review comments"
  - "respond to review"
  - "address feedback"
version: "1.0.0"
user_invocable: true
---

# /gh-pr-respond - Respond to Review Comments

View and respond to review comments on a pull request.

## Usage

```bash
/gh-pr-respond              # Show comments on current PR
/gh-pr-respond 123          # Show comments on PR #123
/gh-pr-respond --unresolved # Show only unresolved threads
/gh-pr-respond --mine       # Show comments requiring my response
```

## Workflow

### Step 1: Fetch PR Comments

```bash
# Get PR for current branch
PR_NUM=$(gh pr view --json number -q '.number' 2>/dev/null)

# Get review comments
gh api repos/{owner}/{repo}/pulls/$PR_NUM/comments

# Get reviews with comments
gh pr view $PR_NUM --json reviews,reviewThreads
```

Using GitHub MCP:

```javascript
mcp__github__get_pull_request_comments(owner, repo, pr_number)
mcp__github__get_pull_request_reviews(owner, repo, pr_number)
```

### Step 2: Categorize Comments

Organize by:
- Resolved vs unresolved
- By file
- By reviewer
- By severity (blocking vs suggestion)

### Step 3: Help Respond

For each comment:
- Show context (code snippet)
- Explain the feedback
- Suggest response or code fix

## Output Format

### Full Comment View

```
Review Comments for PR #123

4 comments total, 2 unresolved

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

UNRESOLVED (2)

[1] src/components/Theme.tsx:45 - @reviewer1 (1 day ago)
    Status: Unresolved | Type: Suggestion

    Code:
    │ 44  const theme = useTheme();
    │ 45  const colors = getColors(theme);
    │ 46  const styles = createStyles(colors);

    Comment:
    "Consider memoizing this with useMemo to prevent
    recalculation on every render."

    Suggested response:
      A) Apply fix: Add useMemo wrapper
      B) Reply: Explain why memoization isn't needed
      C) Reply: Ask for clarification

    [Apply Fix] [Reply] [Resolve]

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

[2] src/hooks/useTheme.ts:12 - @reviewer2 (6 hours ago)
    Status: Unresolved | Type: Bug

    Code:
    │ 11  useEffect(() => {
    │ 12    const listener = window.matchMedia('...').addEventListener(...);
    │ 13  }, []);

    Comment:
    "This event listener is never cleaned up, which will
    cause a memory leak. Add a cleanup function."

    Suggested fix:
    ```typescript
    useEffect(() => {
      const mql = window.matchMedia('...');
      const handler = (e) => { ... };
      mql.addEventListener('change', handler);
      return () => mql.removeEventListener('change', handler);
    }, []);
    ```

    [Apply Fix] [Reply] [Resolve]

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

RESOLVED (2)

[3] src/styles/theme.css:23 - @reviewer1
    "Consider using CSS custom properties"
    ✓ Resolved by @you: "Applied - using CSS variables now"

[4] README.md:45 - @reviewer2
    "Update documentation for dark mode"
    ✓ Resolved by @you: Fixed in commit abc1234
```

### Apply Fix Mode

When choosing to apply a fix:

```
Applying fix for comment [2]...

File: src/hooks/useTheme.ts

Changes:
  - Added cleanup function to useEffect
  - Event listener properly removed on unmount

Modified code:
  │ 11  useEffect(() => {
  │ 12    const mql = window.matchMedia('(prefers-color-scheme: dark)');
  │ 13    const handler = (e: MediaQueryListEvent) => setTheme(e.matches ? 'dark' : 'light');
  │ 14    mql.addEventListener('change', handler);
  │ 15    return () => mql.removeEventListener('change', handler);
  │ 16  }, []);

Next steps:
  1. Review the change
  2. /commit to commit the fix
  3. /git-push to update PR
  4. Reply to the comment (optional)
```

### Reply Mode

```
Reply to @reviewer2's comment:

Original comment:
  "This event listener is never cleaned up..."

Your reply:
> Good catch! I've added a cleanup function in the latest commit (abc1234).
> Let me know if there's anything else.

[Send Reply] [Edit] [Cancel]
```

### Batch Response

```
Respond to all unresolved comments:

Summary of changes made:
  [1] Added useMemo for theme calculation
  [2] Added useEffect cleanup function

Would you like to:
  A) Commit all fixes together
  B) Reply to each comment individually
  C) Resolve all as "addressed in latest commit"
```

## Response Strategies

| Comment Type | Suggested Response |
|--------------|-------------------|
| Bug/Error | Fix the code, commit, reference commit |
| Suggestion | Apply if good, or explain why not |
| Question | Answer clearly, add context |
| Nitpick | Apply or discuss |
| Blocking | Must address before merge |

## Commit with Comment Reference

When committing fixes:

```bash
git commit -m "Address review feedback

- Add useMemo for theme calculation (comment #1)
- Add useEffect cleanup function (comment #2)

Co-Authored-By: Claude <noreply@anthropic.com>"
```

## Integration

- Use `/gh-pr-status` to see overall PR status
- Use `/commit` to commit fixes
- Use `/git-push` to update PR
- Use `/gh-pr-merge` when all comments resolved
