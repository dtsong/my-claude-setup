---
name: "GitHub Triage"
description: "Batch label and prioritize GitHub issues"
triggers:
  - "gh-triage"
  - "triage issues"
  - "label issues"
  - "prioritize issues"
version: "1.0.0"
user_invocable: true
---

# /gh-triage - Batch Issue Triage

Review and triage unlabeled or unassigned issues efficiently.

## Usage

```bash
/gh-triage                    # Triage unlabeled issues
/gh-triage --unlabeled        # Show only unlabeled issues
/gh-triage --unassigned       # Show unassigned issues
/gh-triage --stale            # Show issues with no activity >30 days
/gh-triage --all              # Full triage dashboard
```

## Workflow

### Step 1: Fetch Issues Needing Triage

```bash
# Get unlabeled open issues
gh issue list --state open --label "" --json number,title,body,createdAt

# Get unassigned issues
gh issue list --state open --assignee "" --json number,title,labels

# Get stale issues (no activity in 30 days)
gh issue list --state open --json number,title,updatedAt | \
    jq '[.[] | select(.updatedAt < (now - 30*24*60*60 | todate))]'
```

### Step 2: Present Issues for Triage

For each issue, analyze and suggest:
- Appropriate labels
- Priority level
- Potential assignees
- Whether to close (duplicate, invalid, etc.)

### Step 3: Apply Triage Decisions

```bash
# Add labels
gh issue edit 123 --add-label "bug,priority-high"

# Assign
gh issue edit 123 --add-assignee "@username"

# Close as duplicate
gh issue close 123 --comment "Duplicate of #456" --reason "not planned"

# Close as stale
gh issue close 123 --comment "Closing due to inactivity. Please reopen if still relevant."
```

## Output Format

### Triage Dashboard

```
Issue Triage Dashboard

Repository: owner/repo
Open issues: 47
Needs triage: 12

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

UNLABELED ISSUES (5)

#456 - Login fails on mobile
  Created: 3 days ago by @user1
  Body: "When I try to log in on my iPhone, the form..."

  Analysis:
    Type: Bug (mobile-specific issue)
    Priority: High (blocks users)
    Similar: None found

  Suggested actions:
    - Add labels: bug, mobile, priority-high
    - Assign: @mobile-team

  [Apply] [Skip] [View Full]

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#457 - Add dark mode
  Created: 5 days ago by @user2
  Body: "Would be great to have a dark theme..."

  Analysis:
    Type: Feature Request
    Priority: Medium (enhancement)
    Similar: #123 (open), #234 (closed - wontfix)

  Suggested actions:
    - Add labels: enhancement, ui
    - Consider: Close as duplicate of #123?

  [Apply] [Duplicate of #123] [Skip]

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

STALE ISSUES (3)

#234 - Feature request from 6 months ago
  Last activity: 45 days ago
  Status: No response from author

  Suggested action: Close as stale

  [Close as Stale] [Ping Author] [Keep Open]

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Summary:
  Triaged: 8 issues
  Labeled: 5
  Closed: 2 (duplicates)
  Closed: 1 (stale)
```

### Quick Triage Mode

For fast bulk triage:

```
Quick Triage - Unlabeled Issues

#456 Login fails on mobile    [bug] [enhancement] [question] [skip]
#457 Add dark mode            [bug] [enhancement] [question] [skip]
#458 Documentation unclear    [bug] [enhancement] [question] [skip]
#459 Performance issue        [bug] [enhancement] [question] [skip]

Selected labels will be applied.
Type number to view issue details.
```

## Label Suggestions

Claude analyzes issue content to suggest labels:

| Content Pattern | Suggested Label |
|-----------------|-----------------|
| "doesn't work", "broken", "error" | bug |
| "would be nice", "feature", "add" | enhancement |
| "how do I", "question", "help" | question |
| "docs", "documentation", "readme" | documentation |
| "slow", "performance", "memory" | performance |
| "security", "vulnerability", "CVE" | security |

## Priority Assessment

Priority is suggested based on:

| Factor | Priority |
|--------|----------|
| Blocks core functionality | critical |
| Affects many users | high |
| Has workaround | medium |
| Nice to have | low |
| Outdated/stale | close candidate |

## Duplicate Detection

When analyzing issues, Claude checks for:

1. Similar titles (fuzzy match)
2. Same error messages
3. Related keywords
4. Links between issues

```
Potential duplicate detected!

#456: Login fails on mobile
  May be duplicate of:
    #234 (open): Mobile login issues
    #123 (closed): iOS login bug

Actions:
  [Close as duplicate of #234]
  [Link to #234]
  [Keep separate]
```

## Batch Operations

Apply same action to multiple issues:

```bash
# Label multiple issues
gh issue edit 456 457 458 --add-label "needs-investigation"

# Close multiple stale issues
for issue in 123 234 345; do
    gh issue close $issue --comment "Closing stale issue"
done
```

## Integration

- Use `/gh-issue create` for new issues
- Use `/gh-mine` to see your assigned issues
- Use `/gh-health` for overall repository health
