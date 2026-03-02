# Ship Review Rules

Rules for parsing `/pr-review-toolkit:review-pr all` output and classifying pass/fail.

## Output Format

The review produces a markdown summary with these sections:

```markdown
# PR Review Summary

## Critical Issues (X found)
- [agent-name]: Issue description [file:line]

## Important Issues (X found)
- [agent-name]: Issue description [file:line]

## Suggestions (X found)
- [agent-name]: Suggestion [file:line]

## Strengths
- What's well-done in this PR
```

## Parsing Rules

Extract severity counts from section headers:

| Pattern | Extract |
|---------|---------|
| `## Critical Issues (N found)` | N = critical count |
| `## Important Issues (N found)` | N = important count |
| `## Suggestions (N found)` | N = suggestion count (informational only) |

If a section header says `(0 found)` or is absent, that count is 0.

## Pass/Fail Classification

| Critical | Important | Result |
|----------|-----------|--------|
| 0 | 0 | **PASS** — merge eligible |
| 0 | >0 | **FAIL** — fix important findings |
| >0 | any | **FAIL** — fix critical findings first |

Suggestions do NOT affect pass/fail. They are logged but not actioned in autonomous fix cycles.

## Fix Cycle Rules

When review fails, enter autonomous fix cycle:

1. **Fix critical findings first** — address all critical issues before any important ones
2. **Then fix important findings** — address remaining important issues
3. **Re-run ALL quality gates** after fixes (a fix may break gates)
4. **Push changes** to the feature branch
5. **Re-invoke review** — `/pr-review-toolkit:review-pr all`
6. **Re-classify** using the same parsing rules above

## Cycle Limits

- Maximum review cycles controlled by `--max-review-cycles` (default: 3)
- Cycle count includes the initial review (cycle 1 = first review)
- If still failing after max cycles → mark `review-failed`, skip to next issue

## Merge Conflict Handling

Before merging, check for conflicts with updated main:

```bash
git fetch origin main
git rebase origin/main
```

If rebase conflicts occur:
1. Resolve conflicts
2. Re-run all quality gates
3. Push force-with-lease
4. Re-invoke review (counts as a review cycle)
5. If this exceeds max cycles → mark `review-failed`
