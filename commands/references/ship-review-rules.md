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

## Fix-First Classification

After parsing severity, classify each finding by fix strategy:

### AUTO-FIX (Apply Immediately)

Mechanical, low-risk fixes with deterministic correct solutions:

- Unused imports or variables
- Missing trailing commas / semicolons (per project linter config)
- Simple type errors with obvious fixes (e.g., `string` vs `String`)
- Formatting violations (whitespace, indentation)
- Missing `await` on async calls
- Stale `console.log` / debug statements
- Import ordering violations

**Rule:** Apply all AUTO-FIX items in a single commit before entering the fix cycle.
Commit message: `fix: auto-fix review findings for #$ISSUE_NUMBER`

### ASK (Batch for User Decision)

Findings requiring judgment, architectural knowledge, or trade-off decisions:

- API design changes (renaming, restructuring endpoints)
- Business logic changes ("should this validate X?")
- Performance trade-offs (caching strategy, query optimization approach)
- Security findings with multiple valid mitigation paths
- Architectural changes (moving code between modules, changing patterns)

**Rule:** Batch all ASK items into one AskUserQuestion:

```
Review found N findings requiring your judgment:
1. [finding] — Options: A) [option], B) [option] [Recommended: A]
2. [finding] — Options: A) [option], B) [option]
Reply with your choices or 'skip all' to defer.
```

### Classification Precedence

1. If a Critical finding is AUTO-FIX → still auto-fix it (severity does not block automation)
2. If all remaining findings are ASK → present to user instead of burning a fix cycle
3. If a finding is ambiguous → classify as ASK (err toward user involvement)

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
