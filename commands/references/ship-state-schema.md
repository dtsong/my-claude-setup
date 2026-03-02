# Ship State Schema

State file location: `$WORKSPACE/.claude/ship-state.md`

## YAML Frontmatter

```yaml
---
active: true
phase: "intake|executing|sweep|complete"
created_at: "YYYY-MM-DDTHH:MM:SS"
updated_at: "YYYY-MM-DDTHH:MM:SS"
max_review_cycles: 3
merge_strategy: "squash|rebase|merge"
no_merge: false
session_id: "<council-session-slug>"    # if --from-session
contract_path: "<path>"                 # if --contract or auto-set from session
---
```

## Markdown Body

```markdown
## Issue Queue

| # | Issue | Title | Status | Blocked By | PR | Impl Attempts | Review Cycles |
|---|-------|-------|--------|------------|----|---------------|---------------|
| 1 | #42 | Auth module | merged | — | #101 | 1 | 1 |
| 2 | #43 | API routes | reviewing | #42 | #102 | 1 | 2 |
| 3 | #44 | Dashboard | pending | #43 | — | 0 | 0 |

## Progress

### Issue #42: Auth module
**Status:** merged
**Branch:** feat/42-auth-module
**PR:** #101
**Impl attempts:** 1 | **Review cycles:** 1/3

#### Implementation
Delegated to /looper — completed on attempt 1.

#### Review Cycle 1
- Result: PASS (0 critical, 0 important)

#### Merge
- Merged via squash at <timestamp>

---

### Issue #43: API routes
**Status:** reviewing
**Branch:** feat/43-api-routes
**PR:** #102
**Impl attempts:** 1 | **Review cycles:** 2/3

#### Review Cycle 1
- Result: FAIL (1 critical, 2 important)
- Findings: <summary>

#### Fix Cycle 1
- Fixed: <what was fixed>
- Gates: all passing
- Re-review triggered

#### Review Cycle 2
- Result: PENDING

## Decisions Log

- <timestamp>: Started issue #42 — no blockers
- <timestamp>: Issue #42 review passed, merging
- <timestamp>: Issue #43 review failed cycle 1 — 1 critical finding
```

## Status Values

| Status | Meaning |
|--------|---------|
| `pending` | Not yet started |
| `implementing` | Delegated to /looper, in progress |
| `pr-created` | Looper completed, PR exists |
| `reviewing` | PR review in progress |
| `fixing` | Fixing review findings |
| `review-passed` | Review passed, awaiting merge |
| `merging` | Merge in progress |
| `merged` | Successfully merged |
| `blocked` | Dependency not yet merged |
| `impl-failed` | Looper failed after max retries |
| `review-failed` | Review failed after max cycles |
