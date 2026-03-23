---
description: "Post-council pipeline: implement GitHub issues, review PRs, iterate on findings, and merge. Issues in, merged PRs out."
argument-hint: "<issues...> [--from-session <id>] [--max-review-cycles N] [--merge-strategy <squash|rebase|merge>] [--no-merge] [--resume]"
allowed-tools: Bash(git checkout:*), Bash(git checkout -b:*), Bash(git pull:*), Bash(git push:*), Bash(git add:*), Bash(git commit:*), Bash(git diff:*), Bash(git status:*), Bash(git log:*), Bash(git branch:*), Bash(git stash:*), Bash(git fetch:*), Bash(git rebase:*), Bash(git merge:*), Bash(gh issue:*), Bash(gh pr:*), Bash(gh api:*), Bash(gh auth:*), Bash(jq:*), Bash(npm:*), Bash(npx:*), Bash(uv:*), Bash(pytest:*), Bash(source ~/.nvm/nvm.sh:*), Bash(mkdir:*), Read, Edit, Write, Glob, Grep, Skill
---

# /ship — Issue-to-Merge Pipeline

Implement GitHub issues into PRs, review them, iterate on findings autonomously, and merge. Delegates implementation to `/looper` per-issue, then wraps with a review-iterate-merge outer loop.

## Input

Parse the provided arguments: `$ARGUMENTS`

### Issue Selectors

Same as `/looper`:

```
/ship 42                           # Single issue
/ship #42                          # Single issue with hash
/ship 42 43 44                     # Multiple issues (space-separated)
/ship 42,43,44                     # Multiple issues (comma-separated)
/ship 42-48                        # Inclusive range
/ship --label roadmap              # All open issues with label
/ship --milestone "Phase 1"        # All open issues in milestone
```

### Flags

```
--from-session <id>   Read issues from council session artifacts, auto-set --contract
--max-review-cycles N Maximum review iterations per PR (default: 3)
--merge-strategy <s>  squash (default), rebase, or merge
--no-merge            Stop after review passes, don't auto-merge
--resume              Resume from .claude/ship-state.md
--max-retries N       Looper retry attempts per issue (default: 3)
--constraints "..."   Freeform constraints passed to looper
--contract <path>     Acceptance contract for criteria verification
--preview             Show execution plan, don't run
```

## Git Safety Context

All work in this skill happens on **feature branches** that get submitted as **pull requests** back to main. Merges use the configured strategy (default: squash) with `--delete-branch`. All git operations are safe, reversible workflow steps. Proceed with git and gh commands without additional confirmation.

---

## Phase A: INTAKE

### Step 1: Parse Arguments

Extract from `$ARGUMENTS`:
- Issue numbers (handling all formats: `42`, `#42`, `42 43 44`, `42,43,44`, `42-48`)
- `--label <label>` — fetch open issues by label
- `--milestone <name>` — fetch open issues by milestone
- `--from-session <id>` — read session artifacts
- `--max-review-cycles N` (default: 3)
- `--merge-strategy <strategy>` (default: squash)
- `--no-merge` flag
- `--resume` flag
- `--preview` flag
- `--max-retries N` (default: 3)
- `--constraints "..."` text
- `--contract <path>`

### Step 2: Resolve Issues

If `--resume` is set, skip to **Phase B, Step 5 (Resume)**.

**If `--from-session <id>`:**

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
SESSION_DIR="$WORKSPACE/.claude/council/sessions/$SESSION_ID"
```

1. Read `$SESSION_DIR/issues.md` — parse the issue map table for issue numbers
2. Auto-set contract path: `--contract $SESSION_DIR/acceptance-contract.md` (if file exists and `--contract` not already set)
3. Extract issue numbers from the `| #<N> |` column

**Otherwise**, fetch issue details:

```bash
# By number
gh issue view $N --json number,title,body,labels,milestone,state

# By label
gh issue list --label "$LABEL" --state open --json number,title,body,labels,milestone --limit 100

# By milestone
gh issue list --milestone "$MILESTONE" --state open --json number,title,body,labels,milestone --limit 100
```

Validate:
- All explicitly-requested issues exist and are open
- Warn about any issues that are already closed (skip them)

### Step 3: Extract Dependencies & Topological Sort

Parse each issue body for dependency markers (case-insensitive):
- `Blocked by #N`
- `Depends on #N`
- `Requires #N`
- `After #N`

Classify each dependency:
- **in-batch** — the blocking issue is in this run's queue (resolve during execution)
- **external-closed** — the blocking issue is NOT in the batch but is already closed (satisfied)
- **external-open** — the blocking issue is NOT in the batch and is still open (skip this issue)

Topological sort using Kahn's algorithm:
1. Build adjacency list from in-batch dependencies
2. Initialize queue with issues that have zero in-degree
3. Process queue, adding newly unblocked issues
4. If any issues remain after queue is empty — **cycle detected** — report the cycle and remove those issues from the queue with a warning

Issues with external-open blockers are placed at the end with status `blocked`.

---

## Phase B: PLANNING

### Step 4: Auto-Detect Quality Gates

Delegate gate detection to looper (looper will auto-detect when invoked per-issue).

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
```

### Step 5: Initialize or Resume State File

**State file location:** `$WORKSPACE/.claude/ship-state.md`

See `commands/references/ship-state-schema.md` for the full state file format.

#### New Run — Create State File

```bash
mkdir -p $WORKSPACE/.claude
```

Write state file with YAML frontmatter (`active: true`, `phase: "executing"`, timestamps, config) and the issue queue table, empty progress section, and empty decisions log.

#### Resume — Read Existing State File

Read `$WORKSPACE/.claude/ship-state.md`. Parse:
- Which issues are in what status
- Previous progress, review cycles, decisions
- Resume from the first issue that is not `merged`, `impl-failed`, or `review-failed`

Update `updated_at` timestamp and set `active: true`.

#### Preview Mode

If `--preview` is set: display the state file contents (issue queue, dependency graph) and **stop**.

---

## Phase C: EXECUTION LOOP

Process each issue in topological order. For each issue:

### Step 6: Check Merge-Order Dependencies

Before starting an issue, verify all its in-batch blockers are **merged** (not just implemented — stricter than looper):
- If a blocker is `merged` — satisfied
- If a blocker is `review-passed` or earlier — **wait** (defer to Phase D sweep)
- If a blocker is `impl-failed` or `review-failed` — skip this issue (mark as `blocked`)

For external dependencies, re-check via `gh issue view`:
- If now closed — satisfied
- If still open — skip this issue (mark as `blocked`)

### Step 7: Implement via Looper

Update state: mark issue as `implementing`.

Invoke `/looper` for a single issue:

```
/looper <issue-number> --max-retries $MAX_RETRIES --contract $CONTRACT_PATH --constraints "$CONSTRAINTS"
```

Capture the PR number from looper's output. If looper fails (issue marked `failed` in looper state), mark as `impl-failed` in ship state and skip to next issue.

On success, update state: mark as `pr-created`, record PR number and branch name.

**Important:** After looper completes, ensure you are on the feature branch for this issue (looper may have returned to main).

### Step 8: Review

Update state: mark issue as `reviewing`.

Invoke the PR review toolkit on the feature branch:

```
/pr-review-toolkit:review-pr all
```

### Step 9: Classify Review Results

See `commands/references/ship-review-rules.md` for parsing rules.

Parse review output for severity headers:
- `## Critical Issues (N found)` — extract N
- `## Important Issues (N found)` — extract N

**Classification:**
- 0 critical + 0 important → **PASS**
- Otherwise → **FAIL**, enter fix cycle

### Step 10: Fix Cycle

When review fails, enter autonomous fix cycle (max `--max-review-cycles` iterations, counting from cycle 1 = initial review):

1. Update state: mark issue as `fixing`
2. Classify each finding as AUTO-FIX or ASK per `commands/references/ship-review-rules.md § Fix-First Classification`
3. Apply all AUTO-FIX items in a single commit:
   ```bash
   git add <changed-files>
   git commit -m "fix: auto-fix review findings for #$ISSUE_NUMBER"
   ```
4. Batch all ASK items into one AskUserQuestion — wait for user response before continuing
5. Apply user-approved fixes
6. Re-run ALL quality gates (a fix may break gates):
   ```bash
   # Detect and run gates same as looper Step 6d
   ```
7. Commit remaining fixes:
   ```bash
   git add <changed-files>
   git commit -m "fix: address review findings for #$ISSUE_NUMBER

   Review cycle $CYCLE/$MAX_CYCLES"
   ```
8. Push to feature branch:
   ```bash
   git push origin HEAD
   ```
9. Re-invoke review:
   ```
   /pr-review-toolkit:review-pr all
   ```
10. Re-classify per Step 9
11. If PASS → proceed to merge
12. If FAIL and cycles remaining → repeat from step 2
13. If FAIL and no cycles remaining → mark `review-failed`, skip to next issue

### Step 11: Merge

When review passes:

1. Update state: mark issue as `review-passed`
2. Check all blocker PRs are merged:
   - If any blocker is not `merged` → mark as `blocked`, defer to Phase D sweep
3. Rebase against updated main to catch conflicts:
   ```bash
   git fetch origin main
   git rebase origin/main
   ```
   If rebase conflicts occur:
   - Resolve conflicts
   - Re-run all quality gates
   - Push with `--force-with-lease`
   - Re-invoke review (counts as a review cycle)
   - If exceeds max cycles → mark `review-failed`
4. If `--no-merge` is set → leave as `review-passed`, skip merge
5. Merge:
   ```bash
   gh pr merge $PR --$MERGE_STRATEGY --delete-branch
   ```
6. Return to main:
   ```bash
   git checkout main && git pull origin main
   ```
7. Update state: mark issue as `merged`

### Step 12: Checkpoint State

After every status transition, update the state file:
- Update issue status, PR number, attempt counts, review cycles
- Record progress details under the issue's section
- Log decisions
- Update `updated_at` timestamp

This checkpoint enables `--resume` if the session is interrupted.

---

## Phase D: DEFERRED MERGE SWEEP

After the main loop completes, sweep `review-passed` issues whose blockers are now merged.

1. Collect all issues with status `review-passed` that were deferred due to unmerged blockers
2. Re-check blocker statuses — some may have been merged during the main loop
3. For each now-unblocked issue (in topological order):
   a. Checkout the feature branch
   b. Rebase against updated main
   c. If rebase conflicts → resolve, re-run gates, re-review (counts as a cycle)
   d. Merge using configured strategy
   e. Return to main, pull
   f. Update state to `merged`
4. Repeat sweep until no more issues can be unblocked

Issues still blocked after the sweep remain as `blocked` in the state file.

---

## Phase E: REPORTING

### Final Summary

```
Ship Complete

  Issues: N/M merged, F failed, B blocked
  PRs merged: N
  Total impl attempts: X (across all issues)
  Total review cycles: Y (across all issues)
  Merge strategy: squash

  | Issue | PR   | Title              | Impl Attempts | Review Cycles | Status        |
  |-------|------|--------------------|---------------|---------------|---------------|
  | #42   | #101 | Auth module        | 1             | 1             | merged        |
  | #43   | #102 | API routes         | 2             | 3             | merged        |
  | #44   | —    | Dashboard          | 0             | 0             | blocked       |
  | #45   | #103 | Notifications      | 1             | 3             | review-failed |

  Failed/Blocked:
  | Issue | Status        | Reason                           |
  |-------|---------------|----------------------------------|
  | #44   | blocked       | Blocked by #99 (external-open)   |
  | #45   | review-failed | Max review cycles exceeded (3/3) |

  State: .claude/ship-state.md
```

If `--from-session` was used:
```
  Session: <session-id>
  Contract: $CONTRACT_PATH
```

Update state file: `active: false`, `phase: "complete"`.

---

## Important Rules

1. **Merge-order dependencies are strict** — a blocker must be `merged` (not just implemented) before its dependent can merge
2. **Delegate implementation to /looper** — never reimplement looper's quality gate logic
3. **Autonomous fix cycles** — fix critical/important findings without user approval, up to max cycles
4. **Re-run ALL gates after every fix** — a fix may break other gates
5. **Checkpoint after every transition** — enable resume on interruption
6. **Separate state files** — ship uses `.claude/ship-state.md`, looper uses `.claude/looper-state.md`
7. **Respect dependency order** — topological sort for implementation, merge-order for merging
8. **Rebase before merge** — catch conflicts from prior merges
9. **Node.js commands** must be wrapped: `source ~/.nvm/nvm.sh && nvm use default --silent && <cmd>`
10. **Failed issues don't block unrelated issues** — only issues with explicit dependency markers are affected
