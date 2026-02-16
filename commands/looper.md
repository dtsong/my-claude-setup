---
description: "Implement GitHub issues into PRs with dependency ordering, quality gate retry loops, and checkpoint/resume."
argument-hint: "<issues...> [--label <label>] [--milestone <name>] [--combined] [--resume] [--preview] [--max-retries N] [--constraints \"...\"] [--contract <path>]"
allowed-tools: Bash(git checkout:*), Bash(git checkout -b:*), Bash(git pull:*), Bash(git push:*), Bash(git add:*), Bash(git commit:*), Bash(git diff:*), Bash(git status:*), Bash(git log:*), Bash(git branch:*), Bash(git stash:*), Bash(gh issue:*), Bash(gh pr:*), Bash(gh api:*), Bash(gh auth:*), Bash(jq:*), Bash(npm:*), Bash(npx:*), Bash(uv:*), Bash(pytest:*), Bash(source ~/.nvm/nvm.sh:*), Bash(mkdir:*), Read, Edit, Write, Glob, Grep
---

# /looper — Issue-Driven Resilient Executor

Implement GitHub issues into PRs with dependency ordering, quality gate retry loops, and checkpoint/resume. The name captures both loops: the **outer loop** (issue by issue in dependency order) and the **inner loop** (retry on gate failure).

## Input

Parse the provided arguments: `$ARGUMENTS`

### Issue Selectors

```
/looper 42                           # Single issue
/looper #42                          # Single issue with hash
/looper 42 43 44                     # Multiple issues (space-separated)
/looper 42,43,44                     # Multiple issues (comma-separated)
/looper 42-48                        # Inclusive range
/looper --label roadmap              # All open issues with label
/looper --milestone "Phase 1"        # All open issues in milestone
```

### Flags

```
--combined          Single PR for all issues (default: separate PRs)
--resume            Resume from .claude/looper-state.md
--preview           Show execution plan, don't run
--max-retries N     Retry attempts per issue (default: 3)
--constraints "..." Freeform constraints, plus skip:<cmd> / gate:<cmd> syntax
--contract <path>   Load acceptance contract for criteria verification
```

### Constraint Syntax

The `--constraints` value is freeform text passed as context during implementation. Two special prefixes modify gate behavior:

- `skip:<cmd>` — skip the named gate (e.g. `skip:lint` removes the lint gate)
- `gate:<cmd>` — add a custom gate command (e.g. `gate:npm run e2e`)

## Git Safety Context

All work in this skill happens on **feature branches** that get submitted as **pull requests** back to main. No changes are ever made directly on main. This means all git operations (branch creation, commits, pushes, PR creation) are safe, reversible workflow steps — the user reviews and merges via the PR. Proceed with git and gh commands without additional confirmation.

---

## Phase A: INTAKE

### Step 1: Parse Arguments

Extract from `$ARGUMENTS`:
- Issue numbers (handling all formats: `42`, `#42`, `42 43 44`, `42,43,44`, `42-48`)
- `--label <label>` — fetch open issues by label
- `--milestone <name>` — fetch open issues by milestone
- `--combined` flag
- `--resume` flag
- `--preview` flag
- `--max-retries N` (default: 3)
- `--constraints "..."` text
- `--contract <path>` (if present, load acceptance contract for criteria mapping)

### Step 2: Resolve Issues

If `--resume` is set, skip to **Phase B, Step 5 (Resume)**.

Fetch issue details:

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
4. If any issues remain after queue is empty → **cycle detected** — report the cycle and remove those issues from the queue with a warning

Issues with external-open blockers are placed at the end with status `blocked`.

---

## Phase B: PLANNING

### Step 4: Auto-Detect Quality Gates

Detect workspace and project stack:

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
```

Auto-detect gates in order: **build → typecheck → lint → test**

| Stack | Detection | Gates |
|-------|-----------|-------|
| **Node.js** | `package.json` exists | `npm run build` (if scripts.build), `npx tsc --noEmit` (if scripts.typecheck or tsconfig.json), `npm run lint` (if scripts.lint), `npm test` (if scripts.test) |
| **Python** | `pyproject.toml` exists | `ruff check .`, `ruff format --check .`, `pytest`, `mypy .` (if mypy in deps) |
| **Go** | `go.mod` exists | `go build ./...`, `go vet ./...`, `go test ./...` |
| **Rust** | `Cargo.toml` exists | `cargo build`, `cargo clippy -- -D warnings`, `cargo test` |

**Node.js commands** must be wrapped per CLAUDE.md:
```bash
source ~/.nvm/nvm.sh && nvm use default --silent && <cmd>
```

Apply constraint modifiers:
- `skip:<name>` removes any gate whose command contains that name (e.g. `skip:lint` removes the lint gate)
- `gate:<cmd>` appends a custom gate command

Verify each gate command actually works by running it once. If a gate command fails with "command not found" or similar, remove it and warn.

### Step 5: Initialize or Resume State File

**State file location:** `$WORKSPACE/.claude/looper-state.md`

#### New Run — Create State File

```bash
mkdir -p $WORKSPACE/.claude
```

Write state file with this structure:

```markdown
---
active: true
phase: "planning"
mode: "separate"  # or "combined"
created_at: "YYYY-MM-DDTHH:MM:SS"
updated_at: "YYYY-MM-DDTHH:MM:SS"
max_retries: 3
constraints: "<constraints text>"
---

## Issue Queue

Execution order (topological sort):

| # | Issue | Title | Status | Blocked By |
|---|-------|-------|--------|------------|
| 1 | #42 | Security gate | pending | — |
| 2 | #43 | Coverage gate | pending | #42 |
| 3 | #44 | Audit gate | pending | — |
| 4 | #45 | Dashboard | blocked | #99 (external-open) |

## Quality Gates

| Gate | Command | Status |
|------|---------|--------|
| build | `npm run build` | pending |
| typecheck | `npx tsc --noEmit` | pending |
| lint | `npm run lint` | pending |
| test | `npm test` | pending |

## Progress

(populated during execution)

## Decisions Log

(populated during execution)

## PRs Created

| Issue | PR | Branch | Title |
|-------|-----|--------|-------|
(populated during execution)
```

#### Resume — Read Existing State File

Read `$WORKSPACE/.claude/looper-state.md`. Parse:
- Which issues are `completed`, `failed`, `pending`, `blocked`, `in_progress`
- Quality gate commands
- Previous decisions and failed approaches
- Resume from the first `pending` or `in_progress` issue

Update `updated_at` timestamp and set `active: true`.

#### Preview Mode

If `--preview` is set: display the state file contents (issue queue, dependency graph, quality gates) and **stop**. Do not proceed to execution.

---

## Phase C: EXECUTION LOOP

Process each issue in topological order. For each issue:

### Step 6a: Verify Blockers Resolved

Before starting an issue, re-check all its in-batch blockers:
- If a blocker is `completed` → satisfied
- If a blocker is `failed` → skip this issue (mark as `blocked-by-failure`), log reason
- If a blocker is still `pending` → this shouldn't happen in topo order, but if it does, skip

For external dependencies, re-check via `gh issue view`:
- If now closed → satisfied
- If still open → skip this issue (mark as `blocked`)

### Step 6b: Create Feature Branch

Update state: mark issue as `in_progress`.

**Separate mode (default):**
```bash
git checkout main && git pull origin main
git checkout -b feat/$ISSUE_NUMBER-$(echo "$TITLE" | tr ' ' '-' | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9-]//g' | cut -c1-40)
```

**Combined mode:**
On first issue, create the combined branch:
```bash
git checkout main && git pull origin main
git checkout -b feat/$FIRST-$LAST-combined
```
On subsequent issues, stay on the combined branch.

### Step 6c: Implement the Issue

Read the full issue body via `gh issue view $N --json body -q .body`.

Implement the requirements:
- Follow existing code patterns and conventions
- Write tests if the project has tests
- Reference the issue number in code comments only where clarifying

If `--constraints` were provided, follow them as additional implementation context.

### Step 6d: Run Quality Gates

Run ALL gate commands in order. Capture output for each:

```bash
# Example for Node.js
source ~/.nvm/nvm.sh && nvm use default --silent && npm run build
source ~/.nvm/nvm.sh && nvm use default --silent && npx tsc --noEmit
source ~/.nvm/nvm.sh && nvm use default --silent && npm run lint
source ~/.nvm/nvm.sh && nvm use default --silent && npm test
```

Record results in state file under the issue's Progress entry.

### Step 6e: Retry on Gate Failure

If ANY gate fails:

1. Log the failure in the state file under the issue's entry:
   ```markdown
   ### Issue #42: Security gate
   **Attempt 1** — FAILED
   - Gate: `npm run lint`
   - Error: <first 50 lines of error output>
   - Approach: <what was tried>
   ```

2. If attempts < max_retries:
   - Read the failed approach log and gate error output
   - Make a **targeted fix** (do not rewrite from scratch)
   - Re-run **ALL** gates (a fix for one gate may break another)
   - Increment attempt counter

3. If attempts >= max_retries:
   - Mark issue as `failed` in state
   - **Separate mode:** abandon the branch (`git checkout main`)
   - **Combined mode:** revert commits for this issue (`git revert` the commits made for this issue)
   - Log final failure reason
   - Continue to next issue — failed issues don't block unrelated issues (only issues that explicitly depend on this one are blocked)

### Step 6f: Gate Pass — Commit, Push, Create PR

When all gates pass:

**Contract Verification (if `--contract` loaded):**

1. Read the acceptance contract file
2. Map current issue to contract criteria via `US-NNN` identifiers in the issue body
3. For each mapped criterion: check if the associated test passes, update contract status
4. If any mapped criterion is `pending` or `failed`: treat as a gate failure → enter retry loop (Step 6e)
5. Update contract file with evidence for verified criteria

**Commit:**
```bash
git add <changed-files>
git commit -m "feat: $(echo $TITLE | tr '[:upper:]' '[:lower:]')

Implements #$ISSUE_NUMBER"
```

**Separate mode — push and create PR immediately:**
```bash
git push -u origin HEAD

gh pr create \
  --title "feat: $(gh issue view $N --json title -q .title)" \
  --body "## Summary
Implements #$N.

## Changes
$(git diff main --stat)

## Quality Gates
All passing:
$(for gate in "${GATES[@]}"; do echo "- \`$gate\` ✓"; done)

## Retry Stats
Attempts: $ATTEMPTS/$MAX_RETRIES

## Acceptance Criteria
$(if [ -n "$CONTRACT_PATH" ]; then echo "Contract: $CONTRACT_PATH"; grep -A2 "^| AC-" "$CONTRACT_PATH" | head -20; fi)

Closes #$N"
```

**Combined mode — commit but defer PR to Phase D.**

After creating the PR (separate mode), record it in state.

### Step 6g: Checkpoint State

After each issue (pass or fail), update the state file:
- Update issue status (`completed`, `failed`, `blocked-by-failure`)
- Record branch name, PR number (if created), attempt count, gate results
- Update `updated_at` timestamp
- Update the Progress section with details

This checkpoint enables `--resume` if the session is interrupted.

---

## Phase D: REPORTING

### Combined Mode — Create Single PR

If `--combined` mode and at least one issue was completed:

```bash
git push -u origin HEAD

gh pr create \
  --title "feat: implement issues $(echo $COMPLETED_ISSUES | tr ' ' ', ')" \
  --body "## Summary
Implements multiple issues in a single PR.

## Issues Addressed
$(for N in $COMPLETED_ISSUES; do echo "- #$N: $(gh issue view $N --json title -q .title)"; done)

## Changes
$(git diff main --stat)

## Quality Gates
All passing:
$(for gate in "${GATES[@]}"; do echo "- \`$gate\` ✓"; done)

$(for N in $COMPLETED_ISSUES; do echo "Closes #$N"; done)"
```

### Step 7: Per-Issue Progress (displayed after each PR)

After each PR is created (or issue is skipped/failed), display:

```
Progress: 2/5 completed | 0 failed | 3 remaining

Completed:
  #42 → PR #101 (1 attempt)
  #43 → PR #102 (2 attempts)

Remaining:
  #44 — pending
  #45 — blocked by #99 (external-open)
  #46 — pending
```

### Step 8: Final Summary

After all issues are processed:

```
Looper Complete

  Issues: 4/5 completed, 1 blocked
  PRs created: 4
  Total attempts: 7 (across all issues)
  Quality gates: build ✓ | typecheck ✓ | lint ✓ | test ✓
  Contract: $(if [ -n "$CONTRACT_PATH" ]; then echo "N/M criteria verified"; else echo "none"; fi)

  PRs:
  | Issue | PR   | Title              | Attempts |
  |-------|------|--------------------|----------|
  | #42   | #101 | Security gate      | 1        |
  | #43   | #102 | Coverage gate      | 2        |
  | #44   | #103 | Audit gate         | 1        |
  | #46   | #104 | Notification gate  | 3        |

  Blocked:
  | Issue | Reason                        |
  |-------|-------------------------------|
  | #45   | Blocked by #99 (external-open)|

  State: .claude/looper-state.md
```

Update state file: `active: false`, `phase: "complete"`.

---

## Important Rules

1. **Always reference issues** in commits and PR body using `#N` syntax
2. **Use `Closes #N`** in PR body to auto-close issues on merge
3. **Run ALL gates on every attempt** — a fix for one gate may break another
4. **Feed failure context forward** — on retry, read previous failure logs to avoid repeating mistakes
5. **Never skip the inner loop** — if gates fail, retry before moving on
6. **Respect dependency order** — never implement an issue before its blockers are resolved
7. **Checkpoint after every issue** — enable resume on interruption
8. **Failed issues don't block unrelated issues** — only issues with explicit dependency markers are affected
9. **Follow existing patterns** — match code style, file organization, naming conventions of the project
10. **Node.js commands** must be wrapped: `source ~/.nvm/nvm.sh && nvm use default --silent && <cmd>`
