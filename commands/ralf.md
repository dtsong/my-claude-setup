---
description: "Start an autonomous execution loop with PRD-based planning"
argument-hint: "[--preview] [--skip-planning] [--from-prd <file>] [--resume <checkpoint>] [--constraints \"...\"] [GOAL...]"
---

# /ralf - PRD-Based Autonomous Task Execution

Start an autonomous Claude session that works on a goal through a PRD-based 3-phase workflow until completion.

## PRD-Based 3-Phase Workflow

```
/ralf "goal"
    │
    ▼
┌─────────────────┐
│ PRD PLANNING    │  ← Generate PRD with quality gates + user stories
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ EXECUTION       │  ← Implement user stories from PRD
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ VERIFICATION    │  ← Check quality gates + acceptance criteria
└─────────────────┘
```

## Key Features

| Feature | Description |
|---------|-------------|
| **PRD-Based Planning** | Generates proper PRD with quality gates + user stories |
| **Quality Gates** | Build, lint, type-check, and test commands that must pass |
| **User Stories** | Acceptance criteria from PRD drive verification |
| **Checkpoints** | Recovery points for long-running tasks |
| **State Tracking** | Progress persisted in `.claude/ralf-state.md` |

## Instructions

### Step 1: Parse Arguments

Parse the provided arguments: `$ARGUMENTS`

Extract:
- `--preview` flag (if present, show plan without executing)
- `--skip-planning` flag (if present, skip planning phase)
- `--from-prd <file>` (if present, use existing PRD)
- `--resume <checkpoint>` (if present, resume from checkpoint file)
- `--constraints "..."` (optional constraints text)
- Remaining text = the GOAL

### Workspace Detection

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
```

### Step 2: Gather Information (Interactive Wizard)

If NO GOAL was provided in arguments (and no --resume or --from-prd), use AskUserQuestion to gather:

1. **Goal Question**: "What's the goal you want to achieve?"

2. **PRD Question**: "Do you have an existing PRD?"
   - Options: "No - generate one (Recommended)", "Yes - I have a PRD file"

3. **Constraints Question**: "Any specific constraints or requirements?" (optional)

### Step 3: Detect Quality Gates

Auto-detect quality gate commands from the project:

```bash
# Read package.json scripts (Node.js)
if [ -f "$WORKSPACE/package.json" ]; then
    # Check for: build, typecheck/tsc, lint, test
    HAS_BUILD=$(jq -r '.scripts.build // empty' "$WORKSPACE/package.json")
    HAS_TYPECHECK=$(jq -r '.scripts.typecheck // .scripts["type-check"] // empty' "$WORKSPACE/package.json")
    HAS_LINT=$(jq -r '.scripts.lint // empty' "$WORKSPACE/package.json")
    HAS_TEST=$(jq -r '.scripts.test // empty' "$WORKSPACE/package.json")
fi

# Python projects
if [ -f "$WORKSPACE/pyproject.toml" ]; then
    # Check for ruff, pytest, mypy
fi
```

### Step 4: PRD Planning Phase

If `--from-prd` was provided, read that file. Otherwise, generate a PRD:

```bash
mkdir -p $WORKSPACE/.claude/prd
```

Generate PRD with this structure:

```markdown
# PRD: <Goal>

## Overview
<1-2 paragraph description>

## Goals
- <Goal 1>
- <Goal 2>

## Non-Goals
- <What's explicitly out of scope>

## Quality Gates

These commands must pass for ALL stories:
- `npm run build` — Build passes
- `npx tsc --noEmit` — Type checking (if applicable)
- `npm run lint` — Linting (if applicable)
- `npm test` — Tests pass (if applicable)

## User Stories

### US-001: <Story title>
**Description:** As a <user>, I want <capability> so that <benefit>.

**Acceptance Criteria:**
- [ ] <Criterion 1>
- [ ] <Criterion 2>

### US-002: ...
(continue for all stories)
```

Save to `$WORKSPACE/.claude/prd/prd-<slug>.md`.

**If `--preview`**: Show the PRD and stop. Do not execute.

Present the PRD to the user via AskUserQuestion:
- **Approve and execute** — Proceed to execution
- **Edit PRD** — Let the user modify before continuing
- **Cancel** — Stop

### Step 5: Initialize State

Create state file at `$WORKSPACE/.claude/ralf-state.md`:

```markdown
---
active: true
phase: "executing"
iteration: 1
prd_file: ".claude/prd/prd-<slug>.md"
---

## Goal
<goal>

## Quality Gates
- [ ] `npm run build` passes
- [ ] `npx tsc --noEmit` passes
(auto-detected gates)

## User Stories Progress
### US-001: <title>
- [ ] <criterion>
(from PRD)

## Decisions Made
(populated during execution)

## Failed Approaches
(populated during execution)
```

### Step 6: Execution Phase

Work through user stories from the PRD:

1. **Pick next uncompleted story** (in order)
2. **Implement** following acceptance criteria
3. **Document decisions** in state file under "Decisions Made"
4. **Document failures** in state file under "Failed Approaches"
5. **Mark criteria as done** `[x]` when verified
6. **Commit progress** after each story:
   ```bash
   git -C $WORKSPACE add <changed-files>
   git -C $WORKSPACE commit -m "<type>(<scope>): <description> [US-<NNN>]"
   ```
7. **Create checkpoint** after each story:
   - Update state file iteration count
   - Save current state

### Step 7: Verification Phase

After all stories are complete, run quality gates:

```bash
# Run each quality gate command
npm run build
npx tsc --noEmit
npm run lint
npm test
```

Check results:
- **ALL pass** → Mark state as complete, report success
- **ANY fail** → Document failure, return to execution phase to fix

### Step 8: Completion

When all quality gates pass and all acceptance criteria are met:

1. Update state file: `active: false`, `phase: "complete"`
2. Final commit with all changes
3. Report:

```
Ralf Loop Complete

  Goal: <goal>
  Stories: <N>/<N> completed
  Quality Gates: ALL PASSING
  Commits: <N> commits

  PRD: .claude/prd/prd-<slug>.md
  State: .claude/ralf-state.md
```

## Example Commands

```
/ralf                                        # Interactive wizard
/ralf "Add dark mode toggle"                 # Starts with PRD planning
/ralf --preview "Build REST API"             # Preview PRD without executing
/ralf --skip-planning "Fix typo"             # Skip PRD, direct execution
/ralf --from-prd ./tasks/prd-feature.md      # Use existing PRD
/ralf --resume .claude/ralf-state.md         # Resume from state file
/ralf --constraints "No new deps" "Add caching"
```

## Integration with /council

The `/council` command can hand off its PRD to `/ralf`:
```
/ralf --from-prd .claude/prd/prd-<slug>.md
```

This allows council deliberation to produce the design, and ralf to execute it autonomously.
