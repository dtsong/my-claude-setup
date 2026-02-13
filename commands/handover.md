---
description: "Save session knowledge — decisions, pitfalls, and next steps — for the next Claude session"
argument-hint: "[--help] [--tag LABEL]"
---

# /handover — Session Knowledge Transfer

Capture everything the next Claude session needs to hit the ground running: what was done, why, what went wrong, and what's next.

## Help Flag

If the argument is `--help`, show a brief usage summary and exit:
```
/handover [--help] [--tag LABEL]
Save session knowledge — decisions, pitfalls, and next steps — for the next Claude session
```
Then say: `Run /help handover for full details.`

## Usage

```
/handover
/handover --tag auth-refactor
```

## Instructions

When the user runs `/handover`, follow these steps:

### 1. Parse Arguments

- `--tag <label>`: Optional thematic label to include in the document header
- If `$ARGUMENTS` contains `--tag`, extract the label that follows it

### 2. Determine Output Path

```bash
WORKSPACE="$(git rev-parse --show-toplevel 2>/dev/null || echo "$PWD")"
TIMESTAMP="$(date +%Y-%m-%d-%H%M)"
mkdir -p "$WORKSPACE/memory"
OUTFILE="$WORKSPACE/memory/HANDOVER-${TIMESTAMP}.md"
```

### 3. Gather Session Context

Collect the following from the current environment:

```bash
BRANCH="$(git -C "$WORKSPACE" branch --show-current 2>/dev/null || echo 'unknown')"
RECENT_COMMITS="$(git -C "$WORKSPACE" log --oneline -5 2>/dev/null || echo 'none')"
```

### 4. Reflect and Write the Handover Document

You have full conversation context. Reflect on the entire session and write a comprehensive handover document to `$OUTFILE` using the Write tool.

**Target length: 80-120 lines.**

Use this template:

```markdown
# Session Handover — YYYY-MM-DD HH:MM
<!-- Tag: <label if provided> -->

## Session Summary
<!-- 2-3 sentences: what was the goal, what was achieved -->

## What Was Done
<!-- Bulleted list of concrete changes made -->
- ...

## Key Decisions Made
<!-- The most valuable section — capture WHY, not just WHAT -->
- **Decision**: <what was decided>
  - **Context**: <why this came up>
  - **Rationale**: <why this option was chosen over alternatives>

## Pitfalls & Gotchas
<!-- Errors hit, dead ends explored, workarounds applied -->
- ...

## Open Questions
<!-- Unresolved items, things that need more research or user input -->
- ...

## Next Steps
<!-- Ordered priority list of what to do next -->
1. ...
2. ...

## Important Files
<!-- Table of key files touched or referenced -->
| File | Role |
|------|------|
| ... | ... |

## Session Context
- **Branch**: <branch name>
- **Recent commits**:
  - <last 5 one-liners>
```

### 5. Confirm to User

After writing the file, tell the user:

```
Handover saved: memory/HANDOVER-<timestamp>.md
```

And give a 1-sentence summary of what was captured.

### Important Rules

- Write a REAL reflection of the session — do not produce a blank template
- Every section should have substantive content based on what actually happened
- The "Key Decisions Made" section is the most valuable — spend extra effort here
- If a section genuinely has nothing (e.g., no open questions), write "None" rather than inventing content
- Do NOT ask the user what to include — you already have the full context, just write it
- If the session was trivial (e.g., only a greeting), say so and skip the handover
