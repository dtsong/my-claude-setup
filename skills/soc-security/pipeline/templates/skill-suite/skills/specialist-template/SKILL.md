---
name: SPECIALIST_NAME
description: >
  SPECIALIST_TRIGGER. Use when SPECIALIST_CONTEXT.
---

# SPECIALIST_NAME

## Inputs
- `required_input`: DESCRIPTION
- `optional_input` (optional): DESCRIPTION

## Procedure

Step 1: Gather context.
  - Read RELEVANT_FILES
  - Record constraints

Step 2: PRIMARY_ACTION.
  - IMPERATIVE_INSTRUCTION
  - If CONDITION → BRANCH_A. Otherwise → BRANCH_B.

Step 3: Verify output.
  - Check each item in the Output Contract
  - If any check fails → fix and re-verify

## Output Format

```json
{
  "result": "EXAMPLE_VALUE",
  "confidence": "high|medium|low"
}
```

## Handoff
Return structured JSON to coordinator. Include findings, confidence, and recommended next specialist (if any).

## References
| File | Load When | Contains |
|------|-----------|----------|
| `references/CHECKLIST.md` | Step 2 if CONDITION | Detailed checklist |
