---
name: fix
description: Apply and verify a fix from an existing diagnosis, then generate a regression test
---

# /fix

Apply a proposed fix from a DiagnosisReport, run the 5-phase verification pipeline, and optionally generate a regression test.

## Usage

```
/fix
/fix "Apply the responsive breakpoint fix for Sidebar"
```

## Prerequisite

A DiagnosisReport must exist in `.claude/qa-cache/artifacts/`. If not, the coordinator runs diagnosis first.

## What Happens

1. **Pre-flight**: Checks `git status`, warns on dirty working tree
2. **Preview**: Shows full diff + "what this does NOT address" + risk level. Waits for approval.
3. **Apply**: Writes the fix (one file change at a time)
4. **Verify**: Scoped (`tsc --noEmit`, lint, related tests), then broad (full tsc, full test suite)
5. **Verdict**: PASS / FAIL / PARTIAL

On FAIL: presents options (revert, investigate, try alternative). No automatic revert.

After a passing fix, offers to generate a regression test via regression-test-generator.
