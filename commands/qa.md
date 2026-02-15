---
name: qa
description: Run the full frontend QA pipeline -- describe a bug and the coordinator maps, diagnoses, fixes, and tests
---

# /qa

Run the complete frontend QA pipeline from bug report through regression test. The coordinator handles everything: auto-detects your stack, maps the component tree, dispatches to the right diagnostic skill, applies and verifies fixes, and generates regression tests -- pausing for your confirmation at each step.

## Usage

```
/qa
/qa "The /dashboard sidebar overlaps the main content on mobile"
/qa "Blank screen on /settings/billing after deploying"
```

## What Happens

1. **Stack detection** (first run only): Detects Next.js version, styling, test framework, component libraries. Confirms with you.
2. **Component mapping**: Traces the route's component tree. Shows project components with file paths. You confirm the scope.
3. **Diagnosis**: Routes to ui-bug-investigator or css-layout-debugger based on symptom. Shows FLAGGED/CLEAR/SKIPPED findings. You confirm the diagnosis.
4. **Fix**: Shows proposed diff + risk assessment. You approve before any file is modified. Runs scoped verification.
5. **Regression test**: Generates a test following your project's conventions. You approve before the file is written.

You can stop at any checkpoint and resume later. Each phase's artifact is saved to `.claude/qa-cache/`.

## When to Use /qa vs. Individual Commands

| Situation | Use |
|-----------|-----|
| Full investigation from bug to test | `/qa` |
| Just need to see the component tree | `/map` |
| Already have a map, need diagnosis | `/diagnose` |
| Already have a diagnosis, need fix | `/fix` |
