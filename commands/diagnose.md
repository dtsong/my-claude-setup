---
name: diagnose
description: Diagnose a UI or CSS bug against an existing component map
---

# /diagnose

Run targeted diagnosis against an existing component map. Routes to ui-bug-investigator (rendering, state, data flow, events) or css-layout-debugger (styling, layout, responsive) based on symptom.

## Usage

```
/diagnose "The sidebar overlaps on mobile"
/diagnose "Click on the submit button does nothing"
/diagnose "Data is stale after form submission"
```

## Prerequisite

A component map must exist in `.claude/qa-cache/component-maps/`. If not, the coordinator runs the mapper first.

## Output

A DiagnosisReport with FLAGGED findings (file:line + evidence), CLEAR items, SKIPPED categories, and a scope-aware summary line. Saved to `.claude/qa-cache/artifacts/`.
