---
name: ui-bug-investigator
description: >
  Use when a user reports a non-CSS UI bug in a Next.js App Router application —
  "blank page," "data not loading," "click does nothing," "hydration mismatch,"
  "flicker on navigation," or "state not updating." Runs symptom-targeted
  diagnostic checks against a component map to identify rendering, state, event
  handling, and data flow issues. Not for CSS layout, styling, or visual design
  problems — route those to css-layout-debugger.
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
---

# UI Bug Investigator

Diagnose non-CSS UI bugs by running symptom-targeted checks against the component map. Produce a DiagnosisReport with FLAGGED/CLEAR/SKIPPED findings.

## Scope Constraints

- Read-only access to source files in the component tree
- Write access limited to `.claude/qa-cache/artifacts/` for DiagnosisReport persistence
- Does not modify source code or run shell commands
- Investigates only components within the ComponentMap — stops at library boundaries (`@radix-ui`, `shadcn/ui`, `@mui`, etc.)

## Inputs

- **ComponentMap** (required): Path to `.claude/qa-cache/component-maps/{route-slug}.json`
- **Symptom description** (required): User-reported bug description
- **Classification** (required): Category from qa-coordinator (rendering, state, event, data-flow, hydration)
- **Screenshot** (optional): Visual evidence of the issue

## Procedure

Copy this checklist and update as you complete each step:
```
Progress:
- [ ] Step 1: Consume Component Map
- [ ] Step 2: Classify Symptom
- [ ] Step 3: Identify Target Components
- [ ] Step 4: Run Checks
- [ ] Step 5: Assess Confidence
- [ ] Step 6: Output DiagnosisReport
- [ ] Step 7: Persist Artifact
```

Note: If you've lost context of previous steps (e.g., after context compaction), check the progress checklist above. Resume from the last unchecked item. Re-read relevant reference files if needed.

### Step 1: Consume Component Map

Read the ComponentMap artifact from `.claude/qa-cache/component-maps/`.

Check `completeness`:
- If `"partial"` or `"shallow"`: warn the user — "Component map is **{completeness}** ({N} unresolved imports). Diagnosis may miss components behind unresolved imports. Run `--depth N` on the mapper for deeper tracing."
- If `"full"`: proceed silently.

### Step 2: Classify Symptom

Map the user's reported symptom to one or more diagnostic categories:

| Symptom Signal | Primary Category | Reference to Load |
|----------------|-----------------|-------------------|
| Blank/missing content, wrong content shown, flicker on load, content appears then disappears | Rendering & State | `references/rendering-state-checks.md` |
| Click/tap does nothing, wrong handler fires, keyboard nav broken, focus lost | Event Handling | `references/event-handling-checks.md` |
| Stale data, missing data, wrong data, loading never resolves, data appears in wrong component | Data Flow | `references/data-flow-checks.md` |
| Hydration mismatch warning in console | Rendering & State | `references/rendering-state-checks.md` |
| Component works in dev but not in production build | Data Flow + Rendering | Load both references sequentially |
| Unknown or ambiguous | All three | Load in order: rendering → data-flow → event-handling |

If the symptom clearly maps to a single category, load only that reference. Do not run all checks when one category is sufficient.

### Step 3: Identify Target Components

From the ComponentMap, select the components to investigate:

1. Start from the component closest to the reported symptom (the user named it, or it renders the broken UI area).
2. Walk up the tree to its parent (layout, wrapper).
3. Walk down to its direct children (data providers, conditional renderers).
4. Stop at library boundaries — do not investigate internals of `@radix-ui`, `shadcn/ui`, `@mui`, etc.

Target 3-8 components. If more than 8 are plausible, narrow by asking the user one question.

### Step 4: Run Checks

Read the reference file(s) identified in Step 2. For each target component, apply the relevant checklist items from the reference.

For each check:
- Read the component source file at the referenced path.
- Evaluate the check's condition against the actual code.
- Classify the result:
  - **FLAGGED** — Code matches the failure pattern. Record the file:line, the specific code, and why it matches.
  - **CLEAR** — Code was checked and does not match the failure pattern.
  - **SKIPPED** — Check does not apply to this component (e.g., event check on a server component). Record the reason.

Stop checking a component after the first FLAGGED item with High confidence. Continue checking other components.

### Step 5: Assess Confidence

For each FLAGGED finding, assign confidence:
- **High** — The code directly produces the reported symptom (e.g., missing key prop causes re-mount on every render, matching the user's "flicker" report).
- **Medium** — The code could produce the symptom but other causes are also plausible.
- **Low** — The code is suspicious but the connection to the symptom is indirect.

### Step 6: Output DiagnosisReport

Present findings in this order:

```
## Diagnosis: [symptom restated]

FLAGGED  [file:line] — [description]
  [2-3 sentence explanation]
  Evidence: [observation 1] | [observation 2] | [observation 3]

CLEAR  [ComponentName] ([file]) — [reason cleared]
CLEAR  [ComponentName] ([file]) — [reason cleared]

SKIPPED  [Category] — [reason]

Checked: [N] components ([categories]) | Not checked: [categories] | Confidence: [High/Medium/Low]
```

If multiple FLAGGED findings: list the highest-confidence one first. If no FLAGGED findings, output the inconclusive format:

```
## Diagnosis: Inconclusive

Investigated [N] components across [categories]. No root cause identified.

What might help:
- [specific ask 1]
- [specific ask 2]
- [specific ask 3]

Checked: [N] components ([categories]) | Not checked: [categories] | Confidence: --
```

### Step 7: Persist Artifact

Save the DiagnosisReport to `.claude/qa-cache/artifacts/diag-{timestamp}-{id}.json` with:
- `version`: `"1.0"`
- `skill`: `"ui-bug-investigator"`
- `issueClassification`: the category from Step 2
- `rootCause`: the highest-confidence FLAGGED finding (or null)
- `differentialDiagnosis`: all CLEAR items with their cleared reasons
- `suggestedFix`: a one-line description of what to change (consumed by component-fix-and-verify)

## Handoff

Pass the DiagnosisReport artifact path to qa-coordinator. The report contains structured `rootCause`, `differentialDiagnosis`, and `suggestedFix` fields consumed by `component-fix-and-verify`.

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/rendering-state-checks.md` | Symptom is rendering, state, or hydration | Checklist for boundary mismatches, key props, conditional rendering, hydration |
| `references/event-handling-checks.md` | Symptom is click/keyboard/focus issues | Checklist for handler attachment, propagation, focus management |
| `references/data-flow-checks.md` | Symptom is data loading, staleness, or missing data | Checklist for fetch patterns, caching, server actions, prop threading |
