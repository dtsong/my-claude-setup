---
name: qa-coordinator
description: >
  Use when a user reports a frontend bug, visual defect, or unexpected behavior
  in a Next.js/TypeScript application. Orchestrates a multi-phase QA pipeline —
  component mapping, diagnosis, fix, and regression testing — by classifying
  symptoms and dispatching to the appropriate specialist skill. Does not perform
  diagnosis or fixes directly; delegates all domain work to specialists. Not for
  backend-only issues, infrastructure problems, or build/deployment failures.
model:
  preferred: haiku
  acceptable: [haiku, sonnet]
  minimum: haiku
  allow_downgrade: true
  reasoning_demand: low
---

# QA Coordinator

## Purpose

Classify frontend bug symptoms, dispatch to the appropriate specialist skill, and orchestrate the MAP → DIAGNOSE → FIX → TEST pipeline with user confirmation between phases.

## Scope Constraints

- Read-only access to `package.json`, `tsconfig.json`, and project config files for stack detection
- Write access limited to `.claude/qa-cache/project-config.json`
- Does not modify source code, test files, or run shell commands directly
- All file modifications and command execution delegated to specialist skills

## Classification

Extract **route** and **symptom** from user input. If ambiguous, ask one question.

Auto-detect the stack if no `.claude/qa-cache/project-config.json` exists: read `package.json`, detect framework/test/styling/state, check for app/ vs pages/, confirm with user, save config. Re-detect only when `package.json` changes.

| Symptom | Skill |
|---------|-------|
| Rendering, missing content, stale data, flicker | `ui-bug-investigator` |
| State not updating, form issues, toggle broken | `ui-bug-investigator` |
| Click/keyboard/focus broken, event issues | `ui-bug-investigator` |
| Data not loading, API errors, server actions | `ui-bug-investigator` |
| Hydration mismatch, RSC error, boundary issues | `ui-bug-investigator` |
| Layout broken, spacing, alignment, overflow | `css-layout-debugger` |
| Styling wrong, colors, dark mode, responsive | `css-layout-debugger` |
| Unclear/mixed | `ui-bug-investigator` first, then `css-layout-debugger` if styling root cause found |

## Skill Registry

| Skill | Path | Purpose | Model Tier |
|-------|------|---------|------------|
| Mapper | `page-component-mapper/SKILL.md` | Map route to component tree | haiku  |
| UI Investigator | `ui-bug-investigator/SKILL.md` | Diagnose non-CSS UI bugs | sonnet |
| CSS Debugger | `css-layout-debugger/SKILL.md` | Diagnose CSS/layout/styling issues | sonnet |
| Fix & Verify | `component-fix-and-verify/SKILL.md` | Apply and verify diagnosed fix | sonnet |
| Test Generator | `regression-test-generator/SKILL.md` | Generate targeted regression test | sonnet |

## Load Directive

Read ONLY the relevant specialist SKILL.md for the current phase. Never load multiple specialists simultaneously. Route silently — never present a skill menu.

## Handoff Protocol

Sequential four-phase pipeline. Pause for user confirmation between each phase.

**MAP** → Read `page-component-mapper/SKILL.md`. Output: `ComponentMap` artifact at .claude/qa-cache/component-maps/. Pause: "{N} components mapped. Continue?"

**DIAGNOSE** → Read classified specialist SKILL.md. Input: ComponentMap path + symptom + classification. Output: `DiagnosisReport` artifact. Pause: "Root cause: {description} in {file}:{line}. Proceed with fix?"

**FIX** → Read `component-fix-and-verify/SKILL.md`. Input: DiagnosisReport + ComponentMap paths. Output: `FixResult` artifact. Pause: "{PASS/FAIL/PARTIAL}. Generate regression test?"

**TEST** → Read `regression-test-generator/SKILL.md`. Input: FixResult + DiagnosisReport + ComponentMap paths. Output: `RegressionTest` artifact. "Test written. Investigation complete."

If user declines at any pause, stop and summarize findings so far.
