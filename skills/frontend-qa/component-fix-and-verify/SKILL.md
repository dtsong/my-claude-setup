---
name: component-fix-and-verify
description: >
  Use when a diagnosed fix needs to be applied and verified against a Next.js
  component — "apply this fix," "fix and run tests," or "verify this change."
  Applies a single diagnosed fix with mandatory diff preview, then runs scoped
  and broad verification (tsc, lint, tests) with atomic safety and revert
  capability. Not for diagnosing bugs (use ui-bug-investigator or
  css-layout-debugger) or generating regression tests (use
  regression-test-generator).
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
---

# Component Fix and Verify

Apply a diagnosed fix to a component and verify through scoped then broad checks with mandatory diff preview and atomic safety.

## Scope Constraints

- Read access to source files, config files, and git state
- Write access to files listed in `affectedFiles` from the DiagnosisReport only
- Executes `tsc`, linter, and test runner commands — no other shell commands
- Does not modify files outside the diagnosed fix scope
- Revert restores original file contents only for files changed by this skill

## Inputs

- **DiagnosisReport** (required): Path to `.claude/qa-cache/artifacts/diag-*.json` with `rootCause` and `suggestedFix`
- **ComponentMap** (required): Path to `.claude/qa-cache/component-maps/{route-slug}.json`
- **FixResult from prior run** (optional): If retrying after a FAIL verdict

## Input Sanitization

- File paths from DiagnosisReport `affectedFiles` are validated against the ComponentMap's `cachedFiles` array. Reject any path not present in the ComponentMap or containing `..`, shell metacharacters, or absolute paths outside the project root.
- Shell commands are constructed from detected tool names (`tsc`, `eslint`, `biome`, `vitest`, `jest`, `playwright`) with file arguments. No user-provided strings are interpolated into commands.

## Procedure

Copy this checklist and update as you complete each step:
```
Progress:
- [ ] Phase 1: Pre-flight (Steps 1-4)
- [ ] Phase 2: Preview (Steps 5-7)
- [ ] Phase 3: Apply (Steps 8-9)
- [ ] Phase 4: Scoped Verification (Steps 10-12)
- [ ] Phase 5: Broad Verification (Steps 13-15)
- [ ] Phase 6: Verdict (Step 16)
```

Note: If you've lost context of previous steps (e.g., after context compaction), check the progress checklist above. Resume from the last unchecked item. Re-read the verification-commands reference if needed.

### Phase 1: Pre-flight

1. Run `git status --short`. If untracked or modified files exist outside the fix scope, warn: "Working tree has uncommitted changes in: [files]. These are unrelated to this fix." Pause for acknowledgment.
2. If no git repo, warn: "No git repository — revert will require manual undo." Pause.
3. Identify the files to change from the DiagnosisReport. Record them as `affectedFiles`.
4. Capture baseline state: run `tsc --noEmit 2>&1 | tail -5` and record pre-existing error count. Note: "Baseline: N pre-existing type errors."

### Phase 2: Preview

5. Generate the complete fix as a unified diff. Show it with a plain-language explanation:
   - What changes and why (1-2 sentences per file)
   - **What this does NOT address** — related issues the fix intentionally leaves untouched
   - Risk level: **Low** (style/typo), **Medium** (logic change), or **High** (architectural change, cross-file)
6. Pause: "Review the diff above. Apply this fix?"
7. Do NOT write any file until the user confirms.

### Phase 3: Apply

8. Write the changes to disk. One fix at a time — never batch multiple independent fixes.
9. Record exactly what was written for revert reference.

### Phase 4: Scoped Verification

10. Read `references/verification-commands.md`. Run scoped checks on `affectedFiles` only:
    - **TypeScript**: `tsc --noEmit` on affected files (see reference for project-specific variants)
    - **Lint**: detected linter on affected files (ESLint, Biome, or project lint script)
    - **Tests**: related tests only (`vitest --related`, `jest --findRelatedTests`, or directory-scoped)
11. If test runner is not detected or test command fails to start, report: "No test infrastructure detected. Verification limited to tsc + lint." Mark tests as SKIPPED.
12. If any scoped check fails, skip Phase 5. Go directly to Phase 6 with FAIL.

### Phase 5: Broad Verification

13. Run full-project `tsc --noEmit`. Compare error count to Phase 1 baseline.
14. Run full test suite via the project's test script (`npm test`, `pnpm test`, etc.).
15. If broad checks introduce new failures beyond the Phase 1 baseline, go to Phase 6 with FAIL. If only pre-existing failures remain, go to Phase 6 with PARTIAL.

### Phase 6: Verdict

Report one of three outcomes:

**PASS** — All scoped and broad checks green.
```
Fix verified: PASS
  tsc: 0 errors (was N baseline)
  lint: clean
  tests: M passed, 0 failed
  scope: [affectedFiles]
```

**FAIL** — Any check introduced new errors. Do NOT auto-revert. Show:
```
Fix verified: FAIL
  failed phase: [Scoped Verification | Broad Verification]
  failing check: [tsc | lint | tests]
  error: [first error message]
  files changed: [affectedFiles]

Options:
  1. Show full error output
  2. Revert this fix (restores original files)
  3. Keep changes and investigate
```

**PARTIAL** — Fix is clean but pre-existing failures exist in broad checks.
```
Fix verified: PARTIAL
  scoped checks: all passed
  broad checks: pre-existing failures detected (not caused by this fix)
  pre-existing: N type errors, M test failures (same as baseline)
  scope: [affectedFiles]
```

16. If user chooses revert on FAIL: restore the original file contents recorded in Phase 3, then confirm: "Reverted [N] files. Working tree matches pre-fix state."

## Visual Triage (When Screenshots Provided)

If the DiagnosisReport includes before/after screenshots:

**Tier 1 — Qualitative** (always available): Examine both screenshots cross-referenced with the code changes. Report observations with mandatory disclaimers:
- "Visual analysis is qualitative, not pixel-accurate"
- "Sub-pixel differences require dedicated tooling"
- "Dynamic states (hover, animation) cannot be assessed from static screenshots"
- Never state "no visual differences" as a pass — say "no differences observed in static comparison"

**Tier 2 — Automated** (if tooling detected): Check for Playwright with `toHaveScreenshot()` or pixelmatch in dependencies. If found, scaffold the comparison command and run it. If not found, note: "Automated visual regression available with Playwright — see playwright.dev/docs/test-snapshots." Proceed with Tier 1 only.

## Output Format

```yaml
FixResult:
  version: "1.0"
  diagnosis_ref: "[DiagnosisReport ID]"
  affectedFiles: ["path/to/file.tsx"]
  diff: "[unified diff string]"
  verdict: "PASS | FAIL | PARTIAL"
  checks:
    tsc: { status: "pass|fail|skip", errors: 0, baseline: 0 }
    lint: { status: "pass|fail|skip", tool: "eslint|biome|none" }
    tests: { status: "pass|fail|skip", passed: 0, failed: 0, runner: "vitest|jest|none" }
  visual: { tier: "1|2|none", observations: "string" }
  notAddressed: ["related issue this fix does not cover"]
  reverted: false
```

## Handoff

Pass the FixResult artifact path to qa-coordinator. The result contains `verdict`, `affectedFiles`, `diff`, and `notAddressed` fields consumed by `regression-test-generator`.

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/verification-commands.md` | Phase 4, always | TypeScript, linter, and test runner detection and invocation commands |
