---
name: regression-test-generator
description: >
  Use when a verified fix needs a regression test — "write a test for this fix,"
  "generate regression test," or "add test coverage for this bug." Auto-detects
  project test conventions, routes to Vitest+RTL or Playwright based on component
  type (sync vs async server), generates targeted tests with anti-brittleness
  constraints, and annotates coverage boundaries. Not for diagnosing bugs, applying
  fixes, or writing feature tests — use ui-bug-investigator, component-fix-and-verify,
  or manual test authoring respectively.
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
---

# Regression Test Generator

Generate a targeted regression test for a verified fix — auto-detect conventions, route to the correct test framework, annotate coverage boundaries.

## Scope Constraints

- Read access to source files, test files, and package configuration
- Write access limited to test file locations (colocated `__tests__/` or root `tests/` directory)
- Executes test runner commands (`vitest`, `jest`, `playwright`) — no other shell commands
- Does not modify source code or production files
- Creates one test file per invocation — never modifies existing test files

## Inputs

- **FixResult** (required): Path to FixResult artifact with `affectedFiles`, `diff`, `diagnosis_ref`, `notAddressed`
- **DiagnosisReport** (required): Path to DiagnosisReport artifact with `rootCause` and `issueClassification`
- **ComponentMap** (required): Path to ComponentMap artifact with component boundaries and metadata

## Input Sanitization

- Test file paths are constructed from detected conventions (Step 3) and the affected component's file path. Validate that the target directory exists and is within the project. Reject paths containing `..` or shell metacharacters.
- Test runner commands are constructed from detected framework names (`vitest`, `jest`, `playwright`) with the generated test file path. No user-provided strings are interpolated into commands.

## Procedure

Copy this checklist and update as you complete each step:
```
Progress:
- [ ] Step 1: Read the FixResult
- [ ] Step 2: Classify Component Type
- [ ] Step 3: Detect Project Conventions
- [ ] Step 4: Generate the Test
- [ ] Step 5: Place the Test File
- [ ] Step 6: Validate the Test
```

Note: If you've lost context of previous steps (e.g., after context compaction), check the progress checklist above. Resume from the last unchecked item. Re-read relevant reference files if needed.

### Step 1: Read the FixResult

Extract from the upstream FixResult:
- `affectedFiles` — the files that were changed
- `diff` — what changed (the fix)
- `diagnosis_ref` — the original bug description
- `notAddressed` — related issues not covered by the fix

### Step 2: Classify Component Type

Determine the routing target. This is a **hard rule**:

| Component type | Detected by | Route to |
|---|---|---|
| Sync client component | `"use client"` directive, uses hooks, event handlers | Vitest + RTL |
| Sync server component | No `"use client"`, no hooks, no `async` | Vitest + RTL |
| Async server component | `async function Component()`, `await` in body, `fetch()` / `cookies()` / `headers()` | **Playwright E2E** |
| Mixed (client wrapper around async server) | Both patterns present | Playwright E2E for the page, Vitest+RTL for the client wrapper |

If async server component → read `references/playwright-patterns.md`.
Otherwise → read `references/vitest-rtl-patterns.md`.

### Step 3: Detect Project Conventions

Scan for existing test files near the affected component:

1. Glob: `**/*.test.{ts,tsx}`, `**/*.spec.{ts,tsx}`, `**/__tests__/**` in the same package
2. Pick the nearest test file to the affected component (same directory > parent > sibling)
3. Extract from that file:
   - **Import style**: `@testing-library/react` vs custom `test-utils` wrapper
   - **Render pattern**: bare `render()` vs custom render with providers
   - **Query preference**: `getByRole` vs `getByTestId` vs `getByText`
   - **File location**: colocated (`__tests__/` or `.test.tsx` next to component) vs root `tests/` dir
   - **File naming**: `ComponentName.test.tsx` vs `component-name.spec.tsx`
4. If no existing test files found, note: "No existing test conventions detected. Using @testing-library/react defaults." Use colocated `.test.tsx` naming.

### Step 4: Generate the Test

Write the test file following detected conventions. Every generated test must include:

**Header annotations (mandatory):**
```typescript
/**
 * Regression test for: [bug title from DiagnosisReport]
 * Bug: [1-sentence defect description]
 * Fix: [1-sentence fix description]
 *
 * GUARDS AGAINST: [specific scenario this test catches]
 * DOES NOT GUARD AGAINST: [related untested scenarios from notAddressed]
 */
```

**Test structure:**
```typescript
describe('[ComponentName] - regression: [bug-slug]', () => {
  it('should [expected behavior that was broken]', () => {
    // Arrange: conditions that triggered the bug
    // Act: user action that exposed the bug
    // Assert: correct behavior
  });
});
```

**Anti-brittleness rules (hard constraints):**
- No snapshot tests — use explicit behavioral assertions
- Prefer `getByRole` with accessible name: `getByRole('button', { name: /submit/i })`
- Use `screen` object, not destructured render returns
- Mock at system boundaries (API, external services), not internal functions
- Assert user-visible outcomes ("error message appears"), not internal state
- No DOM structure assertions (`querySelector('.a > .b')`)
- No class name or CSS property assertions

### Step 5: Place the Test File

Follow the convention detected in Step 3:
- If colocated pattern: place next to the component file
- If root `tests/` pattern: mirror the source directory structure
- Use the detected naming convention (`.test.tsx` vs `.spec.tsx`)

Show the full file path and contents. Pause: "Write this test file?"

### Step 6: Validate the Test

After writing the test file, run it once:

```bash
# Vitest
npx vitest --run --reporter=verbose <test-file>

# Jest
npx jest <test-file> --verbose

# Playwright
npx playwright test <test-file> --reporter=list
```

Report result:
- **Test passes**: "Regression test passes. It verifies [behavior]. Run it before future changes to [component] to catch regressions."
- **Test fails**: "Test failed — this may indicate the test needs adjustment. Error: [message]." Do not auto-fix. Show the error and let the user decide.

## Output Format

```yaml
RegressionTest:
  version: "1.0"
  fix_ref: "[FixResult ID]"
  testFile: "path/to/ComponentName.test.tsx"
  framework: "vitest-rtl | jest-rtl | playwright"
  guardsAgainst: "specific regression scenario"
  doesNotGuardAgainst: ["untested scenario 1", "untested scenario 2"]
  conventions:
    source: "detected | defaults"
    nearestTestFile: "path or null"
  result: { status: "pass | fail", error: "message or null" }
```

## Handoff

Pass the RegressionTest artifact path to qa-coordinator. The result contains `testFile`, `framework`, `guardsAgainst`, and `doesNotGuardAgainst` fields. This is the final phase of the QA pipeline.

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/vitest-rtl-patterns.md` | Step 2, sync client or server component | Query priority, rendering patterns, assertion patterns, anti-patterns |
| `references/playwright-patterns.md` | Step 2, async server component or mixed | Test structure, locator priority, common regression patterns, API mocking |
