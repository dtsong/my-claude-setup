# Verification Commands Reference

## Table of Contents

- [TypeScript Checking](#typescript-checking)
- [Lint Checking](#lint-checking)
- [Test Running](#test-running)
- [Infrastructure Detection Summary](#infrastructure-detection-summary)
- [E2E Tests (Playwright)](#e2e-tests-playwright)

## TypeScript Checking

### Scoped (affected files only)

```bash
# Standard project
npx tsc --noEmit --pretty <file1.tsx> <file2.tsx>

# Project references / composite
npx tsc -b --noEmit

# Monorepo (run from package root)
cd <package-dir> && npx tsc --noEmit --pretty <file1.tsx>
```

### Broad (full project)

```bash
npx tsc --noEmit --pretty 2>&1
```

Compare error count to baseline. New errors = FAIL. Same count = pre-existing (PARTIAL).

### Detection

- Check `tsconfig.json` exists at project root
- If `composite: true` or `references` array present, use `-b` flag
- If `tsconfig.json` missing, skip tsc and report SKIPPED

## Lint Checking

### Detect linter

| Check | Linter | Config files |
|-------|--------|-------------|
| First | Biome | `biome.json`, `biome.jsonc` |
| Second | ESLint | `eslint.config.*`, `.eslintrc.*`, `eslintConfig` in package.json |
| Third | Package script | `scripts.lint` in package.json |
| None found | Skip | Report: "No linter detected" |

### Scoped commands

```bash
# ESLint (flat or legacy config)
npx eslint --no-error-on-unmatched-pattern <file1.tsx> <file2.tsx>

# Biome
npx biome check <file1.tsx> <file2.tsx>

# Package script fallback (runs full lint)
npm run lint
```

### Broad commands

```bash
# Prefer project lint script for broad
npm run lint
# or
pnpm lint
```

## Test Running

### Detect test framework

| Check | Framework | Config files |
|-------|-----------|-------------|
| First | Vitest | `vitest.config.*`, `vite.config.*` with test block |
| Second | Jest | `jest.config.*`, `jest` key in package.json |
| Third | Package script | `scripts.test` in package.json |
| None found | Skip | Report: "No test infrastructure detected" |

### Scoped commands (related tests only)

```bash
# Vitest — run tests related to changed files
npx vitest --run --reporter=verbose --related <file1.tsx> <file2.tsx>

# Jest — find and run related tests
npx jest --findRelatedTests <file1.tsx> <file2.tsx> --verbose

# Fallback: directory-scoped
npx vitest --run --reporter=verbose <dir/>
npx jest <dir/> --verbose
```

### Broad commands (full suite)

```bash
# Prefer project test script
npm test -- --run          # vitest needs --run to exit
npm test                   # jest exits by default

# Direct invocation
npx vitest --run --reporter=verbose
npx jest --verbose
```

### Common failures that are NOT fix-related

- `Cannot find module` on test utilities → pre-existing infrastructure issue
- Timeout on unrelated test file → pre-existing flaky test
- Snapshot mismatch on unrelated component → pre-existing snapshot drift

Record these as pre-existing. They do not make the verdict FAIL.

## Infrastructure Detection Summary

Run this sequence before Phase 4:

```
1. TypeScript: ls tsconfig.json → present? → tsc available
2. Linter: check biome.json, eslint config, scripts.lint → detected? → lint available
3. Tests: check vitest/jest config, scripts.test → detected? → tests available
4. Runner validation: execute detected runner with --help or minimal dry-run
   - If runner fails to start (missing deps, broken config): INFRASTRUCTURE_BROKEN
   - If runner starts but no tests found for affected files: report 0 related tests
```

Report honestly:
```
Verification scope: tsc [yes/no] + lint [tool/none] + tests [runner/none]
```

## E2E Tests (Playwright)

Only run if the DiagnosisReport flagged an issue requiring E2E verification (async server component, route-level behavior, client-server interaction).

```bash
# Run specific test file
npx playwright test <test-file.spec.ts> --reporter=list

# Run tests matching a grep pattern
npx playwright test --grep "<pattern>" --reporter=list
```

Do not run the full Playwright suite during fix verification — E2E suites are slow. Run only the specific test relevant to the fix.
