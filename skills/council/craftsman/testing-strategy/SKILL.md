---
name: "Testing Strategy"
department: "craftsman"
description: "[Council] Design comprehensive test strategies with test pyramid coverage and quality gates. Used during council/academy deliberation only."
version: 1
triggers:
  - "test"
  - "testing"
  - "unit test"
  - "integration test"
  - "e2e"
  - "coverage"
  - "CI"
  - "quality gate"
  - "regression"
  - "TDD"
---

# Testing Strategy

## Purpose

Design comprehensive test strategies with test pyramid coverage, test file structure, and quality gates.

## Inputs

- Feature description and scope
- Existing test infrastructure (framework, runner, coverage tools)
- CI/CD pipeline details (if relevant)
- Existing test conventions in the codebase
- Coverage targets or requirements (if any)

## Process

### Step 1: Audit Existing Test Infrastructure

- Test framework (Jest, Vitest, Playwright, Cypress, etc.)
- Test runner and configuration
- Coverage tools (Istanbul, c8, etc.)
- CI integration (GitHub Actions, etc.)
- Existing test patterns (file location, naming, describe/it structure)
- Existing mocking patterns (jest.mock, vi.mock, MSW, etc.)

### Step 2: Identify Testable Units

From the feature, extract:
- **Pure functions and utilities** — deterministic, no side effects, easiest to test
- **Data transformations** — input/output mapping, validation logic
- **API handlers/endpoints** — request/response contracts, error handling
- **UI components** — render output, interaction behavior, state changes
- **Integration points** — database queries, external API calls, file I/O
- **Business logic** — rules, calculations, conditional flows

### Step 3: Design the Test Pyramid

```
        /  E2E  \        ← Few: critical user paths only (expensive, slow)
       /----------\
      / Integration \    ← Some: cross-boundary, API contracts, DB queries
     /----------------\
    /    Unit Tests     \ ← Many: fast, isolated, 80%+ of test count
   /--------------------\
```

- **Unit tests (base):** Fast, isolated, test one thing. Target 80%+ of total test count.
- **Integration tests (middle):** Cross-boundary tests. Database interactions, API contracts, service-to-service.
- **E2E tests (top):** Critical user paths only. Expensive to write and maintain, keep count low.

### Step 4: Write Test Specifications

For each layer, specify:

| Layer | Test File | Test Cases | Mocks Needed | Priority |
|-------|-----------|------------|--------------|----------|
| Unit | ... | ... | ... | ... |
| Integration | ... | ... | ... | ... |
| E2E | ... | ... | ... | ... |

For each test case:
- **Location:** Follow existing convention (co-located `__tests__/`, top-level `tests/`, or `.test.ts` suffix)
- **Description:** `describe('ModuleName', () => { it('should ...') })` format
- **Key assertions:** What exactly are we verifying?
- **Mock strategy:** What to mock (external deps), what to keep real (internal logic)
- **Edge cases:** Boundary values, empty inputs, error conditions

### Step 5: Define Coverage Targets

- **Line coverage:** Pragmatic target (70-90%, not 100%)
- **Branch coverage:** Focus on critical paths and business logic branches
- **Not worth testing:** Glue code, framework boilerplate, simple pass-through, type-only files
- **Must test:** Business rules, data transformations, error handling, security-sensitive code

### Step 6: Plan Quality Gates

- **Pre-commit:**
  - Lint (ESLint, Biome)
  - Type check (tsc --noEmit)
  - Affected unit tests (if tooling supports)
- **CI pipeline:**
  - Full test suite
  - Coverage threshold check
  - Build verification
- **Manual review checklist:**
  - [ ] New business logic has unit tests
  - [ ] Error paths are tested
  - [ ] No snapshot tests for logic (only for stable UI)
  - [ ] Mocks don't hide real bugs
  - [ ] Test descriptions read as documentation

## Output Format

### Test Pyramid Summary

| Layer | Count | Run Time | Mock Strategy |
|-------|-------|----------|---------------|
| Unit | ... | ... | ... |
| Integration | ... | ... | ... |
| E2E | ... | ... | ... |

### Test Specifications

For each test file:

```
File: src/__tests__/feature.test.ts
Layer: Unit

describe('FeatureName')
  it('should handle the happy path')
    - Input: ...
    - Expected: ...
  it('should handle invalid input')
    - Input: ...
    - Expected: throws/returns error
  it('should handle edge case')
    - Input: ...
    - Expected: ...

Mocks: ExternalService (return mock data)
```

### Coverage Targets

| Category | Target | Rationale |
|----------|--------|-----------|
| Business logic | 90%+ | Core value, must be correct |
| API handlers | 80%+ | Contract compliance |
| UI components | 70%+ | Render + key interactions |
| Utilities | 90%+ | Pure functions, easy to test |
| Glue/config | Skip | Not worth testing |

### Quality Gate Checklist

- [ ] Pre-commit hooks configured
- [ ] CI runs full test suite
- [ ] Coverage thresholds enforced
- [ ] New code has corresponding tests

## Quality Checks

- [ ] Every business logic function has a unit test spec
- [ ] Critical user paths have integration tests
- [ ] At least 1 E2E test for the main happy-path flow
- [ ] Mock strategy documented and doesn't hide real bugs
- [ ] Test file locations follow existing project conventions
- [ ] Edge cases and error paths included in test specs
- [ ] Coverage targets are pragmatic (not aspirational 100%)

## Evolution Notes
<!-- Observations appended after each use -->
