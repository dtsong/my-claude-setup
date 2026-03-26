---
name: e2e-testing
department: "craftsman"
description: "Use when designing end-to-end test suites, visual regression testing, or cross-browser test strategies. Covers Playwright/Cypress test architecture, page object patterns, test data management, visual snapshot comparison, cross-browser matrix, and CI integration. Do not use for unit/integration test strategy (use testing-strategy) or code pattern audit (use pattern-analysis)."
version: 1
triggers:
  - "e2e"
  - "end-to-end"
  - "visual regression"
  - "cross-browser"
  - "Playwright"
  - "Cypress"
  - "browser testing"
  - "screenshot testing"
  - "smoke test"
---

# E2E Testing

## Purpose

Design end-to-end test suites that validate critical user journeys across the full stack, catch visual regressions, and ensure cross-browser compatibility with efficient CI execution.

## Scope Constraints

Analyzes application architecture and existing test infrastructure to design E2E test strategy. Does not execute tests or modify application code. Does not set up CI pipelines (hand off to operator/deployment-plan).

## Inputs

- Application type and tech stack (SPA, SSR, mobile web)
- Critical user journeys to cover
- Current E2E framework in use, if any (Playwright, Cypress, Selenium)
- CI environment constraints (runner OS, parallelism, time budget)
- Browser/device matrix requirements

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define test scope and critical paths
- [ ] Step 2: Design test architecture
- [ ] Step 3: Plan visual regression strategy
- [ ] Step 4: Configure cross-browser matrix
- [ ] Step 5: Design test data management
- [ ] Step 6: Plan CI integration

### Step 1: Define Test Scope and Critical Paths

- Identify critical user journeys (auth, core workflows, payment, onboarding).
- Prioritize by business impact and failure cost.
- Define smoke test subset for deploy gates (target <2 min).
- Map which journeys need full E2E vs can rely on integration tests.
- Set coverage target: aim for 100% of critical paths, not 100% of features.

### Step 2: Design Test Architecture

- Recommend framework: Playwright for multi-browser/API testing, Cypress for single-browser simplicity.
- Define page object model or component abstraction pattern.
- Establish test file organization: by feature, by journey, or by page.
- Specify selector strategy: `data-testid` attributes over CSS/XPath.
- Design test isolation: each test independent, no shared state between tests.
- Define retry and timeout strategy per test category.

### Step 3: Plan Visual Regression Strategy

- Select visual comparison approach: pixel diff, perceptual diff, or DOM snapshot.
- Define baseline management: where snapshots are stored, how updates are approved.
- Specify viewport sizes for visual snapshots (mobile, tablet, desktop).
- Set diff thresholds to avoid false positives (anti-aliasing, font rendering).
- Plan for dynamic content exclusion (timestamps, avatars, ads).
- Recommend tooling: Playwright visual comparisons, Percy, Chromatic, or Argos.

### Step 4: Configure Cross-Browser Matrix

- Define browser matrix: Chromium, Firefox, WebKit at minimum.
- Identify browser-specific features that need targeted tests.
- Set mobile emulation profiles (viewport, user agent, touch events).
- Plan matrix reduction: full matrix on main branch, reduced on PRs.
- Document known browser-specific workarounds and their tests.

### Step 5: Design Test Data Management

- Define test data strategy: seeded database, API fixtures, or mock services.
- Plan database reset approach per test or per suite.
- Design factory patterns for test entity creation.
- Specify authentication shortcuts (API login vs UI login).
- Identify external service dependencies and stub/mock strategy.
- Plan for test data isolation in parallel execution.

### Step 6: Plan CI Integration

- Define test sharding strategy for parallel execution.
- Set test timeout budgets: smoke <2 min, full suite <15 min.
- Plan artifact collection: screenshots, videos, traces on failure.
- Design retry strategy for flaky test mitigation (max 2 retries).
- Define quality gates: block merge on smoke failure, warn on full suite.
- Plan test result reporting and trend tracking.

> **Compaction resilience**: If context was lost, re-read the Inputs section to identify the application under test, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### E2E Test Plan

| Journey | Priority | Tests | Framework | Browser Matrix | Data Strategy |
|---------|----------|-------|-----------|----------------|---------------|
| Auth flow | P0 - Smoke | 5 | Playwright | Chromium, Firefox, WebKit | API fixtures |
| Checkout | P0 - Smoke | 8 | ... | ... | ... |
| Dashboard | P1 - Full | 12 | ... | ... | ... |

### CI Execution Plan

| Gate | Tests | Parallelism | Time Budget | Trigger |
|------|-------|-------------|-------------|---------|
| PR smoke | 15 | 3 shards | <2 min | Every PR |
| Full suite | 80 | 6 shards | <15 min | Main branch |
| Visual regression | 30 | 2 shards | <5 min | PR + Main |

## Handoff

- Hand off to testing-strategy for unit/integration test layer design.
- Hand off to operator/deployment-plan for CI pipeline implementation.
- Hand off to advocate/interaction-design for identifying testable interaction states.

## Quality Checks

- [ ] Critical user journeys identified and prioritized
- [ ] Page object or abstraction pattern defined
- [ ] Selector strategy uses stable test attributes
- [ ] Visual regression baseline and threshold strategy documented
- [ ] Cross-browser matrix defined with reduction strategy for PRs
- [ ] Test data management ensures isolation in parallel runs
- [ ] CI time budgets specified for each gate
- [ ] Flaky test mitigation strategy documented

## Evolution Notes
<!-- Observations appended after each use -->
