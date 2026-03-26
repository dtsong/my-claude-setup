---
name: "e2e-testing"
department: "craftsman"
description: "Use when designing end-to-end test suites, visual regression tests, or cross-browser strategies. Covers Playwright/Cypress patterns, test data management, and CI integration for E2E. Do not use for unit/integration test planning (use testing-strategy)."
version: 1
triggers:
  - "e2e"
  - "end-to-end"
  - "visual regression"
  - "cross-browser"
  - "Playwright"
  - "Cypress"
  - "browser testing"
  - "smoke test"
---

# E2E Testing

## Purpose

Design robust end-to-end test suites with cross-browser coverage, visual regression detection, and CI-optimized execution.

## Scope Constraints

- Covers E2E test design patterns, visual regression testing, cross-browser strategy, Playwright/Cypress patterns, test data management, and CI integration.
- Does not cover unit or integration test planning — hand off to testing-strategy.
- Does not cover infrastructure or deployment pipeline design — hand off to operator department.

## Inputs

- Application type (web, mobile web, desktop via Electron)
- Critical user journeys to cover
- Target browsers and viewports
- Existing E2E infrastructure (framework, config, test count)
- CI/CD pipeline details
- Visual design baseline requirements (if any)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist

- [ ] Step 1: Audit existing E2E infrastructure
- [ ] Step 2: Identify critical user journeys
- [ ] Step 3: Design test architecture
- [ ] Step 4: Define cross-browser strategy
- [ ] Step 5: Plan visual regression approach
- [ ] Step 6: Design test data management
- [ ] Step 7: Configure CI integration

### Step 1: Audit Existing E2E Infrastructure

- Framework in use (Playwright, Cypress, Selenium, none)
- Configuration files and base URL setup
- Existing test count, flakiness rate, average run time
- Authentication handling (fixtures, API login, stored state)
- Current CI integration and parallelization

### Step 2: Identify Critical User Journeys

- Map top 5-10 user flows by business impact
- Prioritize: sign-up, core feature loop, checkout/conversion, error recovery
- Mark smoke-test subset for PR checks vs full suite for nightly

### Step 3: Design Test Architecture

- Page Object Model or component-based abstractions
- Fixture and helper organization
- Test isolation strategy (independent state per test)
- Selector strategy: prefer `data-testid` > role > CSS; never use fragile selectors
- Assertion patterns: wait-for over sleep, auto-retrying assertions

### Step 4: Define Cross-Browser Strategy

- Primary: Chromium (every PR)
- Secondary: Firefox, WebKit (nightly or release gate)
- Viewport matrix: desktop (1280x720), tablet (768x1024), mobile (375x812)
- If Playwright: use `projects` config; if Cypress: use `--browser` flag per CI job

### Step 5: Plan Visual Regression Approach

- Tool selection: Playwright built-in snapshots, Percy, Chromatic, or Argos
- Baseline management: commit snapshots vs external service
- Threshold tuning: pixel diff percentage, anti-aliasing tolerance
- Update workflow: how to approve intentional changes

### Step 6: Design Test Data Management

- Seed strategy: API-based setup in `beforeEach`, not UI-driven
- Cleanup: API teardown or ephemeral environments
- Sensitive data: never hardcode credentials; use env vars or vault
- State isolation: each test creates its own data, no shared mutable state

### Step 7: Configure CI Integration

- Parallelization: shard by file or test; target <10 min total
- Artifact collection: screenshots, videos, traces on failure
- Retry policy: 1 retry for flaky mitigation, flag repeated failures
- Reporting: HTML report or CI dashboard integration
- Gate policy: smoke suite blocks PR merge; full suite is nightly

> **Compaction resilience:** If context is compacted mid-task, check the Progress Checklist for completed steps, re-read this Procedure section, and continue from the next incomplete step.

## Handoff

- If test planning scope expands to unit/integration layers, hand off to **testing-strategy**.
- If CI pipeline architecture changes are needed, hand off to **operator department**.
- If selector strategy reveals inconsistent component structure, hand off to **pattern-analysis**.

## Output Format

### E2E Test Plan Summary

| Aspect | Decision |
|--------|----------|
| Framework | ... |
| Critical Journeys | ... |
| Browser Matrix | ... |
| Visual Regression | ... |
| CI Gate | ... |
| Target Run Time | ... |

### Test Specifications

```
File: e2e/flows/checkout.spec.ts

describe('Checkout Flow')
  it('completes purchase with valid payment')
  it('shows validation errors for invalid card')
  it('handles session timeout gracefully')

Data setup: API seed → user + cart + product
Cleanup: API teardown
Browsers: Chromium (PR), Firefox + WebKit (nightly)
```

### Quality Checks

- [ ] Every critical user journey has at least one E2E test
- [ ] Tests are independent — no shared mutable state between tests
- [ ] Selectors use `data-testid` or accessible roles, not fragile CSS
- [ ] No hard-coded waits; all waits use auto-retrying assertions
- [ ] Visual regression baselines are versioned and reviewable
- [ ] CI runs complete in under 10 minutes with parallelization
- [ ] Failure artifacts (screenshots, traces) are collected automatically
- [ ] Test data is created and cleaned up per test

## Evolution Notes
<!-- Observations appended after each use -->
