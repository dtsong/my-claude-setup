---
description: "Enforce test-driven development — red-green-refactor loop with no exceptions"
argument-hint: "[TASK, ISSUE URL, or BUG DESCRIPTION...]"
---

# /tdd — Test-Driven Development

Explicit entry point for strict TDD workflow. Every line of production code starts with a failing test.

## Usage

```
/tdd fix the email validation bug
/tdd https://github.com/org/repo/issues/42
/tdd add retry logic to the API client
```

## Instructions

When the user runs `/tdd`, follow these steps:

### 1. Capture the Task

The task is everything after `/tdd`. If no argument is provided, ask: "What are we building or fixing?"

If the argument is a GitHub issue URL, fetch the issue details with `gh issue view`.

### 2. Load TDD Workflow

Invoke the `superpowers:test-driven-development` skill. This is the governing workflow for the entire session — follow it without exception.

### 3. Load TDD Reference

Load `skills/tdd/SKILL.md` for reference guidance on tests, interface design, mocking, and refactoring. Use its conditional references as needed throughout the session.

### 4. Confirm Scope

Before writing any test, confirm with the user:
- What behaviors need to exist (or change)?
- What is the test boundary (which module/function/endpoint)?
- What test framework and runner does this project use?

If these can be answered by exploring the codebase, explore instead of asking.

### 5. Execute Red-Green-Refactor

Follow the cycle from `superpowers:test-driven-development` strictly:

1. **RED** — Write one failing test. Run it. Confirm it fails for the right reason.
2. **GREEN** — Write minimal code to pass. Run tests. Confirm all green.
3. **REFACTOR** — Clean up while staying green.
4. **Repeat** — Next behavior, next test.

Do not batch tests. One test at a time. One behavior at a time.

### Important Rules

- No production code without a failing test first. Wrote code first? Delete it. Start over.
- Run tests after every RED and GREEN step — never skip verification.
- If a test passes immediately, it tests existing behavior. Fix or discard the test.
- Mocks only at system boundaries (HTTP, DB, filesystem). Never mock the unit under test.
- When stuck, the test is telling you the interface is wrong. Listen to it.
