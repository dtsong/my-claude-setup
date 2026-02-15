---
name: tdd
description: >
  Test-driven development reference for writing good tests, designing testable
  interfaces, mocking at system boundaries, and refactoring after green. Use when
  writing tests, reviewing test quality, or applying red-green-refactor workflow.
  Not for running test suites or CI configuration — use language-conventions or
  cicd-generation for those.
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: true
  reasoning_demand: low
---

# TDD Reference

Practical guidance for test-driven development: writing good tests, designing testable interfaces, mocking correctly, and refactoring safely.

## Scope Constraints

- Read-only reference skill — provides guidance, does not modify code
- Does not run tests, generate test files, or configure test runners
- Complements `superpowers:test-driven-development` workflow skill

## Inputs

- **Context** (required): What the user is testing or designing
- **Phase** (optional): `red` (writing failing test), `green` (making it pass), `refactor` (cleaning up)

## Input Sanitization

- Context descriptions: free text, reject null bytes.

## Procedure

1. Identify the TDD phase. If unclear, ask: "Are you writing a new test, making one pass, or refactoring?"
2. Load the reference file matching the phase or question:
   - Writing tests → `references/tests.md`
   - Designing interfaces for testability → `references/interface-design.md`
   - Mocking decisions → `references/mocking.md`
   - Refactoring after green → `references/refactoring.md`
   - Module depth and API design → `references/deep-modules.md`
3. Apply the reference guidance to the user's specific code context.
4. Flag anti-patterns from the loaded reference when found in user code.

## Output Format

```
## TDD Guidance: [phase/topic]

[Specific advice applied to user's code context]

  Pattern: [recommended approach]
  Anti-pattern: [what to avoid and why]

Reference: [which reference file was consulted]
```

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/tests.md` | Writing or reviewing tests | Good vs bad test patterns, quality table, examples |
| `references/mocking.md` | Mock decisions or test setup | When to mock, anti-patterns, dependency injection |
| `references/interface-design.md` | Designing testable code | DI, return values over side effects, surface area |
| `references/refactoring.md` | After green phase | Refactor candidates checklist |
| `references/deep-modules.md` | API/module design | Deep vs shallow modules, interface simplification |
