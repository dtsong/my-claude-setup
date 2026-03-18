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

## Gotchas

- Tests that assert implementation details (e.g., checking internal method calls) break on every refactor — test behavior and outputs, not how the code does it
- Mocking at the wrong boundary (e.g., mocking the function under test, or mocking too deep) — mock at system boundaries (HTTP, DB, filesystem), not internal modules
- Assertion-free "tests" that just call code without checking results — every test needs at least one meaningful assertion
- `beforeAll` shared state between tests causes order-dependent failures — prefer `beforeEach` for fresh state per test
- Testing private methods directly indicates poor interface design — if you need to test it, it should be part of the public API
- Snapshot tests that get `--update`d without review become rubber stamps — review every snapshot diff carefully

```typescript
// WRONG: testing implementation details
expect(service.internalCache.size).toBe(3);
// RIGHT: testing behavior
expect(await service.getUser("abc")).toEqual({ id: "abc", name: "Alice" });

// WRONG: mocking the thing you're testing
vi.spyOn(calculator, 'add').mockReturnValue(5);
expect(calculator.add(2, 3)).toBe(5); // tests nothing
// RIGHT: mock dependencies, test the unit
vi.spyOn(httpClient, 'get').mockResolvedValue({ rate: 1.5 });
expect(await converter.convert(100, 'USD', 'EUR')).toBe(150);
```

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/tests.md` | Writing or reviewing tests | Good vs bad test patterns, quality table, examples |
| `references/mocking.md` | Mock decisions or test setup | When to mock, anti-patterns, dependency injection |
| `references/interface-design.md` | Designing testable code | DI, return values over side effects, surface area |
| `references/refactoring.md` | After green phase | Refactor candidates checklist |
| `references/deep-modules.md` | API/module design | Deep vs shallow modules, interface simplification |
