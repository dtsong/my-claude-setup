# Test Generation Patterns

## Framework Routing Table

| Component Type | Indicator | Test Framework | Rationale |
|---------------|-----------|---------------|-----------|
| Sync client component | `"use client"`, hooks, state | Vitest + RTL | Fast, isolated, behavior-focused |
| Sync server component | No `"use client"`, no hooks | Vitest + RTL | Supported in Next.js 15+ with Vitest |
| Async server component | `async function`, top-level `await` | Playwright E2E | Vitest cannot render async components |
| Page with data fetching | `fetch()` in server component, server actions | Playwright E2E | Requires full server environment |
| Client interaction flow | Form submission, navigation, multi-step UI | Playwright E2E | Cross-component browser behavior |
| Pure utility function | No JSX, no React imports | Vitest (no RTL) | Unit test with plain assertions |

- Rule: never generate a Vitest test for an async server component — it will fail at import time

## Accessible Selector Hierarchy

| Priority | Query | Use Case |
|----------|-------|----------|
| 1 | `getByRole('button', { name: 'Submit' })` | Most stable, matches accessibility tree |
| 2 | `getByLabelText('Email address')` | Form inputs with associated labels |
| 3 | `getByPlaceholderText('Search...')` | When no visible label exists |
| 4 | `getByText('Welcome back')` | Non-interactive text content |
| 5 | `getByDisplayValue('current value')` | Pre-filled form fields |
| 6 | `getByAltText('Product photo')` | Images |
| 7 | `getByTitle('Close dialog')` | Elements with title attributes |
| 8 | `getByTestId('submit-btn')` | Last resort; couples test to implementation |

- Rule: never use `container.querySelector('.class-name')`, `container.firstChild`, or DOM structure traversal

## Anti-Brittleness Rules

- Rule: assert on user-visible outcomes ("error message appears") not internal state ("error flag is true")
- Rule: mock at system boundaries (API calls, router, external services) not internal functions or hooks
- Rule: use `screen` object for queries, not destructured `render()` return values
- Rule: no snapshot tests for regression purposes — use explicit behavioral assertions
- Rule: no assertions on class names, inline styles, or CSS properties
- Rule: no assertions on exact error message strings for third-party libraries (they change across versions)
- Check: element appears after state change → prefer `findByRole` (async) over `getByRole` (sync, throws immediately)
- Rule: wrap state-changing actions in `act()` or use `userEvent` which handles this automatically
- Rule: test one behavior per test; multiple assertions fine if they verify the same user-visible outcome

## Convention Detection

Before generating any test, scan for existing patterns:

1. Glob: `**/*.test.{ts,tsx}`, `**/*.spec.{ts,tsx}`, `**/__tests__/**`
2. Find nearest test file to the component under test
3. Extract: import style, render pattern, query preference, assertion library, file location, naming convention
4. If no existing tests found: use RTL best practices defaults

## Regression Test Template

```typescript
/**
 * Regression test for: [bug title]
 * Bug: [1-sentence what was broken]
 * Fix: [1-sentence what was changed]
 *
 * GUARDS AGAINST: [specific scenario this catches]
 * DOES NOT GUARD AGAINST: [related untested scenarios]
 */
describe('[ComponentName] - regression: [bug-slug]', () => {
  it('should [expected behavior that was previously broken]', () => {
    // Arrange: set up the conditions that triggered the bug
    // Act: perform the user action that exposed the bug
    // Assert: verify the correct behavior
  });
});
```

## Framework Notes

- Vitest: `vi.mock()` for modules, `vi.fn()` for spies, `vi.stubGlobal()` for globals like `fetch`
- Jest: `jest.mock()` for modules, `jest.fn()` for spies, `moduleNameMapper` for path aliases
- Playwright: `page.route()` to intercept requests, `page.waitForResponse()` for API assertions
- RTL: `cleanup` is automatic in Vitest/Jest with proper setup; do not call manually
- Next.js router: mock `next/navigation` exports (`useRouter`, `usePathname`, `useSearchParams`) not module internals
