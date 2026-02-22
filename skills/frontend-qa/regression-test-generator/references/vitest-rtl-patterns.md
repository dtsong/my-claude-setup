# Vitest + React Testing Library Patterns

## Table of Contents

- [Query Priority](#query-priority-use-in-this-order)
- [Component Rendering Patterns](#component-rendering-patterns)
- [Assertion Patterns for Common Regressions](#assertion-patterns-for-common-regressions)
- [Anti-Patterns](#anti-patterns-never-generate-these)

## Query Priority (Use In This Order)

| Priority | Query | When to use |
|----------|-------|-------------|
| 1 | `getByRole` | Buttons, links, headings, forms, landmarks — always try first |
| 2 | `getByLabelText` | Form inputs with labels |
| 3 | `getByPlaceholderText` | Inputs without visible labels (less accessible — note this) |
| 4 | `getByText` | Non-interactive text content |
| 5 | `getByDisplayValue` | Filled form inputs |
| Last resort | `getByTestId` | Only if no accessible query works — add `data-testid` to source |

Always use `screen` object: `screen.getByRole('button', { name: /submit/i })`.

## Component Rendering Patterns

### Basic client component
```tsx
import { render, screen } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import { ComponentName } from './ComponentName'

it('should [behavior]', async () => {
  const user = userEvent.setup()
  render(<ComponentName prop="value" />)
  await user.click(screen.getByRole('button', { name: /submit/i }))
  expect(screen.getByText(/success/i)).toBeInTheDocument()
})
```

### With providers (detected custom render)
```tsx
// If project has a custom render in test-utils:
import { render, screen } from '@/test-utils' // match project import
import { ComponentName } from './ComponentName'

it('should [behavior]', () => {
  render(<ComponentName />)
  // providers (theme, router, query client) are handled by custom render
})
```

### With mocked API boundary
```tsx
import { http, HttpResponse } from 'msw'
import { server } from '@/mocks/server' // if MSW detected

// or inline mock:
vi.mock('@/lib/api', () => ({
  fetchData: vi.fn().mockResolvedValue({ items: [{ id: 1, name: 'Test' }] })
}))
```

If MSW is in dependencies, prefer MSW handlers over `vi.mock`. MSW tests the full fetch path.

### With Next.js router
```tsx
import { useRouter, usePathname } from 'next/navigation'

vi.mock('next/navigation', () => ({
  useRouter: vi.fn(() => ({ push: vi.fn(), back: vi.fn() })),
  usePathname: vi.fn(() => '/current-path'),
  useSearchParams: vi.fn(() => new URLSearchParams()),
}))
```

## Assertion Patterns for Common Regressions

### Element visibility
```tsx
expect(screen.getByRole('alert')).toBeInTheDocument()
expect(screen.queryByRole('alert')).not.toBeInTheDocument() // absent
```

### Form submission
```tsx
const user = userEvent.setup()
await user.type(screen.getByLabelText(/email/i), 'test@example.com')
await user.click(screen.getByRole('button', { name: /submit/i }))
expect(screen.getByText(/submitted/i)).toBeInTheDocument()
```

### Conditional rendering
```tsx
// Before: element should not exist
expect(screen.queryByText(/error/i)).not.toBeInTheDocument()
// Trigger condition
await user.click(screen.getByRole('button'))
// After: element should appear
expect(screen.getByText(/error/i)).toBeInTheDocument()
```

### Loading states
```tsx
render(<ComponentWithAsync />)
expect(screen.getByRole('progressbar')).toBeInTheDocument() // or getByText(/loading/i)
await waitFor(() => {
  expect(screen.queryByRole('progressbar')).not.toBeInTheDocument()
})
expect(screen.getByText(/data loaded/i)).toBeInTheDocument()
```

### Event handler fires
```tsx
const onAction = vi.fn()
render(<Component onAction={onAction} />)
await user.click(screen.getByRole('button', { name: /trigger/i }))
expect(onAction).toHaveBeenCalledOnce()
expect(onAction).toHaveBeenCalledWith(expect.objectContaining({ id: 1 }))
```

## Anti-Patterns (Never Generate These)

```tsx
// BAD: snapshot — catches everything, guards nothing specific
expect(container).toMatchSnapshot()

// BAD: DOM structure — breaks on any restructuring
expect(container.querySelector('.card > .header > h2')).toHaveTextContent('Title')

// BAD: class name assertion — breaks on styling changes
expect(element).toHaveClass('bg-red-500')

// BAD: implementation detail — tests internal state, not behavior
expect(component.state.isOpen).toBe(true)

// BAD: internal mock — couples test to implementation
vi.mock('./useInternalHook')
```
