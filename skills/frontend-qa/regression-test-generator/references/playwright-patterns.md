# Playwright E2E Patterns

## Table of Contents

- [When to Use Playwright](#when-to-use-playwright)
- [Test Structure](#test-structure)
- [Locator Priority](#locator-priority-same-as-rtl)
- [Common Regression Patterns](#common-regression-patterns)
- [API Mocking (Route Handlers)](#api-mocking-route-handlers)
- [Anti-Patterns](#anti-patterns-never-generate-these)

## When to Use Playwright

Hard rule: async server components cannot be unit-tested with Vitest+RTL because they require the Next.js server runtime. Route these to Playwright.

Also use for: route-level behavior, middleware effects, client-server interaction, navigation flows, visual regression.

## Test Structure

```typescript
import { test, expect } from '@playwright/test'

test.describe('[PageName] - regression: [bug-slug]', () => {
  test('should [expected behavior]', async ({ page }) => {
    // Navigate to the route
    await page.goto('/route-path')

    // Wait for meaningful content (not arbitrary timeout)
    await expect(page.getByRole('heading', { name: /title/i })).toBeVisible()

    // Act
    await page.getByRole('button', { name: /action/i }).click()

    // Assert
    await expect(page.getByText(/result/i)).toBeVisible()
  })
})
```

## Locator Priority (Same as RTL)

| Priority | Locator | Example |
|----------|---------|---------|
| 1 | `getByRole` | `page.getByRole('button', { name: /submit/i })` |
| 2 | `getByLabel` | `page.getByLabel('Email')` |
| 3 | `getByPlaceholder` | `page.getByPlaceholder('Enter email')` |
| 4 | `getByText` | `page.getByText('Welcome')` |
| Last resort | `getByTestId` | `page.getByTestId('custom-element')` |

Never use CSS selectors (`page.locator('.class')`) unless no accessible locator exists.

## Common Regression Patterns

### Async server component rendering
```typescript
test('should render server-fetched data', async ({ page }) => {
  await page.goto('/dashboard')
  // Server component data should be in initial HTML
  await expect(page.getByRole('table')).toBeVisible()
  await expect(page.getByRole('cell', { name: /expected value/i })).toBeVisible()
})
```

### Navigation and routing
```typescript
test('should navigate to detail page', async ({ page }) => {
  await page.goto('/items')
  await page.getByRole('link', { name: /item name/i }).click()
  await expect(page).toHaveURL(/\/items\/\d+/)
  await expect(page.getByRole('heading', { name: /item name/i })).toBeVisible()
})
```

### Form submission (server action)
```typescript
test('should submit form and show confirmation', async ({ page }) => {
  await page.goto('/contact')
  await page.getByLabel('Name').fill('Test User')
  await page.getByLabel('Email').fill('test@example.com')
  await page.getByRole('button', { name: /send/i }).click()
  await expect(page.getByText(/thank you/i)).toBeVisible()
})
```

### Error states
```typescript
test('should show error for invalid input', async ({ page }) => {
  await page.goto('/form')
  await page.getByRole('button', { name: /submit/i }).click()
  await expect(page.getByText(/required/i)).toBeVisible()
})
```

### Loading and streaming
```typescript
test('should show loading then content', async ({ page }) => {
  await page.goto('/data-page')
  // Suspense fallback may flash briefly
  await expect(page.getByRole('main')).toBeVisible()
  // Wait for streamed content
  await expect(page.getByText(/loaded data/i)).toBeVisible({ timeout: 10000 })
})
```

### Visual regression (Tier 2 — only if Playwright screenshots configured)
```typescript
test('should match visual baseline', async ({ page }) => {
  await page.goto('/component-page')
  await expect(page.getByRole('main')).toBeVisible()
  // Only generate if project has existing screenshot baselines
  await expect(page).toHaveScreenshot('component-page.png', {
    maxDiffPixelRatio: 0.01,
  })
})
```

Generate visual regression tests only if the project already has a `*.png` baseline in a test snapshots directory. Do not create the first visual baseline in a regression test — that is a project decision.

## API Mocking (Route Handlers)

If the project uses Playwright route interception:

```typescript
test('should handle API error', async ({ page }) => {
  await page.route('**/api/data', (route) =>
    route.fulfill({ status: 500, body: 'Internal Server Error' })
  )
  await page.goto('/data-page')
  await expect(page.getByRole('alert')).toBeVisible()
  await expect(page.getByText(/something went wrong/i)).toBeVisible()
})
```

Prefer route interception over modifying source code for test mocks.

## Anti-Patterns (Never Generate These)

```typescript
// BAD: arbitrary wait
await page.waitForTimeout(3000)

// BAD: CSS selector
await page.locator('.card-wrapper > div.content').click()

// BAD: fragile URL assertion
await expect(page).toHaveURL('http://localhost:3000/exact/path?with=params')
// GOOD: pattern match
await expect(page).toHaveURL(/\/exact\/path/)

// BAD: screenshot without existing baseline
await expect(page).toHaveScreenshot() // creates baseline on first run — not a regression test
```
