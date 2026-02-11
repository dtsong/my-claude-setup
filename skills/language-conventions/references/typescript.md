---
language: typescript
stack: Next.js + React + Tailwind + shadcn/ui
min_version: "5.0"
last_updated: 2026-02-10
token_estimate: ~3200
---

# TypeScript Conventions

Opinionated TypeScript conventions for Next.js + React applications with Tailwind and shadcn/ui.

## Tooling

| Tool | Purpose | Command |
|------|---------|---------|
| **pnpm** | Workspace-based package manager | `pnpm install`, `pnpm --filter <pkg> add` |
| **Vitest** | Testing + coverage | `pnpm test`, `pnpm test:coverage` |
| **Prettier** | Formatting | `pnpm format` |
| **TypeScript** | Type checking (strict mode) | `pnpm typecheck` |

## TypeScript Config

```json
{
  "compilerOptions": {
    "target": "ES2017",
    "lib": ["dom", "dom.iterable", "esnext"],
    "allowJs": true,
    "skipLibCheck": true,
    "strict": true,
    "noUncheckedIndexedAccess": true,
    "noEmit": true,
    "esModuleInterop": true,
    "module": "esnext",
    "moduleResolution": "bundler",
    "resolveJsonModule": true,
    "isolatedModules": true,
    "jsx": "preserve",
    "incremental": true,
    "plugins": [{ "name": "next" }],
    "paths": { "@/*": ["./src/*"] }
  },
  "include": ["next-env.d.ts", "**/*.ts", "**/*.tsx", ".next/types/**/*.ts"],
  "exclude": ["node_modules"]
}
```

## Pre-commit Config

```yaml
repos:
  - repo: https://github.com/pre-commit/pre-commit-hooks
    rev: v5.0.0
    hooks:
      - id: trailing-whitespace
      - id: end-of-file-fixer
      - id: check-yaml
      - id: check-json
      - id: check-added-large-files

  - repo: local
    hooks:
      - id: prettier
        name: prettier
        entry: bash -c 'source ~/.nvm/nvm.sh && nvm use default --silent && npx prettier --write "$@"' --
        language: system
        types_or: [javascript, jsx, ts, tsx, json, yaml, markdown]

      - id: typecheck
        name: TypeScript typecheck
        entry: bash -c 'source ~/.nvm/nvm.sh && nvm use default --silent && pnpm typecheck'
        language: system
        types_or: [ts, tsx]
        pass_filenames: false
```

## Vitest Config

```typescript
import { defineConfig } from "vitest/config";
import react from "@vitejs/plugin-react";
import path from "path";

export default defineConfig({
  plugins: [react()],
  test: {
    environment: "jsdom",
    globals: true,
    setupFiles: ["./src/test/setup.ts"],
    coverage: {
      provider: "v8",
      reporter: ["text", "html", "lcov"],
      include: ["src/**/*.ts", "src/**/*.tsx"],
      exclude: ["src/**/*.test.ts", "src/**/*.test.tsx", "src/**/__tests__/**", "src/app/**"],
    },
  },
  resolve: {
    alias: { "@": path.resolve(__dirname, "./src") },
  },
});
```

### Test Setup File

```typescript
// src/test/setup.ts
import "@testing-library/jest-dom/vitest";
```

## Next.js App Router

- `"use client"` directive for client components
- `dynamic(() => import(...))` for code splitting
- Layout/page hierarchy: `layout.tsx` wraps all children
- Providers wrapper pattern (QueryClientProvider, theme, etc.)
- `src/app/` directory structure

```
src/
├── app/
│   ├── layout.tsx         # Root layout
│   ├── page.tsx           # Home page
│   ├── providers.tsx      # Client-side providers wrapper
│   └── <feature>/
│       ├── page.tsx
│       └── layout.tsx
├── components/
│   ├── ui/                # shadcn primitives
│   └── <feature>/         # Domain components
├── lib/
│   ├── api.ts             # API client
│   ├── utils.ts           # cn() and helpers
│   └── hooks/             # Custom hooks
├── stores/                # Zustand stores
└── test/
    └── setup.ts           # Test setup
```

## Tailwind CSS

- HSL CSS variables for theming: `--primary: 222.2 84% 4.9%`
- Custom color scales via CSS variables
- `cn()` utility combining `clsx` + `tailwind-merge`
- Dark mode via class strategy
- `tailwind.config.ts` with content paths

```typescript
// lib/utils.ts
import { clsx, type ClassValue } from "clsx";
import { twMerge } from "tailwind-merge";

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}
```

## shadcn/ui

- `React.forwardRef` for all components
- CVA (class-variance-authority) for variants
- Radix `Slot` for composition
- `displayName` on all forwarded ref components
- Install via `npx shadcn@latest add`

```typescript
const Button = React.forwardRef<HTMLButtonElement, ButtonProps>(
  ({ className, variant, size, ...props }, ref) => {
    return (
      <button
        className={cn(buttonVariants({ variant, size, className }))}
        ref={ref}
        {...props}
      />
    );
  },
);
Button.displayName = "Button";
```

## Data Fetching

- React Query with `staleTime`, `gcTime`, `retry` config
- Centralized API client (`src/lib/api.ts`)
- Zod schema validation for API responses
- Query key factories for consistent cache keys

```typescript
// Query key factory
export const itemKeys = {
  all: ["items"] as const,
  lists: () => [...itemKeys.all, "list"] as const,
  list: (filters: Filters) => [...itemKeys.lists(), filters] as const,
  details: () => [...itemKeys.all, "detail"] as const,
  detail: (id: string) => [...itemKeys.details(), id] as const,
};

// Usage
const { data } = useQuery({
  queryKey: itemKeys.detail(id),
  queryFn: () => api.getItem(id),
  staleTime: 5 * 60 * 1000,
});
```

## State Management

- Zustand with `persist` middleware
- `partialize` for selective persistence
- SSR-safe localStorage (check `typeof window`)
- Separate stores by domain

```typescript
import { create } from "zustand";
import { persist } from "zustand/middleware";

interface PreferencesStore {
  theme: "light" | "dark";
  setTheme: (theme: "light" | "dark") => void;
}

export const usePreferencesStore = create<PreferencesStore>()(
  persist(
    (set) => ({
      theme: "light",
      setTheme: (theme) => set({ theme }),
    }),
    {
      name: "preferences",
      partialize: (state) => ({ theme: state.theme }),
    },
  ),
);
```

## Testing

- `vi.mock()` with factory functions
- `vi.clearAllMocks()` in afterEach
- `mockFetch` / `createMockResponse` helpers
- Provider wrapping: wrap components in QueryClientProvider for tests
- `@testing-library/jest-dom/vitest` for matchers
- `@testing-library/user-event` for interactions

```typescript
import { render, screen } from "@testing-library/react";
import userEvent from "@testing-library/user-event";
import { QueryClient, QueryClientProvider } from "@tanstack/react-query";

function renderWithProviders(ui: React.ReactElement) {
  const queryClient = new QueryClient({
    defaultOptions: { queries: { retry: false } },
  });
  return render(
    <QueryClientProvider client={queryClient}>{ui}</QueryClientProvider>,
  );
}

vi.mock("@/lib/api", () => ({
  api: { getItems: vi.fn() },
}));
```

## Component Organization

- Domain folders: `src/components/<feature>/`
- `ui/` for primitives (shadcn components)
- `__tests__/` colocated with components
- Named exports preferred over default

## Shared Types

- `@<project>/shared-types` workspace package
- `Api*` prefix for API types (snake_case from backend)
- camelCase for frontend types
- Zod schemas for runtime validation

```typescript
// API type (matches backend snake_case)
interface ApiItem {
  id: string;
  created_at: string;
  display_name: string;
}

// Frontend type (camelCase)
interface Item {
  id: string;
  createdAt: string;
  displayName: string;
}
```

## Accessibility

- Skip-to-content link
- `data-testid` for test selectors
- `motion-safe:` for animations (reduced motion)
- Semantic HTML, ARIA where needed

## Security Headers (next.config)

```typescript
const securityHeaders = [
  { key: "X-Content-Type-Options", value: "nosniff" },
  { key: "X-Frame-Options", value: "DENY" },
  { key: "X-XSS-Protection", value: "1; mode=block" },
  { key: "Referrer-Policy", value: "strict-origin-when-cross-origin" },
  {
    key: "Strict-Transport-Security",
    value: "max-age=63072000; includeSubDomains; preload",
  },
  {
    key: "Content-Security-Policy",
    value: "default-src 'self'; script-src 'self' 'unsafe-eval' 'unsafe-inline';",
  },
];
```

## Gotchas

- Always source NVM before running node/npm/pnpm commands in hooks
- `noUncheckedIndexedAccess` catches array/object undefined access
- Use `@/` path alias, never relative imports from deeply nested files
- `pnpm --filter` for workspace-scoped commands
- `vi.clearAllMocks()` in `afterEach` to prevent test pollution
- QueryClient must have `retry: false` in test configs
- Check `typeof window !== "undefined"` before accessing localStorage (SSR safety)

## Common Mistakes (WRONG → RIGHT)

### Path alias imports

```typescript
// WRONG — relative imports from deeply nested files
import { Button } from "../../../components/ui/button";

// RIGHT — use @/ path alias configured in tsconfig
import { Button } from "@/components/ui/button";
```

### Test QueryClient retry

```typescript
// WRONG — tests retry failed queries, causing flaky timeouts
const queryClient = new QueryClient();

// RIGHT — disable retry in test QueryClient
const queryClient = new QueryClient({
  defaultOptions: { queries: { retry: false } },
});
```

### Mock cleanup

```typescript
// WRONG — mock state leaks between tests
afterEach(() => {
  // nothing
});

// RIGHT — clear all mocks to prevent test pollution
afterEach(() => {
  vi.clearAllMocks();
});
```

### SSR localStorage access

```typescript
// WRONG — crashes during SSR when window is undefined
const theme = localStorage.getItem("theme");

// RIGHT — guard with typeof check for SSR safety
const theme = typeof window !== "undefined" ? localStorage.getItem("theme") : null;
```
