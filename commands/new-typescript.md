# New TypeScript Project Setup

Initialize a TypeScript project with opinionated tooling (pnpm, Next.js, Vitest, Prettier) and conventions.

> For full convention details, see `~/.claude/skills/language-conventions/references/typescript.md`

## Stack

- **Runtime**: Node 22+
- **Package manager**: pnpm
- **Framework**: Next.js 14+ (App Router)
- **Styling**: Tailwind CSS + shadcn/ui
- **Testing**: Vitest + React Testing Library
- **Formatting**: Prettier
- **TypeScript**: Strict mode + noUncheckedIndexedAccess

## Setup Steps

1. Initialize Next.js project:
```bash
source ~/.nvm/nvm.sh && nvm use default --silent
pnpm create next-app <project-name> --typescript --tailwind --eslint --app --src-dir --import-alias "@/*"
cd <project-name>
```

2. Add dev dependencies:
```bash
pnpm add -D vitest @vitest/coverage-v8 @vitejs/plugin-react jsdom @testing-library/react @testing-library/jest-dom @testing-library/user-event prettier
```

3. Add runtime dependencies:
```bash
pnpm add @tanstack/react-query clsx tailwind-merge class-variance-authority zod zustand
```

4. Create/update `tsconfig.json`:
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

5. Add scripts to `package.json`:
```json
{
  "scripts": {
    "dev": "next dev",
    "build": "next build",
    "start": "next start",
    "lint": "next lint",
    "format": "prettier --write \"src/**/*.{ts,tsx,js,jsx,json,css,md}\"",
    "format:check": "prettier --check \"src/**/*.{ts,tsx,js,jsx,json,css,md}\"",
    "typecheck": "tsc --noEmit",
    "test": "vitest run",
    "test:watch": "vitest",
    "test:coverage": "vitest run --coverage"
  }
}
```

6. Create `vitest.config.mts`:
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
      exclude: [
        "src/**/*.test.ts",
        "src/**/*.test.tsx",
        "src/**/__tests__/**",
        "src/app/**",
      ],
    },
  },
  resolve: {
    alias: {
      "@": path.resolve(__dirname, "./src"),
    },
  },
});
```

7. Create `src/test/setup.ts`:
```typescript
import "@testing-library/jest-dom/vitest";
```

8. Create `.prettierrc`:
```json
{
  "semi": true,
  "singleQuote": false,
  "trailingComma": "all",
  "printWidth": 100
}
```

9. Create `.pre-commit-config.yaml`:
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
        exclude: pnpm-lock.yaml

      - id: typecheck
        name: TypeScript typecheck
        entry: bash -c 'source ~/.nvm/nvm.sh && nvm use default --silent && pnpm typecheck'
        language: system
        types_or: [ts, tsx]
        pass_filenames: false
```

10. Create `src/lib/utils.ts`:
```typescript
import { type ClassValue, clsx } from "clsx";
import { twMerge } from "tailwind-merge";

export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}
```

11. Create `src/app/providers.tsx`:
```tsx
"use client";

import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { useState } from "react";

export function Providers({ children }: { children: React.ReactNode }) {
  const [queryClient] = useState(
    () =>
      new QueryClient({
        defaultOptions: {
          queries: {
            staleTime: 60 * 1000,
            gcTime: 5 * 60 * 1000,
            retry: 1,
          },
        },
      }),
  );

  return (
    <QueryClientProvider client={queryClient}>
      {children}
    </QueryClientProvider>
  );
}
```

12. Update `src/app/layout.tsx` to wrap with Providers:
```tsx
import type { Metadata } from "next";
import { Providers } from "./providers";
import "./globals.css";

export const metadata: Metadata = {
  title: "<Project Name>",
  description: "<Project description>",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>
        <a href="#main-content" className="sr-only focus:not-sr-only">
          Skip to content
        </a>
        <Providers>
          <main id="main-content">{children}</main>
        </Providers>
      </body>
    </html>
  );
}
```

13. Create initial test structure:
```
src/
├── test/
│   └── setup.ts
├── lib/
│   └── utils.ts
├── components/
│   └── ui/          # shadcn/ui components go here
└── app/
    ├── layout.tsx
    ├── providers.tsx
    └── page.tsx
```

14. Create `.gitignore` (extend Next.js default):
```
node_modules/
.next/
dist/
coverage/
```

15. Create project CLAUDE.md:
```markdown
# <Project Name>

## What This Is
<1-2 sentence description>

## Key Docs
- `/docs/CODEMAP.md` — Codebase structure and quick reference
- Convention reference: `~/.claude/skills/language-conventions/references/typescript.md`

## Quick Context
- Frontend: Next.js 14+ (App Router), TypeScript, Tailwind CSS
- UI: shadcn/ui + Radix primitives
- State: Zustand (client), React Query (server)

## Tooling

### TypeScript
- **pnpm** - Package manager (`pnpm install`, `pnpm add`)
- **Vitest** - Testing (`pnpm test`, `pnpm test:coverage`)
- **Prettier** - Formatting (`pnpm format`)
- **TypeScript** - Type checking (`pnpm typecheck`)

## Key Decisions
- <Decision 1>

## Testing
- All feature work must include unit tests
- Vitest + React Testing Library
- `vi.mock()` with factory functions

## Git Workflow
- <Branch strategy>

## Current Focus
- <Current phase>
```

16. Initialize git and install pre-commit:
```bash
git init
pre-commit install
git add .
git commit -m "chore: initial project setup"
```

## Verification

```bash
source ~/.nvm/nvm.sh && nvm use default --silent
pnpm typecheck && pnpm test && pnpm build
```
