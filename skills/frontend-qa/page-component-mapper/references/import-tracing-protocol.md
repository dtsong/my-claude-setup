# Import Tracing Protocol

## Table of Contents

- [tsconfig Path Resolution](#tsconfig-path-resolution)
- [File Extension Resolution Order](#file-extension-resolution-order)
- [Barrel Export Handling](#barrel-export-handling)
- [Dynamic Import Handling](#dynamic-import-handling)
- [External Package Detection](#external-package-detection)
- [Server/Client Boundary Rules](#serverclient-boundary-rules)
- [Monorepo Handling](#monorepo-handling)
- [Style Import Classification](#style-import-classification)
- [Depth Limit Behavior](#depth-limit-behavior)

## tsconfig Path Resolution

1. Read `tsconfig.json`. If `extends` is present (e.g., `"extends": "./tsconfig.app.json"`), read the parent first and merge — child overrides parent.
2. Extract `compilerOptions.baseUrl` (default: project root) and `compilerOptions.paths`.
3. Path entries use glob patterns. Convert to directory mappings:
   - `"@/*": ["./src/*"]` means `@/components/Button` resolves to `./src/components/Button`
   - `"~/lib/*": ["./lib/*"]` means `~/lib/utils` resolves to `./lib/utils`
4. If multiple path entries match, try each in order until a file is found.
5. Also read `next.config.{js,mjs,ts}` for `webpack.resolve.alias` — these supplement tsconfig paths.

## File Extension Resolution Order

When an import specifies no extension, try in this order:
1. `{path}.tsx`
2. `{path}.ts`
3. `{path}.jsx`
4. `{path}.js`
5. `{path}/index.tsx`
6. `{path}/index.ts`
7. `{path}/index.jsx`
8. `{path}/index.js`

Stop at the first match.

## Barrel Export Handling

A barrel export is an `index.ts` that re-exports from other files:
```typescript
// components/index.ts
export { Button } from './Button'
export { Card } from './Card'
export { Input } from './Input'
```

When an import targets a barrel file:
1. Read the barrel `index.ts`.
2. Find the specific re-export matching the imported name.
3. Follow the re-export to the actual source file.
4. If the re-export target is another barrel, follow again (up to 5 levels).
5. At level 5, record as unresolved with reason `"barrel-depth-exceeded"`.

Watch for renamed re-exports:
```typescript
export { default as Button } from './ButtonBase'  // follow to ButtonBase
export { Input as TextInput } from './Input'       // follow to Input, note rename
```

## Dynamic Import Handling

| Pattern | Action |
|---------|--------|
| `next/dynamic(() => import('./Foo'))` | Trace `./Foo`, set `isDynamic: true` |
| `React.lazy(() => import('./Foo'))` | Trace `./Foo`, set `isDynamic: true` |
| `import('./Foo')` (top-level dynamic) | Trace `./Foo`, set `isDynamic: true` |
| `` import(`./locale/${lang}`) `` | Record as unresolved, reason: `"dynamic-computed"` |
| `import(variable)` | Record as unresolved, reason: `"dynamic-computed"` |

## External Package Detection

Classify an import as external and stop tracing when:
- Import specifier does not start with `.`, `..`, `@/`, `~/`, or any tsconfig path alias
- Import specifier starts with a known package scope: `react`, `next`, `@radix-ui`, `@tanstack`, `@mui`, `@headlessui`, `lucide-react`, `framer-motion`, `zod`, `date-fns`
- Import specifier resolves into `node_modules/`

Record external imports with `importType: "external"`. Note the package name for stack detection.

## Server/Client Boundary Rules

| Condition | Classification |
|-----------|---------------|
| File contains `'use client'` or `"use client"` in first 5 lines | `"client"` |
| File contains `'use server'` or `"use server"` in first 5 lines | `"server"` |
| File is in `app/` directory, no directive | `"server"` (App Router default) |
| File is in `components/`, `lib/`, `utils/`, no directive | `"shared"` |
| File is in `pages/` directory | `"client"` (Pages Router default) |

Boundary violations to flag (inform diagnostic skills):
- `"client"` component importing a `"server"`-only module
- `"server"` component using `useState`, `useEffect`, or other client hooks
- `"shared"` component using hooks (should be `"client"`)

## Monorepo Handling

1. Check `package.json` for `workspaces` field or check for `pnpm-workspace.yaml`.
2. Check `next.config.*` for `transpilePackages` — these are workspace packages Next.js will bundle.
3. When an import resolves to a workspace package, trace into it but cap at 3 levels deep within the package.
4. At the workspace depth limit, record as unresolved with reason `"workspace-boundary"`.

## Style Import Classification

| Import Pattern | `importType` | `styling_approach` |
|----------------|-------------|-------------------|
| `import './styles.css'` | `"style"` | Check for Tailwind directives |
| `import styles from './Foo.module.css'` | `"style"` | `"css-modules"` |
| `import styled from 'styled-components'` | `"external"` | `"styled-components"` |
| Tailwind classes in JSX `className="flex ..."` | (detected in JSX) | `"tailwind"` |
| `style={{ ... }}` in JSX | (detected in JSX) | `"inline"` |

## Depth Limit Behavior

At the configured depth limit (default 3):
- Record all remaining imports with `unresolved: true`, `unresolvedReason: "depth-limit"`
- Add each to the top-level `unresolvedImports` array
- Do NOT read the target files — this is the cost-saving mechanism
- In the summary output, report: `"{N} unresolved (depth-limit)"`

When the user requests `--depth N` with a higher N:
- Rebuild the entire map at the new depth (no incremental deepening)
- This is a full rebuild, same as `--fresh`
