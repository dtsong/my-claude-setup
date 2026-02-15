# Component Analysis Patterns

## Import Tracing

### Step 0: Resolve tsconfig Path Aliases

- Read `tsconfig.json` at project root; if `extends` present, follow chain and merge `compilerOptions.paths`
- Build lookup table: `{ "@/*": "./src/*", "~/*": "./lib/*" }`
- Check: `tsconfig.json` missing → warn and proceed with relative-only resolution

### Step 1: Identify Route Entry Point

| Router | Entry File | Also Check |
|--------|-----------|------------|
| App Router | `app/{route}/page.tsx` | `layout.tsx`, `loading.tsx`, `error.tsx`, `template.tsx`, `not-found.tsx` |
| Pages Router | `pages/{route}.tsx` | `_app.tsx`, `_document.tsx` |

### Step 2: Trace Imports (Depth-Limited)

- Relative path (`./foo`, `../bar`) → resolve against current file; try `.tsx`, `.ts`, `.jsx`, `.js`, `/index.tsx`, `/index.ts`
- Aliased path (`@/foo`, `~/bar`) → resolve using Step 0 lookup table
- Bare specifier (`react`, `next/link`, `@radix-ui/*`) → record as external dependency, stop tracing
- Dynamic import with literal path → resolve target, flag `isDynamic: true`
- Check: dynamic import with computed path → record as unresolved, reason: `dynamic-computed`
- Check: barrel export import from `index.ts` → follow re-export chain, cap at 5 levels; if exceeded, reason: `barrel-depth-exceeded`
- Check: at depth limit → record as unresolved, reason: `depth-limit`

### Step 3: Classify Completeness

| Classification | Condition |
|---------------|-----------|
| `full` | `unresolvedImports` array is empty |
| `shallow` | All unresolved imports have reason `depth-limit` only |
| `partial` | Unresolved imports include non-depth-limit reasons |

## Server/Client Boundary Detection

### Directive Rules

- Rule: `"use client"` must be the first expression in the file (before any imports)
- Rule: file without `"use client"` is a server component by default in App Router
- Rule: everything imported by a `"use client"` file becomes client bundle, even without its own directive
- Rule: `"use server"` on a file marks all exports as server actions, not server components
- Rule: `"use server"` inside a function body marks that single function as a server action

### Boundary Classification

| Signal | Classification |
|--------|---------------|
| `"use client"` directive present | `client` |
| No directive, no hooks, no event handlers | `server` |
| No directive but uses `useState`/`useEffect`/`useRef` | Error: will fail at runtime |
| No directive, imported only by client components | `client` (implicit, inherited) |
| No directive, imported by both server and client | `shared` (must not contain hooks or browser APIs) |

### Common Boundary Violations

- Check: server component imports module that calls `useEffect` deep in dependency chain → runtime error
- Check: client component passes function prop to server component → functions not serializable
- Check: context provider without `"use client"` → fails because providers use state internally
- Check: third-party library without `"use client"` that internally uses hooks → throws in server context

## Prop Flow Analysis

- Check: prop drilling deeper than 3 levels without context → suggests refactoring opportunity
- Check: spread props (`{...props}`) → hides which props are used, complicates debugging
- Check: optional prop without default value and no null check in render → runtime error
- Check: callback prop passed from server to client component → not serializable
- Check: object/array prop created inline in parent render → causes unnecessary child re-renders
- Check: `children` contains server components but parent is client component → needs composition pattern

## State Management Patterns

| Pattern | Detection Signal | Notes |
|---------|-----------------|-------|
| Local state | `useState`, `useReducer` | Scoped to component; re-renders on change |
| Context | `useContext`, `createContext` | Provider must be client; consumers re-render on any value change |
| URL state | `useSearchParams`, `usePathname` | Requires `<Suspense>` boundary |
| Server state | `fetch()` in server component | Cached by default; no re-render without revalidation |
| External store | `useSyncExternalStore`, Zustand, Jotai | Client-only; requires `"use client"` |
| Form state | `useFormState`, `useFormStatus` | Tied to server actions; `useFormStatus` must be in child of `<form>` |

## Re-render Cause Analysis

Check these causes in priority order:

1. Check: parent re-renders → child re-renders even if its props unchanged
2. Check: inline object/array props (`data={{ key: 'val' }}`) → new reference every render
3. Check: context value change → all consumers re-render
4. Check: missing `React.memo` → component receives stable props but re-renders anyway
5. Check: hook dependency creates new reference each render → `useEffect`/`useMemo`/`useCallback` re-fires
6. Check: state update inside `useEffect` without proper deps → infinite loop or extra renders
7. Check: parent changes `key` prop → forces full unmount and remount
