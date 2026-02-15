# Data Flow Checks

## Props

- Check: Required prop is not passed by parent component → component receives `undefined`, renders nothing or crashes. Trace the prop from parent render JSX to child type definition
- Check: Prop name mismatch between parent and child (e.g., parent passes `userData`, child expects `user`) → child receives `undefined`. Check TypeScript types — if props are typed as `any` or loosely, TS will not catch this
- Check: Prop is passed but as wrong type (string where number expected, e.g., `id="5"` vs `id={5}`) → comparison with `===` fails, filtering breaks
- Check: Prop drilling through 3+ levels where an intermediate component does not forward the prop → value lost mid-chain. Trace each level to confirm `{...props}` or explicit forwarding

## Context

- Check: `useContext(MyContext)` returns `undefined` → component is outside the provider. Trace up the component tree in the ComponentMap to verify a `<MyContext.Provider>` ancestor exists
- Check: Context provider is inside a client component but consumer is in a server component → server components cannot use `useContext`. The consumer needs `"use client"`
- Check: Context provider re-creates the value object on every render (e.g., `value={{ user, theme }}` inline) → all consumers re-render on every provider render, even if user/theme have not changed
- Check: Multiple providers of the same context at different tree levels → consumer reads from the nearest ancestor provider, which may not be the one the developer intended

## Server/Client Serialization (App Router)

- Check: Server component passes a function as prop to a client component → serialization error ("Functions cannot be passed directly to Client Components")
- Check: Server component passes a `Date` object as prop to a client component → serialized as string, client receives string not Date. Use `.toISOString()` explicitly
- Check: Server component passes a `Map`, `Set`, `RegExp`, or class instance as prop → not serializable, throws at the boundary
- Check: `fetch` in server component returns data with circular references → JSON serialization to client fails
- Check: Server action receives `FormData` but accesses a field that was not in the form → returns `null`, not `undefined`; downstream code may not handle `null`

## Async Data & Suspense

- Check: `async` server component fetches data that returns `null` or `undefined` on error → component renders with null data, child components crash on `.map()` or property access
- Check: `fetch()` in server component without error handling → unhandled rejection crashes the route segment. Wrap in try/catch or use `error.tsx` boundary
- Check: Component uses `React.use(promise)` but no `<Suspense>` boundary exists above it → unhandled suspense, white screen
- Check: `loading.tsx` exists but is placed in the wrong route segment → loading state never shows for the intended page. Verify file is a sibling of `page.tsx` in the same directory
- Check: `fetch()` in server component is cached by Next.js full route cache → data appears stale. Check `{ cache: 'no-store' }` option or `revalidate` settings

## Null/Undefined Handling

- Check: Optional chaining (`?.`) used on the access but not on the method call → `data?.items.map()` crashes if `data` is defined but `items` is `undefined`. Should be `data?.items?.map()`
- Check: Nullish coalescing (`??`) confused with OR (`||`) → `value ?? fallback` only catches `null`/`undefined`; `value || fallback` also catches `0`, `""`, `false`
- Check: API response shape changed (field renamed, nested differently) but component destructuring uses old shape → destructured value is `undefined`, no TypeScript error if API response is typed as `any`
- Check: Array `.find()` result used without null check → `.find()` returns `undefined` when no match, property access on `undefined` crashes

## State Management

- Check: Zustand/Jotai store read in a server component → store is client-side only; server component gets initial/default value, not current state
- Check: TanStack Query / SWR `useQuery` hook with a key that changes on every render (includes a new object or array literal) → cache is never hit, data refetches on every render
- Check: State updated inside `useEffect` without deps → re-render triggers effect, effect updates state, state triggers re-render → infinite loop
- Check: Optimistic update in mutation handler assumes success but server rejects → UI shows stale optimistic value until next refetch

## Route & Navigation Data

- Check: `useSearchParams()` used without `<Suspense>` boundary in App Router → warning in dev, potential crash in production; Next.js 14+ requires Suspense around `useSearchParams()`
- Check: `useRouter().push()` with query params does not trigger `useSearchParams()` re-read in the target page → component renders with stale params from the previous route
- Check: Dynamic route param (`params.id`) type is always `string` → numeric comparison or lookup fails if downstream code expects a number. Cast explicitly
- Check: `generateStaticParams()` does not include the accessed param value → 404 in production (static export) even though it works in dev mode
