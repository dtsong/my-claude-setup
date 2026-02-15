# Next.js App Router Gotchas

## Hydration Mismatches

- Check: `typeof window !== 'undefined'` in render path → server/client output diverges
- Check: `Date()`, `Date.now()`, `Math.random()` in render → non-deterministic mismatch
- Check: `navigator`, `localStorage`, `window.innerWidth` in render → crashes or diverges on server
- Check: invalid HTML nesting (`<p>` in `<p>`, `<div>` in `<a>`) → browser auto-corrects differently than server
- Check: CSS-in-JS without SSR config → styles inject client-side only, flash of unstyled content
- Check: `suppressHydrationWarning` on containers → hides real bugs (valid only on leaf nodes for timestamps)
- Note: browser extensions (`cz-shortcut-listen`, `data-grammarly`) inject attributes causing benign warnings
- Note: iOS auto-detects phone numbers/emails, wrapping in `<a>` tags absent from server HTML

## Server/Client Boundary

- Check: hooks (`useState`, `useEffect`, `useRef`, `useContext`) in file without `"use client"` → runtime error
- Check: non-serializable props crossing boundary (functions, Dates, Maps, Sets, classes) → serialization error
- Check: event handlers (`onClick`, `onChange`) without `"use client"` on component or ancestor → runtime error
- Check: context provider without `"use client"` → fails because providers use state internally
- Check: third-party component without `"use client"` that uses hooks → throws in server context
- Rule: `"use client"` marks the boundary; everything imported by a client component is also client
- Rule: component without `"use client"` imported by client component becomes client implicitly
- Rule: `"use server"` on a function creates a server action, not a server component

## Loading and Error States

- Check: missing `loading.tsx` for route with data fetching → page blocks until all data resolves (no streaming)
- Check: `error.tsx` without `"use client"` directive → error boundary fails (it requires state)
- Check: `error.tsx` trying to catch `layout.tsx` errors in same segment → cannot catch; needs parent segment
- Check: `not-found.tsx` expected to catch 404 API responses → only triggers from `notFound()` calls
- Rule: `loading.tsx` wraps `page.tsx` of its own segment in `<Suspense>`, not child segments
- Rule: nested `loading.tsx` overrides parent loading state for that segment only
- Rule: `template.tsx` re-mounts on navigation (unlike `layout.tsx`); use for per-page state resets

## Data Fetching and Caching

- Check: `fetch()` in server component without cache option → cached by default; stale data if not intended
- Check: data mutation without `revalidatePath()`/`revalidateTag()` → stale reads after write
- Check: sequential `await` for independent fetches → use `Promise.all()` for parallel execution
- Check: expecting `revalidatePath()` to clear client Router Cache → it only purges server-side cache
- Rule: `cache: 'no-store'` opts out of fetch caching; `revalidate: 0` opts out for ISR
- Rule: Router Cache caches visited pages for 30s (dynamic) or 5min (static); `router.refresh()` clears current route
- Rule: `unstable_cache()` caches function results across requests, not `fetch()` calls

## Metadata

- Check: both `layout.tsx` and `page.tsx` export `metadata` with same field → duplicate `<meta>` tags
- Check: dynamic title using static `metadata` export instead of `generateMetadata()` → title does not update
- Rule: child `generateMetadata()` merges with parent; explicit fields override parent
- Rule: `opengraph-image.tsx` file convention takes priority over metadata export
- Rule: child `metadata.robots` does not override root-level `robots.txt`

## Suspense Boundaries

- Check: `useSearchParams()` without `<Suspense>` wrapper → entire page opts into client-side rendering
- Check: missing `<Suspense>` around async server component → no streaming, blocks parent
- Rule: each `<Suspense>` boundary streams independently; nested boundaries resolve inside-out
- Rule: `dynamic(() => import('./X'), { ssr: false })` skips server rendering; use for browser-only components
- Rule: Suspense fallbacks may flash during client navigation if data resolves faster than transition
