# Rendering & State Checks

## Key Prop Issues

- Check: Array `.map()` without `key` or using array index as `key` on a list that reorders/filters → component re-mounts lose local state, cause flicker
- Check: `key` prop changes on every render (e.g., `key={Math.random()}` or `key={Date.now()}`) → forces unmount/remount each render cycle
- Check: Missing `key` on sibling elements returned from conditional branches → React reuses DOM and carries stale state across branches

## Stale Closures in Hooks

- Check: `useEffect` callback references a state/prop variable but the deps array omits it → callback uses stale value from initial render
- Check: `useCallback` wraps a function that reads state but deps array is `[]` → memoized function never sees state updates
- Check: Event handler defined inside component reads state but is passed as prop to a memoized child (`React.memo`) → child never re-renders, handler has stale closure
- Check: `setInterval` or `setTimeout` in `useEffect` captures state at creation time without cleanup+recreation on state change → timer callback reads stale state

## Effect Dependencies

- Check: `useEffect` deps include an object or array literal created during render (e.g., `[{ id: 1 }]`) → new reference every render, effect runs infinitely
- Check: `useEffect` with no deps array (runs every render) performing expensive work or setting state → infinite re-render loop
- Check: `useEffect` sets state that triggers a re-render that changes a dep of the same effect → infinite loop
- Check: `useEffect` cleanup function missing for subscriptions, timers, or event listeners → memory leak or stale listener fires after unmount

## Hydration Mismatches (App Router)

- Check: Server component renders content based on `Date.now()`, `Math.random()`, or `typeof window` → server HTML differs from client render, hydration mismatch
- Check: `useEffect` or `useState` with browser-only initial value (e.g., `useState(window.innerWidth)`) without `"use client"` directive → crashes on server or hydration mismatch
- Check: Conditional rendering based on `typeof window !== 'undefined'` wrapping layout-affecting content → server renders one layout, client renders another, DOM mismatch
- Check: Third-party script or browser extension injects DOM elements between server render and hydration → mismatch warning, may cause content to disappear

## Re-render & Performance

- Check: Parent component re-renders on every keystroke (e.g., form input state in parent) causing expensive child tree to re-render → visible lag or flicker
- Check: Context provider value is a new object literal each render (e.g., `value={{ user, theme }}`) → all consumers re-render on every provider render
- Check: Component passes inline arrow function as prop to `React.memo` child → memo is defeated, child re-renders every time

## Controlled vs Uncontrolled

- Check: Input has both `value` (controlled) and `defaultValue` (uncontrolled) → React warns, behavior is unpredictable
- Check: `value` prop on input without `onChange` handler → input appears frozen (read-only without `readOnly` prop)
- Check: Component switches between controlled (`value={x}`) and uncontrolled (`value={undefined}`) across renders → React warning, input behavior breaks

## Conditional Rendering

- Check: `&&` short-circuit with falsy number (`{count && <Component />}` where count is `0`) → renders `0` instead of nothing
- Check: Conditional rendering causes hooks to run in different order across renders (hook inside an `if` block) → React hooks rule violation, crash
- Check: `Suspense` boundary missing around component using `use()` or lazy-loaded via `React.lazy`/`next/dynamic` → unhandled promise, blank render

## Server/Client Boundary

- Check: Component uses hooks (`useState`, `useEffect`, etc.) but is missing `"use client"` directive → build error or runtime crash in App Router
- Check: Server component directly imports a client-only library (e.g., `framer-motion`, `react-dnd`) without `"use client"` → build error
- Check: Props passed from server component to client component include non-serializable values (functions, class instances, Dates) → serialization error at the server/client boundary
- Check: Client component wraps server component children incorrectly — server components can be passed as `children` props to client components, but cannot be directly imported inside a `"use client"` file
