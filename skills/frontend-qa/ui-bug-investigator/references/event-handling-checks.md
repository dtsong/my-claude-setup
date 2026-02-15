# Event Handling Checks

## Handler Binding

- Check: `onClick={handleClick()}` with parentheses → function is called during render, return value (probably `undefined`) is bound as handler. Fix: `onClick={handleClick}`
- Check: Class-based handler without `.bind(this)` or arrow function → `this` is undefined inside handler (legacy pattern, rare in modern React)
- Check: Handler references a state setter but component is server-rendered without `"use client"` → handlers cannot be attached to server components, click does nothing
- Check: `onClick` on a `<div>` or `<span>` without `role` and `tabIndex` → element is not focusable, click works but keyboard users cannot activate it

## Event Propagation

- Check: `e.stopPropagation()` on an inner element prevents a parent handler from firing → user reports "clicking X does nothing" when the parent is the actual listener
- Check: Portal-rendered content (modals, dropdowns, tooltips via `createPortal`) fires events at the portal mount point, not the React tree position → parent `onClick` does not receive events from portal children
- Check: `e.preventDefault()` on a form submit handler is missing → form submits to server, page reloads, state lost
- Check: Event listener added via `document.addEventListener` in `useEffect` without corresponding `removeEventListener` in cleanup → duplicate handlers accumulate on re-renders

## Focus Management

- Check: Modal or dialog opens but focus does not move into it → keyboard user is stuck behind the overlay. Look for missing `autoFocus`, missing `ref.focus()` in `useEffect`, or Radix/headless UI focus trap not configured
- Check: After closing a modal/dropdown, focus does not return to the trigger element → focus lands on `<body>`, screen reader user loses position
- Check: `tabIndex={-1}` on an element that should be tabbable → element is focusable programmatically but skipped in tab order
- Check: Multiple elements with `tabIndex > 0` → tab order does not follow DOM order, navigation is confusing

## Keyboard Navigation

- Check: Custom interactive element (dropdown, combobox, toggle) only responds to `onClick`, missing `onKeyDown` for Enter/Space → keyboard users cannot activate
- Check: `onKeyDown` handler checks `e.key === "Enter"` but not `e.key === " "` (Space) → buttons activated by Enter but not Space, violates WAI-ARIA expectations
- Check: Escape key does not close modal/popover/dropdown → user cannot dismiss without clicking outside, which may not work for keyboard-only users
- Check: Arrow key navigation in a list or menu is not implemented → Tab cycles through every item instead of arrow keys moving within the group

## Form Events

- Check: `onSubmit` handler on `<form>` does not call `e.preventDefault()` in client-side form handling → full page reload
- Check: `onChange` fires on every keystroke for a text input triggering expensive re-renders → use `onBlur` for validation or debounce the handler
- Check: `<input type="number">` `onChange` receives `e.target.value` as string, not number → comparison bugs downstream (e.g., `"5" > "10"` is `true`)
- Check: File input `onChange` does not fire when selecting the same file twice → browser optimization; clear the input value after processing to allow re-selection

## Server Actions (App Router)

- Check: Form uses `action={serverAction}` but also has `onSubmit` client handler → both fire; if `onSubmit` does not call `e.preventDefault()`, the server action runs alongside the client handler
- Check: `useFormStatus` hook used outside of a `<form>` with a server action → `pending` is always `false`, loading state never shows
- Check: `useFormState` initial state type does not match server action return type → TypeScript may not catch this if types are loosely defined, causing runtime shape mismatch
- Check: Server action mutates data but does not call `revalidatePath()` or `revalidateTag()` → stale cached data persists after mutation, user sees old data

## Synthetic vs Native Events

- Check: Third-party library adds native DOM listener that conflicts with React's synthetic event system → event fires twice or in unexpected order
- Check: `onWheel`, `onTouchStart`, `onTouchMove` attached as React props are passive by default in React 17+ → calling `e.preventDefault()` throws a warning and has no effect. Use `ref` + `addEventListener` with `{ passive: false }` instead
- Check: `onScroll` on a non-scrollable element → handler never fires; verify the element has `overflow: auto/scroll` and content exceeds its bounds
