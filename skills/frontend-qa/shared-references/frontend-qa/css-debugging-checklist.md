# CSS Debugging Checklist

## Category 1: Flexbox and Grid

- Check: children overflow flex parent → `flex-shrink: 0` or `min-width` prevents shrinking
- Check: `gap` has no visible effect → parent is not `display: flex` or `display: grid`
- Check: `align-items: center` not centering → child has `align-self` override
- Check: grid items wrap unexpectedly → `grid-template-columns` defines fewer columns than children (implicit grid)
- Check: grid column collapses to 0 width → `fr` unit with no intrinsic content and no `minmax()`
- Check: single flex child not centered → `justify-content: space-between` pushes lone child to start

## Category 2: Z-Index Stacking Context

- Check: `z-index` has no effect → element lacks `position: relative/absolute/fixed/sticky` (or not flex/grid child)
- Check: child z-index trapped below sibling → parent creates stacking context via `transform`, `filter`, `opacity < 1`, `will-change`, or `contain: paint`
- Check: modal behind page content → z-index set on overlay content but not on portal root
- Rule: `isolation: isolate` creates stacking context without visual side effects

## Category 3: Overflow Clipping

- Check: absolute-positioned child cut off → parent has `overflow: hidden`
- Check: `position: sticky` not working → ancestor has `overflow: hidden` or `overflow: auto`
- Check: scrollbar appears when content fits → padding, borders, or margin collapse adds hidden size
- Check: `text-overflow: ellipsis` not showing → missing `overflow: hidden` + `white-space: nowrap` + explicit width

## Category 4: Box Model

- Check: element larger than expected → `box-sizing: content-box` (default) adds padding/border outside width
- Check: third-party component sized wrong → may use `content-box` while project uses `border-box`
- Check: horizontal overflow with `width: 100%` → margin is outside box in both models
- Rule: `outline` does not affect layout; `border` does (shifts adjacent elements)

## Category 5: Responsive Breakpoints

- Check: layout breaks at tablet width → missing intermediate breakpoint between mobile and desktop
- Check: element visible when should be hidden → `hidden md:block` = hidden below 768px, visible above
- Check: Tailwind breakpoint and media query conflict → Tailwind uses `min-width`; `max-width` queries can overlap
- Check: `@container` query not matching → parent lacks `container-type` declaration

## Category 6: Positioning

- Check: `position: absolute` element in wrong location → no positioned ancestor; positions relative to viewport
- Check: `position: fixed` moves with scroll → ancestor has `transform`, changing containing block
- Check: `position: sticky` not sticking → missing `top`/`bottom` value or no scrollable overflow ancestor
- Check: sticky in flex container stretches full height → parent needs `align-self: start`

## Category 7: Margin Collapse

- Check: vertical gap smaller than expected → adjacent margins collapse (larger wins, not sum)
- Check: child margin leaks outside parent → parent has no padding, border, or BFC trigger
- Fix: add `overflow: hidden`, `display: flow-root`, or `padding: 1px` to parent to prevent collapse
- Rule: flexbox and grid containers prevent margin collapse between children

## Category 8: CSS Variables and Tokens

- Check: property using `var()` silently fails → variable undefined; evaluates to `initial`
- Check: Tailwind `theme()` vs CSS `var()` mismatch → `theme()` resolves at build; `var()` at runtime
- Check: dark mode not applying → `class` strategy needs `.dark` on ancestor; `media` uses `prefers-color-scheme`
- Check: CSS Module variable unavailable in another module → scope is local; shared vars go in `globals.css`

## Tailwind-Specific Patterns

| Pattern | Problem | Resolution |
|---------|---------|------------|
| `p-4 px-2` both present | Conflicting padding | Use `cn()`/`tailwind-merge` for last-wins dedup |
| `text-gray-900` no `dark:` variant | Invisible text on dark backgrounds | Add `dark:text-gray-100` |
| `text-${color}-500` template literal | Purged by scanner (cannot detect) | Use full class strings or `safelist` |
| `w-[200px]` arbitrary value | Bypasses design system | Check if standard token fits (`w-48`) |
| `!p-4` important modifier | Overrides all cascade | Avoid unless overriding third-party |

## CSS Modules + Server Components

- Rule: CSS Modules work in server and client components (applied at build time)
- Rule: global CSS can only be imported in root `layout.tsx`, not individual components
- Check: dynamic class switching in server component → requires client state, needs `"use client"`
- Rule: module class names scoped (no cross-file conflicts); global style conflicts remain possible
- Rule: `composes` resolves at build time; works identically in server and client components
