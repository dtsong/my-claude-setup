# Tailwind Conflict Map

## Utility-to-CSS-Property Mapping

When two classes on the same element target the same CSS property, flag as conflict.

| CSS Property | Tailwind Utilities (conflict group) |
|---|---|
| `display` | `block`, `inline-block`, `inline`, `flex`, `inline-flex`, `grid`, `inline-grid`, `hidden`, `table`, `contents` |
| `position` | `static`, `fixed`, `absolute`, `relative`, `sticky` |
| `width` | `w-*` (all width utilities) |
| `height` | `h-*` (all height utilities) |
| `min-width` / `max-width` | `min-w-*` / `max-w-*` |
| `min-height` / `max-height` | `min-h-*` / `max-h-*` |
| `padding` (all) | `p-*` — conflicts with `px-*`, `py-*`, `pt-*`, `pr-*`, `pb-*`, `pl-*`, `ps-*`, `pe-*` |
| `padding-x` | `px-*` — conflicts with `pl-*`, `pr-*`, `ps-*`, `pe-*` |
| `padding-y` | `py-*` — conflicts with `pt-*`, `pb-*` |
| `margin` (all) | `m-*` — conflicts with `mx-*`, `my-*`, `mt-*`, `mr-*`, `mb-*`, `ml-*`, `ms-*`, `me-*` |
| `margin-x` | `mx-*` — conflicts with `ml-*`, `mr-*`, `ms-*`, `me-*` |
| `margin-y` | `my-*` — conflicts with `mt-*`, `mb-*` |
| `color` | `text-{color}-*` (not `text-sm`, `text-lg` which are font-size) |
| `font-size` | `text-xs`, `text-sm`, `text-base`, `text-lg`, `text-xl`, `text-2xl` ... `text-9xl` |
| `font-weight` | `font-thin`, `font-light`, `font-normal`, `font-medium`, `font-semibold`, `font-bold`, `font-extrabold`, `font-black` |
| `text-align` | `text-left`, `text-center`, `text-right`, `text-justify`, `text-start`, `text-end` |
| `background-color` | `bg-{color}-*` |
| `border-radius` (all) | `rounded`, `rounded-*` — conflicts with `rounded-t-*`, `rounded-b-*`, `rounded-l-*`, `rounded-r-*`, `rounded-tl-*`, etc. |
| `border-width` | `border`, `border-*` (width variants) |
| `border-color` | `border-{color}-*` |
| `flex-direction` | `flex-row`, `flex-col`, `flex-row-reverse`, `flex-col-reverse` |
| `justify-content` | `justify-start`, `justify-end`, `justify-center`, `justify-between`, `justify-around`, `justify-evenly` |
| `align-items` | `items-start`, `items-end`, `items-center`, `items-baseline`, `items-stretch` |
| `gap` (all) | `gap-*` — conflicts with `gap-x-*`, `gap-y-*` |
| `overflow` (all) | `overflow-*` — conflicts with `overflow-x-*`, `overflow-y-*` |
| `z-index` | `z-*` (all z-index utilities) |
| `opacity` | `opacity-*` |
| `box-shadow` | `shadow`, `shadow-*` |
| `ring` | `ring`, `ring-*` (width) — separate from `ring-{color}-*` |
| `outline` | `outline`, `outline-*` |
| `transform` | `scale-*`, `rotate-*`, `translate-x-*`, `translate-y-*`, `skew-*` |
| `transition-property` | `transition`, `transition-all`, `transition-colors`, `transition-opacity`, `transition-shadow`, `transition-transform` |
| `grid-template-columns` | `grid-cols-*` |
| `grid-template-rows` | `grid-rows-*` |
| `grid-column` | `col-span-*`, `col-start-*`, `col-end-*` |
| `flex` (shorthand) | `flex-1`, `flex-auto`, `flex-initial`, `flex-none` |
| `cursor` | `cursor-*` |
| `pointer-events` | `pointer-events-none`, `pointer-events-auto` |
| `object-fit` | `object-contain`, `object-cover`, `object-fill`, `object-none`, `object-scale-down` |

## Axis Overlap Rules

Shorthand utilities conflict with their axis-specific or side-specific variants:
- `p-4 px-8` → NOT a conflict. `px-8` overrides horizontal, `p-4` supplies vertical. Result: `py-4 px-8`. Flag as WARNING only if both exist without clear intent.
- `p-4 pt-2` → NOT a conflict. `pt-2` overrides top only. Intentional.
- `p-4 p-8` → DEFINITE conflict. Same property, different values. Last wins in source order but `cn()`/tailwind-merge resolves to the last one.
- `m-4 mx-auto` → NOT a conflict. Common centering pattern.

## cn() / clsx() / classnames() Parsing Rules

| Expression Pattern | Classification |
|---|---|
| String literal: `cn("p-4", "flex")` | Always-applied |
| Variable: `cn(baseClasses, props.className)` | Always-applied (assume truthy) |
| `&&` guard: `cn("p-4", isLarge && "p-8")` | Conditionally-applied |
| Ternary: `cn(active ? "bg-blue-500" : "bg-gray-500")` | Mutually exclusive (no conflict between branches) |
| Object: `clsx({ "p-4": true, "p-8": isLarge })` | Boolean keys: `true` = always, variable = conditional |
| Spread: `cn(...classes)` | Unknown — cannot analyze statically, skip with warning |

**Conflict classification:**
- Two always-applied classes targeting same property → FLAGGED (definite conflict)
- Always-applied + conditionally-applied targeting same property → FLAGGED as WARNING (potential override issue)
- Two conditionally-applied in mutually exclusive branches → CLEAR (no conflict)
- Two conditionally-applied with unknown conditions → SKIPPED (cannot determine statically)

## Dark Mode Completeness

Color-related utility prefixes that should have `dark:` counterparts:
`text-`, `bg-`, `border-`, `ring-`, `shadow-`, `outline-`, `placeholder-`, `accent-`, `caret-`, `fill-`, `stroke-`, `decoration-`

**Detection:** Project uses dark mode if `tailwind.config` has `darkMode` set OR `dark:` classes appear elsewhere in the codebase.

- Check: color class without `dark:` counterpart → FLAGGED as WARNING
- Check: `dark:` variant identical to base (e.g., `text-gray-900 dark:text-gray-900`) → FLAGGED (likely copy-paste error)
- Check: `dark:` variant with insufficient contrast on dark background → FLAGGED

## Responsive Breakpoint Rules

Tailwind is mobile-first. Breakpoints apply at that width AND above.

- `md:flex` already covers `lg:`, `xl:`, `2xl:` → explicitly adding `lg:flex xl:flex` is redundant (INFO only)
- Layout-changing utilities without any responsive variant → FLAGGED as INFO if the component is in a `page-layout` or `section` role
- Responsive class order has no functional impact (Tailwind generates styles by breakpoint) but flag for readability
- Check: layout utility at one breakpoint with no adjacent coverage (e.g., `md:grid-cols-2` but no `lg:` variant) → INFO
