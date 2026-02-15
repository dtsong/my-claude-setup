# Stacking & Viewport Checks

## Stacking & Paint

### Z-Index Audit

- Check: `z-index` set on element without stacking context → `z-index` only works on positioned elements (`relative`, `absolute`, `fixed`, `sticky`) or flex/grid children. On a `static` element, `z-index` has no effect.
- Check: `z-index` competing across different stacking contexts → elements in separate stacking contexts cannot interleave. A `z-index: 9999` child inside a `z-index: 1` parent will never appear above a `z-index: 2` sibling of the parent. Identify stacking context boundaries.
- Check: stacking context created unintentionally by `transform`, `filter`, `opacity < 1`, `will-change`, `mix-blend-mode`, `isolation: isolate`, `contain: paint/layout` → these all create new stacking contexts. If a modal or dropdown appears behind another element, look for these properties on ancestors.
- Check: Tailwind `z-*` values escalating across components → suggests missing `isolation: isolate` (Tailwind: `isolate`) to scope z-index. Without isolation, z-index values leak across component boundaries.
- Check: `z-index` on flex/grid children without explicit `position` → works (flex/grid children participate in stacking regardless of position) but may confuse developers expecting `position: relative` to be required.

### Overflow Clipping

- Check: `overflow: hidden` on parent clips `position: absolute` child → clipping only occurs if the `overflow: hidden` ancestor is also a containing block (`position` other than `static`). If parent is `static`, absolute children escape to the next positioned ancestor.
- Check: `overflow: hidden` on flex/grid container → may clip content that extends beyond the container. Common with dynamically sized content, tooltips, or dropdown menus that should overflow the container.
- Check: `overflow-x: hidden` on `<body>` or page container → hides horizontal scrollbar but may break `position: sticky` and create clipping issues for modals/drawers.
- Check: `overflow: auto` causing unexpected scrollbar → element's content exceeds container, creating a scroll region. Often unintentional with percentage-based heights or dynamic content.
- Check: `text-overflow: ellipsis` requires three conditions → `overflow: hidden` + `white-space: nowrap` + explicit width constraint. Missing any one means no ellipsis. Tailwind: `truncate` utility applies all three.

### Compositing Layers

- Check: `will-change: transform` (or any `will-change`) on many elements → each creates a compositing layer, consuming GPU memory. Use sparingly and remove after animation completes.
- Check: `transform: translateZ(0)` or `translate3d(0,0,0)` used as "GPU acceleration hack" → creates compositing layer unnecessarily. Only use when actual transform animation is happening.
- Check: `filter: blur()` or `backdrop-filter` on parent → creates containing block for fixed-position descendants (breaking their positioning) and creates a new stacking context.
- Check: animation on `width`, `height`, `top`, `left`, `margin`, `padding` → triggers layout recalculation every frame. Prefer `transform` (translate, scale) and `opacity` which only trigger composite. Tailwind: `transition-transform` instead of `transition-all`.

## Viewport & Responsiveness

### Viewport Units

- Check: `height: 100vh` on mobile → `100vh` does not account for mobile browser chrome (address bar, bottom bar). Use `100dvh` (dynamic viewport height) or `100svh` (small viewport height). Tailwind v3.4+: `h-dvh`, `h-svh`.
- Check: `width: 100vw` → includes scrollbar width on desktop, causing horizontal overflow. Use `width: 100%` instead, which excludes scrollbar. Tailwind: prefer `w-full` over `w-screen`.
- Check: `svh`/`dvh`/`lvh` without fallback → older browsers do not support these units. Provide a `vh` fallback: `height: 100vh; height: 100dvh;`
- Check: viewport units in `calc()` with fixed values → `calc(100vh - 64px)` has the same mobile chrome issue. Use `calc(100dvh - 64px)`.

### Container Queries

- Check: `@container` query without `container-type` on the ancestor → container queries require the ancestor to declare `container-type: inline-size` (or `size`). Without it, the query never matches.
- Check: `container-type: size` causes zero-height collapse → `size` containment prevents the element from deriving height from its content. Use `inline-size` unless you explicitly control height.
- Check: mixing media queries and container queries for the same layout → pick one model. Media queries respond to viewport; container queries respond to parent width. Using both creates confusing breakpoint interactions.

### Breakpoint Coverage

- Check: component has layout-changing utility at only one breakpoint → e.g., `md:flex-col` but no `lg:` variant. The `md:` style persists at larger breakpoints (mobile-first). Verify this is intentional.
- Check: responsive visibility with `hidden md:block` pattern → `hidden md:block lg:hidden` creates show/hide/show which is likely unintentional. Verify toggle patterns are consistent across all breakpoints.
- Check: font-size or spacing jumps across breakpoints → e.g., `text-sm md:text-2xl` skips intermediate sizes. On `md` breakpoint the jump may be jarring. Consider `md:text-lg lg:text-xl xl:text-2xl` for smoother scaling.
- Check: `max-w-*` without responsive adjustment → `max-w-4xl` (56rem) may leave excessive margins on wide screens. Consider responsive max-width or Tailwind's `container` utility.
- Check: `grid-cols-*` without responsive variants → a `grid-cols-3` grid that does not reduce to `grid-cols-1` or `grid-cols-2` on small viewports will overflow or produce tiny columns. Flag if component `layout_role` is `section` or `page-layout`.
- Check: padding/margin at fixed values that become disproportionate on mobile → `px-16` (4rem / 64px) consumes too much width on a 375px mobile screen. Consider responsive padding: `px-4 md:px-8 lg:px-16`.
