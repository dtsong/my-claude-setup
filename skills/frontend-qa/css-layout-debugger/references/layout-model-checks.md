# Layout Model Checks

## Flexbox

- Check: `display: flex` container without explicit `flex-direction` → defaults to `row`. If children stack vertically in the design, this is the bug. Tailwind: missing `flex-col`.
- Check: flex child overflows container → add `min-width: 0` (or `min-w-0`) to the child. Flex items default to `min-width: auto` which prevents shrinking below content size.
- Check: flex child does not grow to fill space → verify `flex-grow` or `flex: 1`. Tailwind: `flex-1` (sets `flex: 1 1 0%`) vs `grow` (sets `flex-grow: 1` only).
- Check: `flex: 1` vs `flex: 1 1 auto` → `flex: 1` uses `flex-basis: 0%` (distributes all space equally). `flex: 1 1 auto` uses content size as basis (distributes extra space). Common source of uneven flex children.
- Check: `align-items` vs `align-content` confusion → `align-items` aligns items within a single line. `align-content` aligns lines within the container (only matters with `flex-wrap`).
- Check: `justify-content: space-between` with single child → no spacing effect, child sits at start. Often a bug when expecting centering.
- Check: `gap` on flex container with `margin` on children → double spacing. Use one or the other.
- Check: `flex-wrap` without `flex-basis` or width on children → children may not wrap as expected. Each child needs a basis to trigger wrapping.
- Check: `order` property used without `flex` or `grid` parent → no effect.
- Check: `flex-shrink: 0` on all children in a `flex-wrap` container → nothing ever wraps.

## Grid

- Check: `grid-template-columns` with `fr` units but no explicit container width → `fr` distributes available space. If the container has no width constraint, the grid may behave unexpectedly.
- Check: implicit grid tracks → items placed beyond `grid-template-columns`/`rows` create implicit tracks. These use `grid-auto-columns`/`rows` sizing (default `auto`). If items appear in unexpected positions, check for implicit track creation.
- Check: `gap` with percentage-based column widths → gap is added to the total, potentially causing overflow. Use `fr` units or `calc()` to account for gaps.
- Check: `grid-column: span N` exceeding defined column count → creates implicit columns or wraps to next row unexpectedly.
- Check: `auto-fill` vs `auto-fit` → `auto-fill` creates empty tracks to fill space. `auto-fit` collapses empty tracks. If columns don't stretch to fill the container, switch from `auto-fill` to `auto-fit`.
- Check: `minmax(min, 1fr)` where `min` is too large → causes horizontal overflow on narrow viewports. Use `minmax(0, 1fr)` or a viewport-relative minimum.
- Check: `align-items: stretch` (grid default) with explicit child height → the explicit height wins, creating uneven row heights.
- Check: `grid-area` placement conflicts → two items assigned to the same grid area. Last in DOM order wins.

## Box Model

- Check: `box-sizing` inconsistency → most projects set `box-sizing: border-box` globally. If a component or library resets to `content-box`, padding and border add to the element's width/height. Tailwind sets `border-box` globally via preflight.
- Check: margin collapse between adjacent siblings → vertical margins collapse to the larger value. Adding `padding`, `border`, `overflow: hidden`, or `display: flex/grid` on the parent prevents collapse.
- Check: margin collapse between parent and first/last child → child's margin "escapes" the parent. Fix: add `padding`, `border`, or `overflow` on the parent. Tailwind: adding `p-px` or `overflow-hidden` to the parent.
- Check: negative margins pulling element outside parent → may be clipped by `overflow: hidden` on an ancestor.
- Check: percentage width/height without sized parent → percentage height requires the parent to have an explicit height. `height: 100%` on a child of `height: auto` parent has no effect.
- Check: `width: 100%` + `padding` or `border` on `content-box` element → total width exceeds parent. Fix: use `border-box` or `calc(100% - padding)`.
- Check: `inline` elements ignore `width`, `height`, `margin-top`, `margin-bottom` → switch to `inline-block` or `block`.

## Positioning

- Check: `position: absolute` without positioned ancestor → element positions relative to the viewport (initial containing block). Add `position: relative` to the intended parent. Tailwind: add `relative` to parent.
- Check: `position: sticky` fails → common causes: (1) no scrollable ancestor, (2) ancestor has `overflow: hidden` or `overflow: auto`, (3) ancestor is flex/grid and element is the only child, (4) no `top`/`bottom`/`left`/`right` value set. Tailwind: need both `sticky` and `top-0` (or other offset).
- Check: `position: fixed` inside a `transform`, `filter`, or `perspective` parent → the parent becomes the containing block, breaking fixed positioning. This is a browser spec behavior, not a bug.
- Check: `inset: 0` without `position: absolute/fixed` → no effect. Tailwind: `inset-0` requires `absolute` or `fixed`.
- Check: `position: absolute` with both `left` and `right` set (or `top` and `bottom`) → stretches element. Intentional for overlays; unintentional if width/height is also set (overconstrained, `right`/`bottom` is ignored in LTR).
- Check: percentage-based positioning (`top: 50%`, `left: 50%`) without `transform: translate(-50%, -50%)` → element's top-left corner is at center, not its center point. Tailwind: use `-translate-x-1/2 -translate-y-1/2` or prefer `flex`/`grid` centering (`place-items-center`).
