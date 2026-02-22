---
name: css-layout-debugger
description: >
  Use when a user reports CSS, layout, or styling issues in a Next.js application —
  "element overlapping," "spacing is wrong," "responsive layout broken," "dark mode
  not working," "Tailwind classes not applying," or "alignment off." Diagnoses through
  a 6-phase pipeline that mirrors browser evaluation order, covering token resolution,
  cascade conflicts, layout models, stacking contexts, and viewport responsiveness.
  Handles Tailwind, CSS Modules, styled-components, and vanilla CSS. Not for
  JavaScript logic bugs, data fetching issues, or server-side rendering errors —
  route those to ui-bug-investigator.
model:
  preferred: sonnet
  acceptable: [sonnet, opus]
  minimum: sonnet
  allow_downgrade: false
  reasoning_demand: medium
---

# CSS Layout Debugger

Diagnose CSS/layout/styling issues through a 6-phase pipeline mirroring browser evaluation order.

## Scope Constraints

- Read-only access to source files, config files (`tailwind.config.*`, CSS files), and component files in the ComponentMap
- Write access limited to `.claude/qa-cache/artifacts/` for DiagnosisReport persistence
- Does not modify source code or run shell commands
- Inspects only components and styles within the ComponentMap — stops at external library internals

## Inputs

- **ComponentMap** (required): Path to `.claude/qa-cache/component-maps/{route-slug}.json`
- **Route path** (required): The route where the issue appears
- **Symptom description** (required): User-reported styling/layout bug
- **Screenshot** (optional): Visual evidence of the issue

## Procedure

Copy this checklist and update as you complete each phase:
```
Progress:
- [ ] Phase 1: Style Approach Detection
- [ ] Phase 2: Token/Variable Resolution
- [ ] Phase 3: Cascade & Specificity
- [ ] Phase 4: Layout Model
- [ ] Phase 5: Stacking & Paint
- [ ] Phase 6: Viewport & Responsiveness
- [ ] Visual Triage (if screenshot)
- [ ] Output DiagnosisReport
```

Note: If you've lost context of previous phases (e.g., after context compaction), check the progress checklist above. Resume from the last unchecked item. Re-read relevant reference files if needed.

Read the ComponentMap. Extract `styling.primary` and the target component's `styling_approach`, `has_conditional_classes`, `design_system_component`, and `accepts_className_prop` fields. If ComponentMap completeness is `partial` or `shallow`, warn the user that some components were not traced.

Execute phases in this fixed order. Stop early when a root cause is found with high confidence. Never reorder phases.

### Phase 1: Style Approach Detection

If ComponentMap already contains `styling.primary`, confirm by scanning the target component file. Otherwise, classify:

| Signal | Approach |
|--------|----------|
| `className={cn(...)}` / `clsx(...)` / `cva()` | tailwind-conditional |
| `className="..."` with utility classes | tailwind-direct |
| `import styles from '*.module.css'` | css-modules |
| `styled.*` / `` css`...` `` | css-in-js |
| `<style jsx>` | styled-jsx |
| `style={{}}` | inline |
| Multiple signals | mixed |

Record the detected approach. All subsequent output uses this approach's vocabulary.

### Phase 2: Token/Variable Resolution

Check CSS custom properties and design token definitions relevant to the symptom.

- Tailwind: read `tailwind.config.ts` (or `.js`/`.mjs`). Verify referenced theme values exist in `theme.extend`. Flag undefined custom colors, spacing, or breakpoints.
- CSS Modules: verify `composes` chains resolve. Check for missing source files.
- CSS variables: trace `var(--name)` to its definition. Flag undefined variables, circular references, or fallback values masking a missing definition.

If the symptom relates to color, spacing, or typography and the token resolves incorrectly, report as root cause. Otherwise continue.

### Phase 3: Cascade & Specificity

**If Tailwind detected:** read `references/tailwind-conflict-map.md`. Apply utility conflict detection against the target element's class list. Parse `cn()`/`clsx()`/`classnames()` calls to separate always-applied from conditionally-applied classes. Flag definite conflicts. Warn on potential conflicts.

**If CSS Modules detected:** check for `:global()` selectors leaking styles. Check `composes` order (last wins). Verify no unintended class name collisions across modules.

**If vanilla/css-in-js:** calculate specificity of competing selectors targeting the same element. Flag `!important` usage.

**If shadcn/ui detected** (ComponentMap `design_system_component: true`): trace the override boundary. Read the `components/ui/*.tsx` file to find base classes. Compare with developer-passed `className`. Check if `cn()` (tailwind-merge) resolves the merge correctly. Flag conflicts that tailwind-merge cannot resolve (responsive variants, arbitrary values).

### Phase 4: Layout Model

Read `references/layout-model-checks.md`. Run the checklist relevant to the symptom:
- Overflow/sizing symptoms: flexbox and grid checks first
- Alignment symptoms: flex alignment and grid placement checks
- Collapse/overlap symptoms: box model and positioning checks
- All symptoms: check `box-sizing` consistency

### Phase 5: Stacking & Paint

Read `references/stacking-viewport-checks.md`, section "Stacking & Paint". Run checks:
- Z-index without stacking context
- `overflow: hidden` clipping positioned/transformed children
- `transform`/`filter`/`will-change` creating unintended compositing layers

Skip this phase if symptom is clearly layout/spacing only. Mark as SKIPPED with reason.

### Phase 6: Viewport & Responsiveness

Read `references/stacking-viewport-checks.md`, section "Viewport & Responsiveness". Run checks:
- Viewport unit issues (`vh` vs `dvh`, `100vw` scrollbar problem)
- Tailwind responsive prefix ordering and completeness
- Container queries vs media queries
- Missing breakpoint coverage for layout-changing utilities

Skip if symptom is not responsive/viewport-related. Mark as SKIPPED with reason.

### Visual Triage (if screenshot provided)

If the user provides a screenshot, perform Tier 1 visual triage. Print this disclaimer first:

```
VISUAL TRIAGE (qualitative, code-informed):
- Identifies visible differences; cannot detect sub-pixel misalignment
- Dynamic states (hover, animation, scroll) cannot be assessed from static images
- "No differences observed" is an observation, not a certification
- For pixel-level confidence, use automated regression tooling
```

Cross-reference visual observations with the code findings from Phases 1-6. Never output CLEAR for visual triage. Use "No visible differences observed (see disclaimer)" or list specific FLAGGED findings.

## Antipattern Severity

Flag proactively even if not directly related to the reported symptom:

| Severity | Flag as | Example |
|----------|---------|---------|
| ERROR | FLAGGED | Focus indicator removed without `:focus-visible` replacement |
| ERROR | FLAGGED | `<img>` without width/height (CLS) |
| WARNING | FLAGGED | `transition: all` (performance) |
| WARNING | FLAGGED | Raw hex value when design token exists |
| WARNING | FLAGGED | Color class without `dark:` counterpart |

## Output Format

Present findings-first, not phase-by-phase:

```
## CSS Diagnosis: [component name]

FLAGGED  [root cause] — [file:line]
  Evidence: [what was found] | Fix: [suggestion in project's styling vocabulary]
FLAGGED  [secondary issue] — [file:line]
  Evidence: [what was found]

CLEAR  [ruled out] (Phase N) | CLEAR  [ruled out] (Phase N)
SKIPPED  [phase]: [reason] | SKIPPED  [phase]: [reason]

Checked: [N items] (tokens, cascade, layout) | Not checked: stacking, viewport | Confidence: High
```

## Handoff

Pass the DiagnosisReport artifact path to qa-coordinator. The report contains structured findings with `rootCause`, severity, and suggested fix in the project's styling vocabulary. Consumed by `component-fix-and-verify`.

## References

| Path | Load Condition | Content Summary |
|------|---------------|-----------------|
| `references/tailwind-conflict-map.md` | Phase 3, Tailwind detected | Utility conflict pairs, tailwind-merge resolution rules |
| `references/layout-model-checks.md` | Phase 4, always | Flexbox, grid, box model, positioning checklists |
| `references/stacking-viewport-checks.md` | Phase 5-6, as needed | Stacking context rules, viewport unit issues, responsive checks |
