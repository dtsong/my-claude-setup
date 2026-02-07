---
name: "Design System Architecture"
department: "artisan"
description: "Token hierarchy, theming strategy, and cross-platform consistency"
version: 1
triggers:
  - "design system"
  - "design tokens"
  - "theme"
  - "dark mode"
  - "CSS variables"
  - "Figma"
  - "Storybook"
  - "component library"
  - "style guide"
---

# Design System Architecture

## Purpose

Design a token-based design system architecture, including primitive → semantic → component token hierarchy, theming strategy (dark/light mode), and cross-platform implementation plan.

## Inputs

- Existing styling approach (Tailwind, CSS modules, styled-components, etc.)
- Target platforms (web, iOS, Android, cross-platform)
- Brand guidelines or existing color palette
- Current component inventory
- Theming requirements (dark mode, high contrast, brand variations)

## Process

### Step 1: Audit Current State

Review the existing styling approach:
- How are colors, spacing, and typography defined today?
- Are there hardcoded values scattered across components?
- Is there an existing design system or component library?
- What CSS methodology is used (utility-first, BEM, CSS-in-JS)?

### Step 2: Define Primitive Tokens

Establish the raw values that form the foundation:
- **Color primitives:** Named palette (blue-50 through blue-900, gray scale, semantic colors)
- **Spacing scale:** 4px base unit → 0, 1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64
- **Type scale:** Size ramp with corresponding line heights and letter spacing
- **Border radius:** Small (4px), medium (8px), large (16px), full (9999px)
- **Shadow/elevation:** Subtle, medium, prominent
- **Duration:** Fast (100ms), normal (200ms), slow (300ms)

### Step 3: Define Semantic Tokens

Map primitives to semantic meaning:
- **Surface:** surface-primary, surface-secondary, surface-elevated
- **Text:** text-primary, text-secondary, text-muted, text-inverse
- **Border:** border-default, border-strong, border-focus
- **Interactive:** interactive-primary, interactive-hover, interactive-pressed
- **Status:** status-success, status-warning, status-error, status-info
- **Spacing:** space-xs, space-sm, space-md, space-lg, space-xl

### Step 4: Define Component Tokens

Map semantic tokens to component-specific values:
- **Button:** button-bg, button-text, button-border, button-radius
- **Input:** input-bg, input-border, input-focus-ring, input-text
- **Card:** card-bg, card-border, card-shadow, card-radius, card-padding

### Step 5: Design Theme Architecture

Define how themes override token values:
- **Light theme:** Default token assignments
- **Dark theme:** Which semantic tokens change, which stay the same
- **High contrast:** Increased border widths, higher contrast ratios
- **Implementation:** CSS custom properties, Tailwind config, or platform-specific theming

### Step 6: Cross-Platform Strategy

If multiple platforms:
- **Token format:** Use Style Dictionary or similar to generate platform-specific output
- **Web:** CSS custom properties or Tailwind theme config
- **iOS:** Swift color/spacing constants or asset catalogs
- **Android:** XML resources or Compose theme
- **Shared source of truth:** JSON or YAML token definitions

## Output Format

```markdown
# Design System Architecture

## Token Hierarchy

### Primitive Tokens
| Category | Token | Value |
|----------|-------|-------|
| Color | blue-500 | #3B82F6 |
| Spacing | space-4 | 16px |
| Type | text-base | 16px/24px |

### Semantic Tokens
| Token | Light | Dark | Usage |
|-------|-------|------|-------|
| surface-primary | white | gray-900 | Main background |
| text-primary | gray-900 | gray-50 | Body text |
| interactive-primary | blue-500 | blue-400 | Buttons, links |

### Component Tokens
| Component | Token | Maps To |
|-----------|-------|---------|
| Button (primary) | button-bg | interactive-primary |
| Button (primary) | button-text | text-inverse |

## Theme Switching
[Implementation approach — CSS class, media query, user preference]

## File Structure
```
tokens/
  primitives.json
  semantic-light.json
  semantic-dark.json
  components.json
```

## Migration Plan
[Steps to migrate from current approach to token-based system]
```

## Quality Checks

- [ ] All existing hardcoded values can be mapped to tokens
- [ ] Semantic tokens cover all current UI needs without gaps
- [ ] Dark mode token overrides maintain WCAG AA contrast
- [ ] Token naming is consistent and predictable
- [ ] The migration path doesn't require a big-bang rewrite
- [ ] Cross-platform strategy has a single source of truth

## Evolution Notes
<!-- Observations appended after each use -->
