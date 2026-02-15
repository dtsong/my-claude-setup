---
name: interaction-design
department: "advocate"
description: "Use when designing component interaction specs with visual states, transitions, and accessibility requirements. Covers state matrices, responsive behavior, ARIA compliance, and content constraints. Do not use for multi-step user journey mapping (use journey-mapping)."
version: 1
triggers:
  - "component"
  - "UI"
  - "interaction"
  - "modal"
  - "form"
  - "button"
  - "dropdown"
  - "toast"
  - "dialog"
  - "input"
  - "state"
  - "hover"
  - "focus"
  - "animation"
---

# Interaction Design

## Purpose

Design component interaction specs with all visual states, transitions, and accessibility requirements.

## Scope Constraints

Reads component requirements, design system documentation, and platform guidelines for interaction analysis. Does not modify files or execute code. Does not access running applications or browser environments directly.

## Inputs

- Component name and purpose
- Context where it appears (page, modal, sidebar, etc.)
- User actions it must support
- Existing design system or component library (if any)
- Platform constraints (web, mobile, both)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define component purpose
- [ ] Step 2: Enumerate all visual states
- [ ] Step 3: Define transitions between states
- [ ] Step 4: Specify accessibility requirements
- [ ] Step 5: Define responsive behavior
- [ ] Step 6: Specify content constraints

### Step 1: Define Component Purpose

- What job does this component do?
- What user need does it serve?
- Where does it appear in the UI hierarchy?
- What is the minimal viable version?

### Step 2: Enumerate All Visual States

| State | Visual Treatment | When Active |
|-------|-----------------|-------------|
| Default/Rest | Base styling | No interaction |
| Hover | Subtle highlight, cursor change | Mouse over (desktop) |
| Focus | Visible focus ring | Keyboard navigation, tab |
| Active/Pressed | Depressed/accent state | Mouse down, touch |
| Loading/Pending | Spinner, skeleton, disabled input | Async operation in progress |
| Success/Confirmed | Green accent, checkmark, brief flash | Operation completed |
| Error/Invalid | Red accent, error message, icon | Validation failed, API error |
| Disabled | Muted colors, no pointer events | Precondition not met |
| Empty/Placeholder | Placeholder text, illustration | No data or content yet |

### Step 3: Define Transitions Between States

For each state change:
- **Trigger:** What causes the transition (click, hover, data load, timer, keyboard)
- **Animation:** Duration and easing (subtle and purposeful, not gratuitous)
  - Micro-interactions: 100-200ms
  - State changes: 200-300ms
  - Layout shifts: 300-500ms
- **Feedback mechanism:** Color change, icon swap, text update, motion

### Step 4: Specify Accessibility Requirements

- **ARIA roles and labels:**
  - `role` attribute (button, dialog, alert, etc.)
  - `aria-label` or `aria-labelledby` for non-text elements
  - `aria-describedby` for supplementary descriptions
  - `aria-live` regions for dynamic updates
- **Keyboard navigation:**
  - Tab order (logical, matches visual order)
  - Enter/Space behavior (activate buttons, submit forms)
  - Escape behavior (close modals, cancel operations)
  - Arrow key behavior (navigate lists, tabs, menus)
- **Screen reader announcements:**
  - State changes announced (loading, success, error)
  - Dynamic content updates via `aria-live`
- **Visual accessibility:**
  - Color contrast: WCAG AA minimum (4.5:1 text, 3:1 UI elements)
  - Focus indicators visible and high contrast
  - Information not conveyed by color alone

### Step 5: Define Responsive Behavior

- **Desktop (1024px+):**
  - Full layout, hover interactions available
  - Keyboard shortcuts active
- **Tablet (768px - 1023px):**
  - Adjusted spacing, simplified hover states
  - Touch-friendly but more screen real estate than mobile
- **Mobile (< 768px):**
  - Touch targets minimum 44x44px
  - Swipe gestures where appropriate
  - Bottom-sheet instead of dropdown where needed
  - Simplified layout, stacked elements

### Step 6: Specify Content Constraints

- Character limits for labels, descriptions, error messages
- Truncation strategy (ellipsis, fade, wrap)
- Internationalization considerations (text expansion 30-50% for translations)
- Number formatting, date formatting

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what component is being designed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### State Matrix

| State | Background | Border | Text | Icon | Cursor | Shadow |
|-------|-----------|--------|------|------|--------|--------|
| Default | ... | ... | ... | ... | ... | ... |
| Hover | ... | ... | ... | ... | ... | ... |
| Focus | ... | ... | ... | ... | ... | ... |
| Active | ... | ... | ... | ... | ... | ... |
| Loading | ... | ... | ... | ... | ... | ... |
| Success | ... | ... | ... | ... | ... | ... |
| Error | ... | ... | ... | ... | ... | ... |
| Disabled | ... | ... | ... | ... | ... | ... |

### Transition Diagram

```
[Default] ←→ [Hover] → [Active] → [Loading] → [Success]
    ↓                                    ↓
 [Focus]                             [Error]
    ↓
 [Active]
```

### Accessibility Checklist

- [ ] ARIA role assigned
- [ ] ARIA label provided
- [ ] Keyboard operable (tab, enter, escape)
- [ ] Focus indicator visible
- [ ] Screen reader announces state changes
- [ ] Color contrast meets WCAG AA
- [ ] Touch targets >= 44x44px

### Component API

```
Props:
- variant: 'primary' | 'secondary' | 'ghost'
- size: 'sm' | 'md' | 'lg'
- disabled: boolean
- loading: boolean
- ...

Events:
- onClick / onPress
- onFocus / onBlur
- ...

Slots:
- icon (leading/trailing)
- children (content)
- ...
```

## Handoff

- Hand off to journey-mapping if user flow analysis is needed for the broader context where the component appears.
- Hand off to craftsman/pattern-analysis if code implementation patterns are needed for the designed component.

## Quality Checks

- [ ] All 8+ visual states defined (default, hover, focus, active, loading, success, error, disabled)
- [ ] Keyboard navigation specified for all interactive elements
- [ ] ARIA labels provided for all non-text elements
- [ ] Touch targets meet 44px minimum
- [ ] Loading and error states designed with recovery paths
- [ ] Empty/placeholder state designed
- [ ] Transitions are subtle and purposeful (not gratuitous)
- [ ] Responsive behavior specified for mobile, tablet, desktop

## Evolution Notes
<!-- Observations appended after each use -->
