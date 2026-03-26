---
name: a11y-audit
department: "advocate"
description: "Use when auditing accessibility compliance of a feature or codebase. Covers WCAG 2.2 AA conformance, screen reader compatibility, keyboard navigation, focus management, color contrast, reduced motion, and ARIA usage. Do not use for general UX review (use journey-mapping) or component interaction specs (use interaction-design)."
version: 1
triggers:
  - "accessibility"
  - "a11y"
  - "WCAG"
  - "screen reader"
  - "ARIA"
  - "keyboard navigation"
  - "focus management"
  - "color contrast"
  - "reduced motion"
---

# A11y Audit

## Purpose

Evaluate accessibility compliance against WCAG 2.2 AA criteria across perceivable, operable, understandable, and robust principles. Identify barriers for users of assistive technologies and provide actionable remediation steps.

## Scope Constraints

Reads source code, templates, styles, and component markup for accessibility analysis. Does not modify files or execute code. Does not perform automated accessibility scans (recommend tooling where appropriate).

## Inputs

- Feature description or codebase path to audit
- Target WCAG conformance level (default: AA)
- Known assistive technologies in scope (screen readers, switch devices, etc.)
- Any existing accessibility testing results or known issues

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Audit keyboard navigation and focus management
- [ ] Step 2: Evaluate screen reader compatibility
- [ ] Step 3: Check color contrast and visual accessibility
- [ ] Step 4: Review ARIA usage and semantic markup
- [ ] Step 5: Assess motion and animation accessibility
- [ ] Step 6: Verify form and error handling accessibility

### Step 1: Audit Keyboard Navigation and Focus Management

- Verify all interactive elements are reachable via Tab/Shift+Tab.
- Check focus order matches visual reading order.
- Confirm visible focus indicators on all interactive elements (`:focus-visible`).
- Verify focus trapping in modals, dialogs, and drawers.
- Check skip-link presence for bypassing repetitive navigation.
- Confirm no keyboard traps (user can always Tab out of any component).

### Step 2: Evaluate Screen Reader Compatibility

- Verify heading hierarchy (`h1`-`h6`) is logical and unbroken.
- Check all images have meaningful `alt` text or `alt=""` for decorative.
- Confirm form inputs have associated `<label>` elements or `aria-label`.
- Verify live regions (`aria-live`) for dynamic content updates.
- Check landmark regions (`<nav>`, `<main>`, `<aside>`, `<header>`, `<footer>`).
- Confirm status messages use `role="status"` or `role="alert"`.

### Step 3: Check Color Contrast and Visual Accessibility

- Verify text contrast meets 4.5:1 for normal text, 3:1 for large text (WCAG 1.4.3).
- Check non-text contrast for UI components and graphical objects at 3:1 (WCAG 1.4.11).
- Confirm information is not conveyed by color alone.
- Verify content remains readable at 200% zoom.
- Check text spacing adjustment tolerance (WCAG 1.4.12).

### Step 4: Review ARIA Usage and Semantic Markup

- Verify ARIA roles match element behavior (no `role="button"` on non-interactive elements without keyboard handlers).
- Check for redundant ARIA on native semantic elements.
- Confirm `aria-expanded`, `aria-selected`, `aria-checked` states update correctly.
- Verify custom widgets follow WAI-ARIA Authoring Practices patterns.
- Check `aria-describedby` and `aria-labelledby` reference valid IDs.

### Step 5: Assess Motion and Animation Accessibility

- Check `prefers-reduced-motion` media query support.
- Verify no content relies solely on animation to convey meaning.
- Confirm auto-playing content can be paused, stopped, or hidden (WCAG 2.2.2).
- Check parallax and scrolling effects respect reduced motion preference.

### Step 6: Verify Form and Error Handling Accessibility

- Confirm error messages are programmatically associated with inputs (`aria-describedby`).
- Verify inline validation announces errors to screen readers.
- Check required fields are indicated both visually and programmatically (`aria-required`).
- Confirm form submission errors provide clear recovery instructions.
- Verify autocomplete attributes on identity/payment fields (WCAG 1.3.5).

> **Compaction resilience**: If context was lost, re-read the Inputs section to identify the audit target, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

| Category | WCAG Criterion | Finding | Severity | Recommendation |
|----------|---------------|---------|----------|----------------|
| Keyboard | 2.1.1 Keyboard | ... | Critical/High/Med/Low | ... |
| Screen reader | 1.3.1 Info and Relationships | ... | ... | ... |
| Color contrast | 1.4.3 Contrast (Minimum) | ... | ... | ... |
| ARIA | 4.1.2 Name, Role, Value | ... | ... | ... |
| Motion | 2.3.1 Three Flashes | ... | ... | ... |
| Forms | 3.3.1 Error Identification | ... | ... | ... |

## Handoff

- Hand off to interaction-design if component-level state changes are needed for accessibility remediation.
- Hand off to artisan/visual-audit if contrast or visual design changes require design system updates.

## Quality Checks

- [ ] All interactive elements verified for keyboard accessibility
- [ ] Focus management audited for modals, dialogs, and dynamic content
- [ ] Screen reader heading hierarchy and landmark structure validated
- [ ] Color contrast ratios verified against WCAG 2.2 AA thresholds
- [ ] ARIA usage follows WAI-ARIA Authoring Practices
- [ ] Reduced motion preferences checked
- [ ] Form error handling is accessible
- [ ] Each finding references a specific WCAG success criterion

## Evolution Notes
<!-- Observations appended after each use -->
