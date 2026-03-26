---
name: a11y-audit
department: "advocate"
description: "Use when auditing accessibility compliance for UI components, pages, or flows. Covers WCAG 2.2 AA conformance, screen reader compatibility, keyboard navigation, focus management, color contrast, reduced motion, and ARIA patterns. Do not use for general UX journey mapping (use journey-mapping) or component interaction specs (use interaction-design)."
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

# Accessibility Audit

## Purpose

Audit UI elements against WCAG 2.2 AA standards and assistive technology compatibility to ensure inclusive, barrier-free experiences.

## Scope Constraints

Reads component code, markup, and style definitions for accessibility analysis. Does not modify files or execute code. Does not run automated testing tools directly.

## Inputs

- Component, page, or flow to audit
- Target WCAG level (default: AA)
- Known assistive technologies in scope (screen readers, switch access, voice control)
- Any existing accessibility test results or known issues

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Semantic structure audit
- [ ] Step 2: Keyboard navigation audit
- [ ] Step 3: Focus management audit
- [ ] Step 4: Screen reader compatibility audit
- [ ] Step 5: Visual accessibility audit
- [ ] Step 6: Motion and animation audit
- [ ] Step 7: ARIA patterns audit

### Step 1: Semantic Structure Audit

- Verify heading hierarchy (h1-h6) is logical and sequential.
- Check landmark regions (main, nav, banner, contentinfo) are present.
- Confirm lists, tables, and form groups use correct semantic elements.
- Validate page title and language attributes.

### Step 2: Keyboard Navigation Audit

- Tab through all interactive elements; confirm logical tab order.
- Verify all functionality is operable via keyboard alone.
- Check for keyboard traps (can the user escape every component?).
- Confirm custom keyboard shortcuts do not conflict with assistive technology.

### Step 3: Focus Management Audit

- Verify visible focus indicators on all interactive elements (minimum 3:1 contrast).
- Check focus moves logically after modal open/close, route changes, and dynamic content.
- Confirm skip links are present and functional.
- Validate focus is not lost after content updates or deletions.

### Step 4: Screen Reader Compatibility Audit

- Verify all images have appropriate alt text (decorative images use `alt=""`).
- Check form inputs have associated labels (explicit `<label>` or `aria-labelledby`).
- Confirm status messages use `role="status"` or `aria-live` regions.
- Validate that dynamic content changes are announced.

### Step 5: Visual Accessibility Audit

- Check text contrast meets 4.5:1 (normal text) and 3:1 (large text) ratios.
- Verify UI component contrast meets 3:1 against adjacent colors.
- Confirm information is not conveyed by color alone.
- Check text resizes to 200% without loss of content or function.
- Validate touch targets meet 24x24 CSS pixel minimum.

### Step 6: Motion and Animation Audit

- Verify `prefers-reduced-motion` is respected for all animations.
- Check no content flashes more than 3 times per second.
- Confirm auto-playing content can be paused, stopped, or hidden.

### Step 7: ARIA Patterns Audit

- Validate ARIA roles match the APG (ARIA Authoring Practices Guide) patterns.
- Check `aria-expanded`, `aria-selected`, `aria-checked` states update correctly.
- Confirm no redundant ARIA (e.g., `role="button"` on a `<button>`).
- Verify `aria-describedby` and `aria-errormessage` on form validation.

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to identify the audit target, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

### Audit Summary

| Category | Issues Found | Severity | WCAG Criteria |
|----------|-------------|----------|---------------|
| ... | ... | Critical/Major/Minor | X.X.X |

### Issue Detail

For each issue:
- **Location:** Component or element reference
- **WCAG criterion:** Success criterion number and name
- **Severity:** Critical / Major / Minor
- **Description:** What fails and why
- **Recommendation:** How to fix with code example if applicable

### Compliance Statement

Overall conformance level achieved and blockers to target level.

## Handoff

- Hand off to interaction-design if component-level state specs need updating to address audit findings.
- Hand off to craftsman/pattern-analysis if implementation patterns need refactoring for accessibility fixes.

## Quality Checks

- [ ] All seven audit steps completed
- [ ] Each issue references a specific WCAG 2.2 success criterion
- [ ] Severity ratings applied to all issues
- [ ] Fix recommendations are actionable (not just "make it accessible")
- [ ] Screen reader behavior explicitly described for dynamic content
- [ ] Keyboard-only operation verified for all interactive elements
- [ ] Color contrast ratios cited with specific values
- [ ] `prefers-reduced-motion` handling verified

## Evolution Notes
<!-- Observations appended after each use -->
