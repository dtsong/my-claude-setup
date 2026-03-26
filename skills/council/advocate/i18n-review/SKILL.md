---
name: i18n-review
department: "advocate"
description: "Use when reviewing internationalization readiness of a feature or codebase. Covers locale strategy, RTL layout, string externalization, pluralization, date/number formatting, and cultural UX adaptation. Do not use for general accessibility audits (use interaction-design)."
version: 1
triggers:
  - "i18n"
  - "localization"
  - "translation"
  - "RTL"
  - "locale"
  - "multi-language"
  - "pluralization"
  - "date format"
  - "number format"
  - "cultural"
---

# I18n Review

## Purpose

Evaluate internationalization readiness across UI, data, and content layers to ensure the product works correctly for users in any locale.

## Scope Constraints

Reads source code, templates, and configuration for i18n analysis. Does not modify files or execute code. Does not perform actual translations.

## Inputs

- Feature description or codebase path to review
- Target locales (or "all" for general readiness)
- Known i18n framework in use (react-intl, next-intl, i18next, etc.), if any
- Any existing translation files or locale configs

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Audit string externalization
- [ ] Step 2: Evaluate locale strategy
- [ ] Step 3: Review pluralization handling
- [ ] Step 4: Check date/number/currency formatting
- [ ] Step 5: Assess RTL layout support
- [ ] Step 6: Evaluate cultural UX adaptation

### Step 1: Audit String Externalization

- Scan for hardcoded user-facing strings in source files.
- Verify all strings use the project's i18n extraction method (message IDs, translation keys).
- Check for string concatenation that breaks translator context.
- Flag template literals with embedded logic that prevent proper translation.

### Step 2: Evaluate Locale Strategy

- Identify how locale is detected (browser, URL, user preference, geo-IP).
- Verify locale persistence across sessions and navigation.
- Check fallback chain (e.g., `fr-CA` -> `fr` -> `en`).
- Confirm locale switching does not cause full page reloads or state loss.

### Step 3: Review Pluralization Handling

- Check usage of ICU MessageFormat or equivalent plural rules.
- Verify plural categories beyond "one/other" for languages that need them (zero, two, few, many).
- Flag any manual plural logic (ternary operators, `count === 1` checks).

### Step 4: Check Date/Number/Currency Formatting

- Verify use of `Intl.DateTimeFormat`, `Intl.NumberFormat`, or equivalent locale-aware APIs.
- Flag hardcoded date patterns (MM/DD/YYYY) or number separators.
- Check currency display respects locale conventions.
- Verify timezone handling for date display.

### Step 5: Assess RTL Layout Support

- Check for CSS logical properties (`inline-start`/`inline-end` vs `left`/`right`).
- Verify `dir="rtl"` attribute propagation.
- Flag hardcoded directional icons (arrows, chevrons) that need mirroring.
- Check text alignment and reading order in mixed-direction content.

### Step 6: Evaluate Cultural UX Adaptation

- Review form fields for locale assumptions (name format, address, phone).
- Check for culturally sensitive icons, colors, or imagery.
- Verify text expansion accommodation (German ~30% longer than English).
- Assess sort order and collation for locale-appropriate sorting.

> **Compaction resilience**: If context was lost, re-read the Inputs section to identify the review target, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

| Category | Finding | Severity | Recommendation |
|----------|---------|----------|----------------|
| String externalization | ... | High/Med/Low | ... |
| Locale strategy | ... | ... | ... |
| Pluralization | ... | ... | ... |
| Date/Number formatting | ... | ... | ... |
| RTL support | ... | ... | ... |
| Cultural adaptation | ... | ... | ... |

## Handoff

- Hand off to interaction-design if component-level state changes are needed for locale-specific UI adaptations.
- Hand off to craftsman/pattern-analysis if i18n framework integration patterns need implementation review.

## Quality Checks

- [ ] All hardcoded user-facing strings identified
- [ ] Locale detection and fallback chain documented
- [ ] Plural rules go beyond simple one/other where needed
- [ ] Date/number formatting uses locale-aware APIs
- [ ] RTL layout assessed with logical properties
- [ ] Text expansion impact on layouts evaluated
- [ ] Form fields checked for locale assumptions
- [ ] Severity ratings applied to all findings

## Evolution Notes
<!-- Observations appended after each use -->
