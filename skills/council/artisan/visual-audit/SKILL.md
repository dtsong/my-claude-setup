---
name: "Visual Audit"
department: "artisan"
description: "[Council] Structured visual design critique with specific actionable feedback. Used during council/academy deliberation only."
version: 1
triggers:
  - "visual"
  - "design review"
  - "UI audit"
  - "hierarchy"
  - "contrast"
  - "spacing"
  - "typography"
  - "color"
  - "layout"
---

# Visual Audit

## Purpose

Perform a structured visual design critique of an interface, producing specific actionable feedback on hierarchy, contrast, spacing, typography, color, and overall coherence.

## Inputs

- Screenshots, mockups, or live implementation of the interface
- Design system or style guide (if it exists)
- Target context (marketing page, app dashboard, settings screen, etc.)
- Accessibility requirements (WCAG AA, AAA, or custom)

## Process

### Step 1: Squint Test

View the interface at arm's length (or blur it mentally). Identify:
- What's the loudest element? Is it the right one?
- Can you identify the primary action within 3 seconds?
- Is there a clear visual reading order?
- Are there any areas of visual "soup" (too much competing for attention)?

### Step 2: Hierarchy Audit

Check the information hierarchy:
- **Heading levels:** Are there clear H1 → H2 → H3 distinctions via size and weight?
- **Primary vs secondary actions:** Is the primary action visually dominant (filled button) vs secondary (ghost/outline)?
- **Content grouping:** Are related items visually grouped (proximity) and distinct groups separated (spacing)?
- **Emphasis distribution:** Is anything fighting for attention that shouldn't be?

### Step 3: Typography Audit

Check the type system:
- **Scale consistency:** Are font sizes from a defined scale (not arbitrary)?
- **Line height:** Is body text at 1.4-1.6x line height for readability?
- **Measure:** Are line lengths between 45-75 characters for body text?
- **Weight usage:** Is font weight used semantically (bold for emphasis, not decoration)?
- **Font pairing:** Are typefaces intentionally paired (one serif + one sans, or a single family)?

### Step 4: Color and Contrast Audit

Check color usage:
- **Contrast ratios:** All text meets WCAG AA (4.5:1 normal text, 3:1 large text)
- **Color meaning:** Color is not the sole indicator of status (add icons, text, patterns)
- **Palette coherence:** Colors come from a defined palette, not ad-hoc hex values
- **Dark mode:** If supported, contrast ratios are verified in dark mode too
- **Saturation balance:** No oversaturated elements that vibrate or strain eyes

### Step 5: Spacing and Alignment Audit

Check spatial consistency:
- **Grid adherence:** Elements align to a defined grid (4px, 8px base)
- **Consistent spacing:** Same-level items use the same spacing value
- **Breathing room:** Content doesn't feel cramped; whitespace is used intentionally
- **Alignment lines:** Elements that should align actually align (check left edges, baselines)

### Step 6: Component Consistency Audit

Check for visual consistency:
- **Button styles:** All buttons of the same type look the same
- **Card patterns:** Cards share border radius, shadow, padding
- **Icon style:** Icons are from one set (outlined, filled, or mixed intentionally)
- **Form elements:** Inputs, selects, and textareas share a visual language

## Output Format

```markdown
# Visual Audit Report

## Overall Assessment
**Score:** [1-10]
**Summary:** [2-3 sentences on the interface's visual effectiveness]

## Squint Test Results
- **Primary focus:** [What draws the eye first — is this correct?]
- **Reading order:** [Clear / Unclear / Competing elements]
- **Visual noise:** [Low / Medium / High]

## Findings

### [CRITICAL] [Category] — [Finding]
**Current:** [What's happening now]
**Issue:** [Why it's a problem — cite specific principle]
**Fix:** [Specific change — exact values where possible]

### [IMPROVEMENT] [Category] — [Finding]
**Current:** [What's happening now]
**Suggestion:** [Specific improvement with rationale]

## Contrast Report
| Element | Foreground | Background | Ratio | Pass AA |
|---------|-----------|------------|-------|---------|
| Body text | #333 | #fff | 12.6:1 | Yes |
| Muted text | #999 | #fff | 2.8:1 | NO |

## Quick Wins
1. [Change that would have the biggest visual impact for the least effort]
2. [Second quick win]
3. [Third quick win]
```

## Quality Checks

- [ ] Every finding includes a specific fix, not just a problem description
- [ ] Contrast ratios are calculated with actual color values
- [ ] Typography findings reference a type scale or specific sizes
- [ ] Spacing findings reference a grid system or specific values
- [ ] At least 3 quick wins are identified with effort-to-impact prioritization
- [ ] Dark mode contrast is checked if dark mode is supported

## Evolution Notes
<!-- Observations appended after each use -->
