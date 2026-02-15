---
name: platform-audit
department: "pathfinder"
description: "Use when auditing a feature or implementation against platform-specific guidelines such as iOS HIG, Material Design 3, and WCAG. Covers compliance scoring, violation identification, remediation steps, and App Store risk assessment. Do not use for navigation architecture (use navigation-design) or hardware API integration (use device-integration)."
version: 1
triggers:
  - "iOS"
  - "Android"
  - "HIG"
  - "Material Design"
  - "platform"
  - "guideline"
  - "compliance"
  - "app review"
  - "App Store"
  - "Play Store"
---

# Platform Audit

## Purpose

Evaluate a proposed feature or existing implementation against platform-specific guidelines (iOS Human Interface Guidelines, Material Design 3, Web Content Accessibility Guidelines) and produce a compliance report with specific violations and remediation steps.

## Scope Constraints

Reads source code, UI mockups, and platform guideline documentation for compliance analysis. Does not modify files or execute code. Does not submit builds or interact with App Store Connect or Google Play Console.

## Inputs

- Feature description or UI mockup being evaluated
- Target platforms (iOS, Android, Web, or cross-platform)
- Existing implementation code (if available)
- App Store / Play Store submission history (if relevant)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Identify target platforms
- [ ] Step 2: Audit iOS HIG compliance
- [ ] Step 3: Audit Material Design compliance
- [ ] Step 4: Audit Web/PWA compliance
- [ ] Step 5: Cross-platform consistency check
- [ ] Step 6: App Store risk assessment

### Step 1: Identify Target Platforms

Determine which platforms the feature targets. For cross-platform projects, note the framework (React Native, Flutter, Capacitor) and assess whether it provides native-feeling UI by default or requires platform-specific overrides.

### Step 2: Audit iOS HIG Compliance

If targeting iOS, check against key Human Interface Guidelines:
- Navigation patterns (navigation controller, tab bars, bottom sheets)
- System UI integration (status bar, safe area, Dynamic Island)
- Gestures (swipe-to-delete, pull-to-refresh, edge swipe for back)
- Typography (SF Pro, Dynamic Type support)
- Iconography (SF Symbols usage, tab bar icon conventions)
- Privacy and permissions (purpose strings, App Tracking Transparency)

### Step 3: Audit Material Design Compliance

If targeting Android, check against Material Design 3:
- Navigation patterns (navigation rail, bottom navigation, drawer)
- Component usage (FAB placement, snackbar vs toast, top app bar)
- Typography (Material Type Scale, Roboto fallback)
- Color system (dynamic color, tonal palettes, color roles)
- Elevation and surfaces (tonal elevation, container hierarchy)
- Back button and predictive back gesture

### Step 4: Audit Web/PWA Compliance

If targeting web, check:
- Responsive breakpoints and layout reflow
- Touch target sizes (48x48px minimum)
- Keyboard navigation and focus management
- WCAG 2.1 AA color contrast and screen reader compatibility
- Progressive Web App criteria (if applicable)

### Step 5: Cross-Platform Consistency Check

For multi-platform features, verify:
- Shared functionality is equivalent (not necessarily identical UI)
- Platform-specific interactions feel native on each platform
- No "lowest common denominator" patterns that feel foreign on any platform

### Step 6: App Store Risk Assessment

Flag any patterns known to trigger review rejection:
- Misleading screenshots or metadata
- Permissions requested without clear justification
- Use of private APIs or undocumented behavior
- In-app purchase and subscription display requirements

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what feature is being audited, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Output Format

```markdown
# Platform Audit Report

## Platforms Evaluated
[iOS | Android | Web | All]

## Compliance Summary
| Platform | Pass | Warn | Fail | Score |
|----------|------|------|------|-------|
| iOS      | N    | N    | N    | X/10  |
| Android  | N    | N    | N    | X/10  |
| Web      | N    | N    | N    | X/10  |

## Findings

### [FAIL] [Platform] — [Finding Title]
**Guideline:** [Specific guideline reference]
**Issue:** [What's wrong]
**Remediation:** [Specific fix]
**Effort:** [Low/Medium/High]

### [WARN] [Platform] — [Finding Title]
**Guideline:** [Specific guideline reference]
**Issue:** [What's suboptimal]
**Recommendation:** [Suggested improvement]

## App Store Risk Assessment
- [Risk and mitigation]

## Cross-Platform Notes
- [Consistency observation]
```

## Handoff

- Hand off to navigation-design if navigation pattern violations require architectural redesign.
- Hand off to device-integration if permission or hardware API compliance issues need integration-level remediation.

## Quality Checks

- [ ] Each finding references a specific platform guideline (not generic "best practice")
- [ ] All FAIL findings include concrete remediation steps
- [ ] Cross-platform features are checked for consistency across platforms
- [ ] App Store / Play Store rejection risks are flagged with mitigation
- [ ] Touch targets, typography, and navigation patterns are verified per platform
- [ ] Permission usage is checked for compliance with privacy requirements

## Evolution Notes
<!-- Observations appended after each use -->
