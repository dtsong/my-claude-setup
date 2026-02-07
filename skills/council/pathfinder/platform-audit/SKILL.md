---
name: "Platform Audit"
department: "pathfinder"
description: "Platform guideline compliance audit across iOS, Android, and web"
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

## Inputs

- Feature description or UI mockup being evaluated
- Target platforms (iOS, Android, Web, or cross-platform)
- Existing implementation code (if available)
- App Store / Play Store submission history (if relevant)

## Process

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

## Quality Checks

- [ ] Each finding references a specific platform guideline (not generic "best practice")
- [ ] All FAIL findings include concrete remediation steps
- [ ] Cross-platform features are checked for consistency across platforms
- [ ] App Store / Play Store rejection risks are flagged with mitigation
- [ ] Touch targets, typography, and navigation patterns are verified per platform
- [ ] Permission usage is checked for compliance with privacy requirements

## Evolution Notes
<!-- Observations appended after each use -->
