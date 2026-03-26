---
name: "Advocate Department"
executive: "Advocate"
color: "Green"
description: "User experience, journey mapping, interaction design"
---

# Advocate Department — Green Lens

The Advocate's department of focused skills for championing the user's perspective through structured UX methodology.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [journey-mapping](journey-mapping/SKILL.md) | User journey mapping with states and emotions | default | `user flow`, `journey`, `onboarding`, `experience`, `workflow` |
| [interaction-design](interaction-design/SKILL.md) | Component specs with all interaction states | default | `component`, `UI`, `interaction`, `modal`, `form`, `button` |
| [a11y-audit](a11y-audit/SKILL.md) | WCAG 2.2 AA compliance audit | default | `accessibility`, `a11y`, `WCAG`, `screen reader`, `ARIA` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| User flow, journey, onboarding, multi-step workflow, entry points, happy path, persona, experience mapping | journey-mapping | High |
| Component, UI states, interaction, modal, form, button, dropdown, hover, focus, animation | interaction-design | High |
| Accessibility audit, WCAG compliance, screen reader, keyboard navigation, ARIA, color contrast, reduced motion | a11y-audit | High |
| Feature with both user flows and component specs | journey-mapping then interaction-design | High |
| General UX review, usability concerns, user-facing feature assessment | journey-mapping | Medium |
| Design system component, responsive behavior, state management for UI elements | interaction-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
