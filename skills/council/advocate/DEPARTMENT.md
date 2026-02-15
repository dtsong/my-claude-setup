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

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| User flow, journey, onboarding, multi-step workflow, entry points, happy path, persona, experience mapping | journey-mapping | High |
| Component, UI states, interaction, modal, form, button, dropdown, hover, focus, animation, accessibility | interaction-design | High |
| Feature with both user flows and component specs | journey-mapping then interaction-design | High |
| General UX review, usability concerns, user-facing feature assessment | journey-mapping | Medium |
| Design system component, responsive behavior, state management for UI elements | interaction-design | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off interaction pattern implementation needs to craftsman/pattern-analysis for code pattern assessment").
