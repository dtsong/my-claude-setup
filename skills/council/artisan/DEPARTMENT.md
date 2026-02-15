---
name: "Artisan Department"
executive: "Artisan"
color: "Rose"
description: "Visual design, design systems, motion"
---

# Artisan Department — Rose Lens

The Artisan's department of focused skills for visual design critique, design token architecture, and motion design.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [visual-audit](visual-audit/SKILL.md) | Structured visual design critique with actionable feedback | default | `visual`, `design review`, `UI audit`, `hierarchy`, `contrast`, `spacing`, `typography`, `color` |
| [design-system-architecture](design-system-architecture/SKILL.md) | Token hierarchy, theming, cross-platform consistency | default | `design system`, `design tokens`, `theme`, `dark mode`, `CSS variables`, `Figma`, `Storybook` |
| [motion-design](motion-design/SKILL.md) | Animation principles, micro-interactions, reduced-motion | default | `animation`, `transition`, `motion`, `easing`, `micro-interaction`, `reduced-motion`, `choreography` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Visual hierarchy, contrast ratios, spacing issues, typography critique, color palette review, UI audit | visual-audit | High |
| Design tokens, theming strategy, dark mode architecture, CSS variables, Figma-to-code, component library tokens | design-system-architecture | High |
| Animation specs, transition choreography, micro-interactions, easing curves, reduced-motion support, loading states | motion-design | High |
| General design review mentioning both layout and token structure | visual-audit | Medium |
| Component styling consistency across platforms | design-system-architecture | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off component implementation patterns to craftsman/pattern-analysis for code pattern assessment").
