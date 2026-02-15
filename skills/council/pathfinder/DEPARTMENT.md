---
name: "Pathfinder Department"
executive: "Pathfinder"
color: "Coral"
description: "Mobile, cross-platform, native apps"
---

# Pathfinder Department — Coral Lens

The Pathfinder's department of focused skills for mobile development, cross-platform architecture, and native platform integration.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [platform-audit](platform-audit/SKILL.md) | Platform guideline compliance across iOS, Android, web | default | `iOS`, `Android`, `HIG`, `Material Design`, `platform`, `guideline`, `compliance`, `app review` |
| [navigation-design](navigation-design/SKILL.md) | Mobile navigation patterns, deep linking, state preservation | default | `navigation`, `deep link`, `universal link`, `tab bar`, `stack`, `routing`, `back button`, `state restoration` |
| [device-integration](device-integration/SKILL.md) | Hardware API integration — sensors, permissions, biometrics | default | `camera`, `GPS`, `biometric`, `Face ID`, `NFC`, `haptic`, `sensor`, `permission`, `bluetooth` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| iOS HIG, Android Material Design, platform guidelines, App Store compliance, Play Store review, app review rejection | platform-audit | High |
| Navigation stack, deep linking, universal links, tab bar, screen flow, routing, state restoration | navigation-design | High |
| Camera, GPS, biometrics, Face ID, NFC, Bluetooth, sensors, permissions, haptics, push notifications | device-integration | High |
| Cross-platform UI consistency, responsive design, platform-specific overrides | platform-audit | Medium |
| Permission flow design, hardware fallback behavior with navigation implications | device-integration then navigation-design | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off API integration findings to architect/api-design for interface specification").
