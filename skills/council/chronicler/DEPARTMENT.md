---
name: "Chronicler Department"
executive: "Chronicler"
color: "Ivory"
description: "Documentation, knowledge architecture, onboarding"
---

# Chronicler Department — Ivory Lens

The Chronicler's department of focused skills for documentation architecture, decision records, and knowledge management.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [documentation-plan](documentation-plan/SKILL.md) | Documentation architecture and onboarding paths | default | `documentation`, `docs`, `README`, `guide`, `onboarding` |
| [adr-template](adr-template/SKILL.md) | Architecture Decision Record creation | default | `ADR`, `decision`, `architecture decision`, `rationale` |
| [changelog-design](changelog-design/SKILL.md) | Changelog and migration guide for breaking changes | default | `changelog`, `migration guide`, `upgrade`, `breaking change` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| `documentation`, `docs`, `README`, `guide`, `onboarding`, `wiki`, `tutorial` | documentation-plan | High |
| `ADR`, `architecture decision`, `decision record`, `design decision`, `rationale` | adr-template | High |
| `changelog`, `migration guide`, `breaking change`, `release notes`, `deprecation`, `semver` | changelog-design | High |
| `upgrade` with breaking change context | changelog-design | Medium |
| `tradeoff`, `decision` without explicit ADR mention | adr-template | Medium |

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off API documentation gaps to architect/api-design for interface specification").
