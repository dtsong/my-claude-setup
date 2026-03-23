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

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
