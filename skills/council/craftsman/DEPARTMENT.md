---
name: "Craftsman Department"
executive: "Craftsman"
color: "Purple"
description: "Testing strategy, code quality, pattern analysis"
---

# Craftsman Department — Purple Lens

The Craftsman's department of focused skills for ensuring code quality, test coverage, and pattern consistency.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [testing-strategy](testing-strategy/SKILL.md) | Test plan with coverage targets and test pyramid | default | `test`, `testing`, `coverage`, `unit test`, `e2e` |
| [pattern-analysis](pattern-analysis/SKILL.md) | Codebase pattern audit and convention enforcement | default | `pattern`, `convention`, `consistency`, `refactor`, `code quality` |

## Classification Logic

| Input Signal | Route To | Confidence |
|--------------|----------|------------|
| Request mentions test plans, coverage targets, test pyramid, or TDD | testing-strategy | High |
| Request mentions pattern audit, convention enforcement, or code consistency | pattern-analysis | High |
| Request mentions refactoring with emphasis on maintaining existing patterns | pattern-analysis | Medium |
| Request mentions CI quality gates or regression testing setup | testing-strategy | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
