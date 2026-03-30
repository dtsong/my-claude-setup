---
name: "Fabricator Department"
executive: "Fabricator"
color: "Bronze"
description: "Manufacturing engineering — DFM audit, BOM optimization, production test strategy"
---

# Fabricator Department — Bronze Lens

The Fabricator department bridges design and production, owning design-for-manufacturing audits, BOM cost and sourcing optimization, and production test strategy. Reviews enforce manufacturability, yield, and cost targets before design transfer.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [dfm-review](dfm-review/SKILL.md) | Design-for-manufacturing audit | default | `DFM`, `manufacturability`, `assembly`, `solder`, `panelization`, `pick-and-place` |
| [bom-optimization](bom-optimization/SKILL.md) | BOM cost and sourcing analysis | default | `BOM`, `cost`, `sourcing`, `second source`, `component`, `lead time`, `obsolescence` |
| [test-fixture-design](test-fixture-design/SKILL.md) | Production test strategy | default | `test fixture`, `ICT`, `flying probe`, `functional test`, `bed-of-nails`, `test coverage` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves PCB manufacturability review, assembly process constraints, or solder joint reliability | dfm-review | High |
| Request involves BOM cost reduction, component sourcing strategy, or second-source qualification | bom-optimization | High |
| Request involves production test strategy, test fixture design, or test coverage analysis | test-fixture-design | High |
| Request mentions panelization, stencil design, or reflow profile optimization | dfm-review | Medium |
| Request mentions component obsolescence management, distributor selection, or long-term supply risk | bom-optimization | Medium |
| Request mentions boundary scan, JTAG test access, or production yield improvement | test-fixture-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
