---
name: "Power Department"
executive: "Power"
color: "Copper"
description: "Power electronics — system power architecture, battery management, switching converters, isolation topologies"
---

# Power Department — Copper Lens

The Power department owns system power architecture from source to load, including battery management, switching converter design, and isolation topologies. Every design is held to quantitative efficiency, thermal, and EMI targets with worst-case analysis across the full operating envelope.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [power-tree-design](power-tree-design/SKILL.md) | System power architecture | default | `power tree`, `power architecture`, `rail`, `LDO`, `buck`, `boost`, `sequencing` |
| [bms-design](bms-design/SKILL.md) | Battery management system design | default | `BMS`, `battery`, `cell balancing`, `fuel gauge`, `charging`, `protection`, `SoC estimation` |
| [isolation-design](isolation-design/SKILL.md) | High-voltage isolation topology | default | `isolation`, `isolated`, `galvanic`, `optocoupler`, `transformer`, `creepage`, `clearance` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves system power tree definition, voltage rail planning, regulator selection, or power sequencing | power-tree-design | High |
| Request involves battery pack design, cell balancing, charge profile, or fuel gauging algorithms | bms-design | High |
| Request involves galvanic isolation topology, isolation barrier component selection, or safety-rated creepage/clearance | isolation-design | High |
| Request mentions load transient analysis, efficiency optimization, or thermal derating of regulators | power-tree-design | Medium |
| Request mentions battery safety certification, cell chemistry trade-offs, or shipping compliance | bms-design | Medium |
| Request mentions medical isolation standards, reinforced insulation, or isolated power supply design | isolation-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
