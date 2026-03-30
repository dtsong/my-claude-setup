---
name: "Thermal Department"
executive: "Thermal"
color: "Rust"
description: "Thermal and reliability engineering — thermal simulation, component derating, environmental qualification"
---

# Thermal Department — Rust Lens

The Thermal department owns thermal management and reliability engineering, covering thermal simulation and heatsink design, component derating analysis, and environmental qualification planning. All thermal designs require quantitative junction temperature budgets and worst-case ambient analysis.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [thermal-simulation](thermal-simulation/SKILL.md) | Thermal modeling and heatsink design | default | `thermal`, `heatsink`, `junction temperature`, `thermal resistance`, `CFD`, `heat dissipation` |
| [derating-analysis](derating-analysis/SKILL.md) | Component derating and reliability | default | `derating`, `reliability`, `MTBF`, `FIT rate`, `stress ratio`, `lifetime`, `Arrhenius` |
| [environmental-qualification](environmental-qualification/SKILL.md) | HALT/HASS/environmental test planning | default | `HALT`, `HASS`, `environmental test`, `thermal cycling`, `vibration`, `humidity`, `qualification` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves thermal modeling, heatsink selection, thermal via optimization, or junction temperature calculation | thermal-simulation | High |
| Request involves component derating policy, reliability prediction, MTBF calculation, or stress analysis | derating-analysis | High |
| Request involves HALT/HASS test planning, thermal cycling profiles, or environmental qualification strategy | environmental-qualification | High |
| Request mentions airflow analysis, thermal interface material selection, or enclosure thermal management | thermal-simulation | Medium |
| Request mentions component lifetime estimation, Arrhenius acceleration factors, or failure rate databases | derating-analysis | Medium |
| Request mentions IP rating qualification, salt spray testing, or shock and vibration profiles | environmental-qualification | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
