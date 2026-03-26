---
name: "Foundry Department"
executive: "Foundry"
color: "Copper"
description: "Constructive chip design, verification methodology, SoC integration, EDA flows"
---

# Foundry Department — Copper Lens

The Foundry's department of focused skills for constructive hardware design, from RTL authoring through verification closure and SoC integration to tape-out.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [chip-design-flow](chip-design-flow/SKILL.md) | RTL-to-GDSII flow with synthesis and physical design | default | `RTL`, `synthesis`, `tape-out`, `place and route`, `timing closure`, `SDC` |
| [verification-methodology](verification-methodology/SKILL.md) | UVM testbench architecture and coverage-driven closure | default | `UVM`, `verification`, `coverage`, `constrained random`, `assertions`, `formal` |
| [soc-integration](soc-integration/SKILL.md) | SoC bus fabric, memory map, IP qualification, DFT | default | `SoC`, `AMBA`, `AXI`, `IP integration`, `DFT`, `register map` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| RTL authoring, synthesis, place-and-route, timing closure, SDC constraints, floor plan, GDSII, tape-out, EDA flow | chip-design-flow | High |
| UVM, testbench, coverage-driven verification, constrained random, assertions, formal verification, coverage closure | verification-methodology | High |
| SoC integration, AMBA/AXI bus, memory map, interrupt controller, IP qualification, DFT, scan, BIST, ATPG | soc-integration | High |
| General RTL design quality or coding style questions | chip-design-flow | Medium |
| Block-level verification planning | verification-methodology | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
