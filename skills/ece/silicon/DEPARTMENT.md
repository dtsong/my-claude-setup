---
name: "Silicon Department"
executive: "Silicon"
color: "Graphite"
description: "ASIC/FPGA design — RTL architecture, synthesis, HW/SW partitioning, timing closure"
---

# Silicon Department — Graphite Lens

The Silicon department owns ASIC and FPGA design disciplines including RTL architecture, synthesis optimization, HW/SW partitioning decisions, and timing closure. All reviews enforce silicon-proven methodology with quantitative area, power, and timing targets.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [hw-sw-partitioning](hw-sw-partitioning/SKILL.md) | ASIC/FPGA/software boundary analysis | default | `partitioning`, `HW/SW`, `boundary`, `offload`, `acceleration`, `coprocessor` |
| [fpga-architecture](fpga-architecture/SKILL.md) | FPGA resource planning and constraints | default | `FPGA`, `resource`, `constraints`, `fabric`, `CLB`, `block RAM`, `DSP slice` |
| [verification-strategy](verification-strategy/SKILL.md) | Simulation, formal, and emulation strategy | default | `verification`, `simulation`, `formal`, `emulation`, `UVM`, `testbench`, `coverage` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves deciding what functions belong in hardware vs. software, acceleration trade-offs, or coprocessor offload | hw-sw-partitioning | High |
| Request involves FPGA resource estimation, floorplanning, pin constraints, or fabric utilization | fpga-architecture | High |
| Request involves simulation strategy, formal verification, UVM testbenches, or coverage closure | verification-strategy | High |
| Request mentions SoC architecture, processor selection, or IP integration trade-offs | hw-sw-partitioning | Medium |
| Request mentions timing closure, synthesis constraints, or clock domain crossing | fpga-architecture | Medium |
| Request mentions regression testing, emulation platforms, or assertion-based verification | verification-strategy | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
