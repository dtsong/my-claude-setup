---
name: "Integrator Department"
executive: "Integrator"
color: "Cobalt"
description: "Systems engineering, requirements decomposition, V-model, cross-functional integration"
---

# Integrator Department — Cobalt Lens

The Integrator's department of focused skills for systems engineering, requirements management, interface control, and V-model lifecycle planning.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [requirements-decomposition](requirements-decomposition/SKILL.md) | Decompose system-level requirements into subsystem specifications with traceability | default | `requirements`, `decomposition`, `specification`, `subsystem`, `design input`, `traceability` |
| [interface-control](interface-control/SKILL.md) | Define and manage interfaces between subsystems and with external systems | default | `interface`, `ICD`, `connector`, `signal`, `boundary`, `protocol`, `pinout`, `mechanical interface` |
| [v-model-planning](v-model-planning/SKILL.md) | Plan verification and validation activities aligned to the V-model lifecycle | default | `V-model`, `V&V`, `verification`, `validation`, `design review`, `test plan`, `qualification` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves decomposing system requirements into subsystem specs, allocating requirements, or building traceability matrices | requirements-decomposition | High |
| Request involves defining interfaces between subsystems, ICDs, connector pinouts, signal definitions, or protocol selection | interface-control | High |
| Request involves V-model planning, verification methods, design reviews (PDR/CDR/TRR), or V&V scheduling | v-model-planning | High |
| Request mentions DOORS or JAMA traceability, design inputs/outputs, or requirements management | requirements-decomposition | Medium |
| Request mentions cross-functional integration, subsystem boundaries, or system block diagrams | interface-control | Medium |
| Request mentions design transfer, qualification testing, or test plan development | v-model-planning | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
