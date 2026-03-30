---
name: Tracer
executive: Tracer — The Teal Lens
color: Teal
description: "Mixed-signal PCB design, stackup architecture, signal integrity, power integrity, and EMC/EMI compliance"
---

# Tracer Department — Teal Lens

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| stackup-design | Design PCB layer stackup optimized for SI, PI, and EMC | opus | stackup, layer, impedance, controlled impedance, dielectric, prepreg, core, cross-section |
| emc-strategy | Board-level EMC/EMI compliance strategy for medical device per IEC 60601-1-2 | opus | EMC, EMI, radiated, conducted, emissions, immunity, ESD, surge, IEC 61000, CISPR, shielding, filtering |
| power-integrity | Design and validate power delivery network from regulator to IC pins | opus | PDN, power integrity, decoupling, target impedance, ripple, voltage drop, power plane, capacitor |

## Classification Logic

1. If the query involves layer stackup, impedance control, dielectric selection, or cross-section geometry -> load `stackup-design`.
2. If the query involves EMC/EMI compliance, emissions, immunity, shielding, or filtering strategy -> load `emc-strategy`.
3. If the query involves power delivery, decoupling, target impedance, or voltage drop analysis -> load `power-integrity`.
4. If the query spans multiple skills, load the skill closest to the root cause. Stackup issues are root; EMC and PI are downstream.
5. If ambiguous, ask one clarifying question before loading a skill.

## Shared Directives

See `references/department-preamble.md` for cross-cutting directives applied to all Tracer skills.
