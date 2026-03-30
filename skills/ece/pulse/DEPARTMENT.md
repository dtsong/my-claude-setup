---
name: "Pulse Department"
executive: "Pulse"
color: "Crimson"
description: "Medical ultrasound systems — piezoelectric transducers, phased-array beamforming, high-voltage pulsers"
---

# Pulse Department — Crimson Lens

The Pulse department specializes in medical ultrasound system design, covering piezoelectric transducer modeling, phased-array beamforming architectures, and high-voltage transmit pulser circuits. All designs must meet IEC 60601 safety requirements and FDA acoustic output limits.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [transducer-design](transducer-design/SKILL.md) | Piezoelectric transducer modeling | default | `transducer`, `piezoelectric`, `PZT`, `matching layer`, `backing`, `acoustic impedance` |
| [beamformer-architecture](beamformer-architecture/SKILL.md) | Phased-array beamforming design | default | `beamforming`, `phased array`, `delay-and-sum`, `apodization`, `steering`, `focusing` |
| [pulser-design](pulser-design/SKILL.md) | High-voltage transmit pulser design | default | `pulser`, `transmit`, `high-voltage`, `HV driver`, `bipolar pulse`, `T/R switch` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves piezoelectric element selection, acoustic stack modeling, or matching layer optimization | transducer-design | High |
| Request involves beamforming algorithm design, channel delay calculation, or aperture synthesis | beamformer-architecture | High |
| Request involves high-voltage pulser topology, transmit waveform shaping, or T/R switch design | pulser-design | High |
| Request mentions transducer bandwidth, sensitivity, or element pitch selection | transducer-design | Medium |
| Request mentions receive signal conditioning, TGC, or digital beamformer FPGA implementation | beamformer-architecture | Medium |
| Request mentions transmit voltage rails, MOSFET driver selection, or pulse repetition frequency | pulser-design | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
