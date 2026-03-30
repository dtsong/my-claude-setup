---
name: Analog
executive: Analog
color: amber
description: "Low-noise precision analog design — biopotential front-ends, signal conditioning, noise budgets, ADC interfacing"
---

# Analog Department

Precision analog signal chain design from transducer/electrode to ADC. Covers instrumentation amplifiers, anti-aliasing filters, driven-right-leg circuits, precision references, and noise budget analysis. Every component choice is justified quantitatively.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|---|---|---|---|
| [noise-analysis](noise-analysis/SKILL.md) | Build complete noise budget for an analog signal chain, identifying dominant contributors and optimization opportunities | claude-opus-4-6 | noise, SNR, noise budget, input-referred, spectral density, noise floor, resolution, dynamic range |
| [front-end-design](front-end-design/SKILL.md) | Design biopotential or sensor analog front-end topology from electrode/transducer to ADC input | claude-opus-4-6 | front end, biopotential, ECG, EEG, electrode, instrumentation amplifier, analog front end, ADS1299, signal conditioning |
| [defibrillation-protection](defibrillation-protection/SKILL.md) | Design defibrillation withstand protection for patient-connected analog circuits per IEC 60601-1 Clause 8.5.5 | claude-opus-4-6 | defibrillation, defib protection, high voltage, CF applied part, energy clamping, surge, patient protection |

## Classification Logic

1. If query mentions noise, SNR, noise budget, spectral density, noise floor, resolution, dynamic range, or input-referred noise --> load `noise-analysis`
2. If query mentions front end, biopotential, ECG, EEG, EMG, electrode, instrumentation amplifier, analog front end, ADS1299, or signal conditioning --> load `front-end-design`
3. If query mentions defibrillation, defib protection, high voltage, CF applied part, energy clamping, surge, or patient protection --> load `defibrillation-protection`
4. If query spans multiple skills, load the skill matching the primary design task. Handoff to secondary skills as needed.

## Shared Directives

See `references/department-preamble.md` for cross-cutting directives that apply to all Analog department skills.
