---
name: "Shield Department"
executive: "Shield"
color: "Slate"
description: "Patient safety, leakage current, creepage/clearance, FMEA, single-fault analysis"
---

# Shield Department — Slate Lens

The Shield's department of focused skills for ensuring patient and operator safety through rigorous IEC 60601-1 analysis, leakage current budgeting, and systematic fault evaluation.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [safety-analysis](safety-analysis/SKILL.md) | IEC 60601-1 safety analysis — applied parts, hazard voltages, MOPP/MOOP, creepage/clearance | default | `safety`, `IEC 60601`, `applied part`, `classification`, `MOPP`, `MOOP`, `isolation`, `hazard` |
| [leakage-current](leakage-current/SKILL.md) | Patient, touch, and earth leakage current analysis under normal and single-fault conditions | default | `leakage current`, `patient current`, `touch current`, `earth leakage`, `normal condition`, `single fault` |
| [single-fault-analysis](single-fault-analysis/SKILL.md) | Systematic single-fault evaluation of safety-critical components with FMEA methodology | default | `single fault`, `fault condition`, `component failure`, `open circuit`, `short circuit`, `FMEA` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Safety analysis, applied part classification, MOPP/MOOP count, creepage, clearance, isolation | safety-analysis | High |
| Leakage current, patient current, touch current, earth leakage, Y-capacitor, impedance path | leakage-current | High |
| Single fault, component failure, FMEA, failure mode, fault condition, open/short circuit | single-fault-analysis | High |
| IEC 60601 general compliance question without specific subsystem focus | safety-analysis | Medium |
| Single-fault leakage current analysis (overlaps both domains) | leakage-current then single-fault-analysis | Medium |
| Risk assessment with both hazard identification and failure mode analysis | safety-analysis then single-fault-analysis | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
