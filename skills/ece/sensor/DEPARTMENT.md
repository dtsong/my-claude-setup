---
name: "Sensor Department"
executive: "Sensor"
color: "Jade"
description: "Biosensor electronics — potentiostat design, electrode interfaces, wearable form factor integration"
---

# Sensor Department — Jade Lens

The Sensor department covers biosensor electronics from electrochemical measurement front-ends through electrode interfaces to wearable form factor integration. Designs prioritize low-noise analog performance, biocompatibility constraints, and miniaturization for on-body devices.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [potentiostat-design](potentiostat-design/SKILL.md) | Electrochemical measurement circuits | default | `potentiostat`, `electrochemical`, `amperometry`, `voltammetry`, `TIA`, `working electrode` |
| [electrode-interface](electrode-interface/SKILL.md) | Skin-electrode and micro-needle design | default | `electrode`, `skin contact`, `micro-needle`, `impedance`, `biocompatible`, `AgCl` |
| [wearable-form-factor](wearable-form-factor/SKILL.md) | Wearable mechanical/electrical integration | default | `wearable`, `form factor`, `flex PCB`, `enclosure`, `IP rating`, `body-worn` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves potentiostat circuit topology, transimpedance amplifier sizing, or electrochemical measurement technique selection | potentiostat-design | High |
| Request involves electrode material selection, skin-electrode impedance modeling, or micro-needle fabrication | electrode-interface | High |
| Request involves wearable enclosure design, flex-rigid PCB layout, or IP-rated sealing for body-worn devices | wearable-form-factor | High |
| Request mentions analog front-end noise budget, DAC-driven voltage control, or sensor calibration circuitry | potentiostat-design | Medium |
| Request mentions biocompatibility testing, electrode drift compensation, or contact impedance reduction | electrode-interface | Medium |
| Request mentions battery compartment design, wearable antenna placement, or sweat/moisture ingress protection | wearable-form-factor | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
