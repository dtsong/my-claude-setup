---
name: "Link Department"
executive: "Link"
color: "Indigo"
description: "Connectivity engineering — wireless radio and antenna design, protocol selection, connected device cybersecurity"
---

# Link Department — Indigo Lens

The Link department covers connectivity engineering from RF front-end and antenna design through protocol selection to connected device cybersecurity. Designs balance range, power consumption, regulatory compliance, and security posture for wireless-enabled products.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [wireless-design](wireless-design/SKILL.md) | BLE/Wi-Fi radio and antenna design | default | `wireless`, `BLE`, `Wi-Fi`, `antenna`, `RF`, `radio`, `link budget`, `matching network` |
| [protocol-selection](protocol-selection/SKILL.md) | Communication protocol trade-off analysis | default | `protocol`, `BLE`, `Zigbee`, `Thread`, `LoRa`, `MQTT`, `data rate`, `range` |
| [cybersecurity-review](cybersecurity-review/SKILL.md) | Connected device cybersecurity assessment | default | `cybersecurity`, `security`, `encryption`, `OTA update`, `authentication`, `threat model` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Request involves antenna design, RF matching network, link budget analysis, or radio front-end component selection | wireless-design | High |
| Request involves wireless protocol comparison, data rate vs. range trade-offs, or network topology selection | protocol-selection | High |
| Request involves device security architecture, threat modeling, encryption implementation, or secure boot | cybersecurity-review | High |
| Request mentions PCB antenna layout, SAR testing, or FCC/CE regulatory pre-compliance | wireless-design | Medium |
| Request mentions coexistence between wireless protocols, gateway architecture, or mesh networking | protocol-selection | Medium |
| Request mentions OTA firmware update security, key provisioning, or vulnerability assessment | cybersecurity-review | Medium |

## Shared Directives

Load Directive, Handoff Protocol, EE-Specific Standards, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
