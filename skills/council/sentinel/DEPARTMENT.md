---
name: "Sentinel Department"
executive: "Sentinel"
color: "Titanium"
description: "IoT, embedded, edge, device protocols"
---

# Sentinel Department — Titanium Lens

The Sentinel's department of focused skills for embedded firmware design, wireless protocol architecture, and fleet-scale device management.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|-------|---------|------------|----------|
| [embedded-architecture](embedded-architecture/SKILL.md) | Firmware design patterns, RTOS selection, memory/power management | default | `firmware`, `RTOS`, `microcontroller`, `bare-metal`, `power`, `battery`, `sleep mode`, `memory`, `flash` |
| [protocol-design](protocol-design/SKILL.md) | Wireless protocol selection, stack design, interoperability | default | `BLE`, `MQTT`, `Matter`, `Thread`, `Zigbee`, `LoRa`, `CoAP`, `protocol`, `wireless`, `radio` |
| [fleet-management](fleet-management/SKILL.md) | Device provisioning, OTA update strategy, fleet monitoring | default | `OTA`, `fleet`, `provisioning`, `update`, `telemetry`, `device management`, `certificate`, `rollout` |

## Classification Logic

| Input Signal | Route To | Confidence |
|-------------|----------|------------|
| Firmware, RTOS, microcontroller, bare-metal, memory layout, power state machine, watchdog | embedded-architecture | High |
| BLE, MQTT, Matter, Thread, Zigbee, LoRa, CoAP, wireless protocol, radio, message format | protocol-design | High |
| OTA, fleet, provisioning, device management, telemetry, rollout, firmware update, certificate | fleet-management | High |
| Battery life optimization, sleep mode design, flash partitioning | embedded-architecture | Medium |
| Device-to-cloud communication pipeline, remote diagnostics | fleet-management | Medium |

## Shared Directives

Load Directive, Handoff Protocol, AskUserQuestion format, and Anti-Sycophancy rules: see [references/department-preamble.md](../references/department-preamble.md).
