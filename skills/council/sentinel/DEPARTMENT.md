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

## Load Directive

Load one specialist skill at a time using the Skill tool. Read the classification logic table to select the appropriate specialist, then invoke the skill. Do not pre-load multiple specialists simultaneously.

## Handoff Protocol

When the specialist skill output reveals issues in another department's domain:
1. Complete the current skill's output format.
2. Note the cross-domain findings in the output.
3. Recommend loading the appropriate department and skill (e.g., "Hand off device security concerns to skeptic/threat-model for threat analysis").
