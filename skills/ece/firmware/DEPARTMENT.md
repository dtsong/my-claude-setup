---
name: Firmware
executive: Firmware
color: olive
description: "Embedded software architecture — ARM Cortex-M, RTOS design, bootloaders, HAL abstraction, IEC 62304 compliance"
---

# Firmware Department

Embedded firmware architecture for medical devices, from HAL and BSP design through RTOS task decomposition to regulatory compliance under IEC 62304. Covers ARM Cortex-M and PIC microcontrollers, bootloader design with secure update mechanisms, and MISRA-C coding standards. Every architecture decision balances real-time performance, patient safety, and regulatory requirements.

## Skills

| Skill | Purpose | Model Tier | Triggers |
|---|---|---|---|
| [rtos-architecture](rtos-architecture/SKILL.md) | Design RTOS task architecture with priorities, stack budgets, and inter-task communication for medical device firmware | claude-opus-4-6 | RTOS, task, priority, FreeRTOS, ThreadX, real-time, scheduling, queue, semaphore, stack |
| [bootloader-design](bootloader-design/SKILL.md) | Design secure bootloader architecture for field-updatable medical device firmware | claude-opus-4-6 | bootloader, firmware update, OTA, secure boot, flash partition, image verification, DFU |
| [iec62304-compliance](iec62304-compliance/SKILL.md) | Assess firmware architecture for IEC 62304 software lifecycle compliance and determine required documentation | claude-opus-4-6 | IEC 62304, software safety, classification, SOUP, software lifecycle, documentation, Class A, Class B, Class C |

## Classification Logic

1. If query mentions RTOS, task architecture, priority, scheduling, FreeRTOS, ThreadX, Zephyr, queue, semaphore, stack budget, or real-time task design --> load `rtos-architecture`
2. If query mentions bootloader, firmware update, OTA, secure boot, flash partition, image verification, DFU, or rollback --> load `bootloader-design`
3. If query mentions IEC 62304, software safety classification, SOUP, software lifecycle, Class A/B/C, or documentation requirements --> load `iec62304-compliance`
4. If query spans multiple skills, load the skill matching the primary design task. Handoff to secondary skills as needed.

## Shared Directives

See `references/department-preamble.md` for cross-cutting directives that apply to all Firmware department skills.
