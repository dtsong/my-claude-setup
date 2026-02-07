---
name: "Embedded Architecture"
department: "sentinel"
description: "Firmware design patterns, RTOS selection, memory and power management"
version: 1
triggers:
  - "firmware"
  - "RTOS"
  - "microcontroller"
  - "bare-metal"
  - "power"
  - "battery"
  - "sleep mode"
  - "memory"
  - "flash"
  - "embedded"
---

# Embedded Architecture

## Purpose

Design the firmware architecture for an embedded/IoT device, including RTOS selection, memory layout, power state machine, and task decomposition.

## Inputs

- Target hardware (MCU, memory, peripherals, power source)
- Feature requirements (sensing, communication, actuation, UI)
- Power budget and battery life requirements
- Real-time constraints (latency, update frequency)
- Regulatory requirements (FCC, CE, safety)

## Process

### Step 1: Hardware Capability Assessment

Document the hardware constraints:
- **MCU:** Architecture (ARM Cortex-M, RISC-V, ESP32), clock speed, cores
- **Memory:** Flash size (code storage), SRAM size (runtime), external storage
- **Peripherals:** UART, SPI, I2C, ADC, PWM, timers, DMA channels
- **Power source:** Battery capacity, charging method, voltage regulators
- **Radio:** BLE, Wi-Fi, cellular, LoRa — power draw per mode

### Step 2: Select RTOS or Bare-Metal

Decision framework:
- **Bare-metal:** < 3 concurrent tasks, no networking stack, simple timing requirements
- **FreeRTOS:** General-purpose, large ecosystem, good for most IoT applications
- **Zephyr:** Strong networking stack, Matter/Thread support, Linux Foundation backing
- **NuttX:** POSIX-compliant, good for complex applications with file systems
- **Custom RTOS:** Almost never justified — use an existing one

### Step 3: Design Task Architecture

Decompose the firmware into tasks/threads:
- **Sensor task:** Read sensors at defined intervals, buffer data
- **Communication task:** Manage radio connection, send/receive data
- **Application task:** Process data, make decisions, trigger actuators
- **Power management task:** Monitor battery, manage sleep states
- **OTA task:** Check for updates, manage download and apply

Define priorities, stack sizes, and inter-task communication (queues, events, semaphores).

### Step 4: Design Memory Layout

Plan memory allocation:
- **Flash partitions:** Application, OTA staging, file system, configuration
- **RAM allocation:** Task stacks, heap, DMA buffers, ring buffers
- **Static vs dynamic allocation:** Prefer static allocation — malloc on embedded systems is risky
- **Stack overflow protection:** Guard patterns, MPU regions

### Step 5: Design Power State Machine

Define power modes and transitions:
- **Active:** Full speed, all peripherals on
- **Low power:** Reduced clock, unnecessary peripherals off
- **Sleep:** MCU sleeping, RTC running, wake on interrupt
- **Deep sleep:** Minimum power, RAM retention optional, slow wake-up
- **Transitions:** What triggers each transition, wake-up latency, power consumption per mode

### Step 6: Design Watchdog and Recovery

Plan for failure recovery:
- **Watchdog timer:** Hardware watchdog with appropriate timeout
- **Task health monitoring:** Each task must pet a software watchdog
- **Crash recovery:** Save crash dump to flash, reboot, report crash on next connection
- **Fail-safe defaults:** If firmware is corrupted, boot into recovery/OTA mode

## Output Format

```markdown
# Embedded Architecture

## Hardware Summary
| Component | Specification | Constraint |
|-----------|--------------|------------|
| MCU | [Model] | [Clock, cores] |
| Flash | [Size] | [Partitioning plan] |
| SRAM | [Size] | [Allocation plan] |
| Battery | [Capacity] | [Target life: X months] |

## RTOS Selection
**Choice:** [RTOS name]
**Rationale:** [Why this RTOS for this hardware and requirements]

## Task Architecture
| Task | Priority | Stack Size | Rate | Description |
|------|----------|-----------|------|-------------|
| Sensor | High | 2KB | 1Hz | Read and buffer sensor data |
| Comms | Medium | 4KB | Event | BLE/MQTT communication |
| App | Medium | 2KB | On data | Process and decide |
| Power | Low | 1KB | 10s | Monitor and manage power states |

## Memory Layout
### Flash (Xkb)
| Partition | Start | Size | Purpose |
|-----------|-------|------|---------|
| Bootloader | 0x0000 | 32KB | Boot and OTA |
| App A | 0x8000 | 448KB | Active firmware |
| App B | 0x78000 | 448KB | OTA staging |
| NVS | 0xE8000 | 32KB | Configuration |

### RAM (Xkb)
| Region | Size | Purpose |
|--------|------|---------|
| Task stacks | 12KB | All task stacks |
| Heap | 8KB | Dynamic allocation (minimized) |
| DMA buffers | 4KB | Peripheral DMA |

## Power State Machine
```
[Active] --idle 5s--> [Low Power] --idle 30s--> [Sleep] --idle 5min--> [Deep Sleep]
    ^                       ^                       ^                       |
    |---sensor event--------|---BLE event-----------|---RTC alarm-----------|
```

| State | Power Draw | Wake Latency | Wake Sources |
|-------|-----------|-------------|--------------|
| Active | 50mA | — | — |
| Low Power | 5mA | <1ms | Any interrupt |
| Sleep | 500μA | 5ms | BLE, GPIO, timer |
| Deep Sleep | 10μA | 500ms | RTC alarm |

## Recovery Strategy
- [Watchdog configuration]
- [Crash dump approach]
- [Fail-safe boot mode]
```

## Quality Checks

- [ ] All task stack sizes are justified (not just "big enough")
- [ ] Memory layout accounts for OTA dual-partition scheme
- [ ] Power state machine has defined transitions and wake sources
- [ ] Watchdog timeout is appropriate for the slowest legitimate operation
- [ ] Static allocation is preferred over dynamic — heap usage is justified
- [ ] Battery life estimate is calculated from power state duty cycle

## Evolution Notes
<!-- Observations appended after each use -->
