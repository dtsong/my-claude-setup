---
name: rtos-architecture
department: firmware
description: "Design RTOS task architecture with priorities, stack budgets, and inter-task communication for medical device firmware"
version: 1
triggers:
  - RTOS
  - task
  - priority
  - FreeRTOS
  - ThreadX
  - real-time
  - scheduling
  - queue
  - semaphore
  - stack
---

# RTOS Architecture

## Purpose

Design a complete RTOS task architecture for a medical device firmware system. Define tasks, priorities, stack budgets, inter-task communication, shared resource protection, and health monitoring. Produce a schedulability analysis proving all tasks meet deadlines under worst-case conditions.

## Scope Constraints

- Medical device firmware running on ARM Cortex-M or PIC32 microcontrollers
- RTOS candidates: FreeRTOS, ThreadX, Zephyr (not bare-metal superloop designs)
- Does not cover HAL or BSP design — assumes hardware abstraction exists
- Does not cover IEC 62304 documentation — handoff to iec62304-compliance for regulatory artifacts
- Task count typically 4-20; beyond 20, question decomposition granularity

## Inputs

- System requirements: all firmware functions with real-time constraints (period, deadline, jitter tolerance)
- MCU specifications: core speed, RAM size, number of interrupt priority levels
- RTOS selection: which RTOS, or request recommendation
- Peripheral list: which peripherals generate interrupts or require DMA
- Safety classification: which functions are safety-critical (IEC 62304 Class B or C)

## Input Sanitization

- Reject requests without defined deadlines — task priority without deadlines is guesswork
- If MCU is unspecified, flag as assumption and use a representative Cortex-M4 at 120 MHz
- Verify that interrupt priority count matches MCU architecture (Cortex-M typically 4-8 bits)
- Confirm RTOS tick rate is specified or assume 1 kHz default

## Procedure

1. **Enumerate firmware functions.** List every firmware function with its real-time requirements: periodic rate (ms), latency deadline (ms), jitter tolerance (us), and whether it is safety-critical. Include ISR-driven functions separately.

2. **Group functions into tasks.** Assign functions to tasks based on rate and priority using rate-monotonic assignment (shorter period = higher priority) or deadline-monotonic assignment (shorter deadline = higher priority). Co-locate functions with identical rates and no conflicting safety classes. ISR handlers are not tasks — keep ISRs minimal (set flag, queue data, defer processing to task).

3. **Define inter-task communication.** For each data flow between tasks, select the mechanism: message queue (producer/consumer, buffered), event flag group (signaling without data), binary/counting semaphore (synchronization), or shared variable with mutex (bidirectional access). Document data size, maximum queue depth, and worst-case latency through each channel.

4. **Calculate stack budget per task.** For each task, estimate stack usage: local variables in deepest call path + RTOS context save + ISR nesting overhead + safety margin. Safety margin is typically 1.5-2x calculated usage. Use RTOS stack watermark feature for runtime validation. Sum all task stacks + RTOS kernel objects + ISR stack to get total RAM usage.

5. **Analyze schedulability.** Perform response-time analysis for each task: R_i = C_i + sum(ceil(R_i / T_j) * C_j) for all higher-priority tasks j. Verify R_i <= D_i for all tasks. Calculate total CPU utilization: U = sum(C_i / T_i). Utilization should be below 70% to provide margin for jitter, cache misses, and future growth.

6. **Design watchdog and health monitoring.** Define system-level watchdog timeout. Implement task-level heartbeat: each task must check in within its period or a stuck-task fault is raised. Define recovery actions per fault type: task restart, subsystem reset, full system reset, or safe-state entry.

### Progress Checklist

- [ ] All firmware functions enumerated with real-time requirements
- [ ] Functions grouped into tasks with priority assignment rationale
- [ ] Inter-task communication defined for all data flows
- [ ] Stack budget calculated per task with safety margin
- [ ] Schedulability analysis completed — all tasks meet deadlines
- [ ] Watchdog and health monitoring strategy defined

### Compaction Resilience

If context is compacted mid-analysis, the Task Table and Inter-Task Communication Table contain all values needed to resume. These two tables plus the RAM Budget summary capture the complete architecture state.

## Output Format

```markdown
## RTOS Architecture: [System Name]

### System Parameters
- MCU: [part number] @ [clock speed]
- RTOS: [name, version]
- Tick rate: [Hz]
- Interrupt priority levels: [count]

### Task Table
| Task | Priority | Period (ms) | WCET (ms) | Deadline (ms) | Stack (bytes) | Safety Class | Functions |
|---|---|---|---|---|---|---|---|
| | | | | | | | |

### ISR Table
| ISR | Priority | Source | Max Duration (us) | Deferred Task |
|---|---|---|---|---|
| | | | | |

### Inter-Task Communication
| Channel | Type | Producer | Consumer | Element Size | Queue Depth | Max Latency (ms) |
|---|---|---|---|---|---|---|
| | | | | | | |

### Shared Resource Table
| Resource | Protection | Owner Tasks | Max Hold Time (us) | Priority Ceiling |
|---|---|---|---|---|
| | | | | |

### Schedulability Analysis
| Task | WCRT (ms) | Deadline (ms) | Margin (ms) | Pass |
|---|---|---|---|---|
| | | | | |
- Total CPU utilization: [%]
- Utilization margin: [%] (target < 70%)

### RAM Budget
| Category | Size (bytes) |
|---|---|
| Task stacks (total) | |
| RTOS kernel objects | |
| ISR stack | |
| Application data | |
| **Total** | |
| MCU RAM available | |
| **Margin** | [%] |

### Watchdog Strategy
- System watchdog timeout: [ms]
- Task heartbeat mechanism: [description]
- Stuck-task detection: [method]
- Recovery actions: [per fault type]

### Risks and Mitigations
| Risk | Severity | Mitigation |
|---|---|---|
| | | |
```

## Handoff

- If safety classification drives architectural decisions, handoff to **iec62304-compliance** for documentation requirements
- If bootloader or firmware update tasks are needed, handoff to **bootloader-design**
- If interrupt latency is driven by analog sampling, flag for analog front-end review
- If RAM or Flash is insufficient, escalate MCU selection to system-level review

## Quality Checks

1. No priority inversion exists without priority inheritance or priority ceiling protocol enabled
2. All shared resources are protected by mutex with defined priority ceiling
3. ISRs contain no blocking calls (no mutex locks, no queue sends with timeout, no task delays)
4. Stack sizes are justified by call-depth analysis, not arbitrary round numbers
5. Total RAM usage is within MCU capacity with at least 20% margin
6. Watchdog timeout is longer than the slowest task period
7. CPU utilization is below 70% to provide margin for worst-case jitter and future growth
8. Safety-critical tasks are isolated from non-critical tasks (no shared mutexes across safety boundaries)

## Evolution Notes

- Future versions may integrate automated response-time analysis calculation
- Consider adding power-mode task scheduling (tickless idle, sleep states)
- Add support for multi-core RTOS architectures (asymmetric multiprocessing)
