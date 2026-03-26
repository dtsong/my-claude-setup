---
name: soc-integration
department: "foundry"
description: "Use when planning SoC integration including bus fabric architecture, memory map allocation, IP qualification, interrupt routing, and design-for-test strategy. Covers AMBA/AXI protocols, register map design, DFT insertion, and production test planning. Do not use for RTL design flow (use chip-design-flow) or block-level verification (use verification-methodology)."
version: 1
triggers:
  - "SoC"
  - "AMBA"
  - "AXI"
  - "IP integration"
  - "DFT"
  - "register map"
  - "memory map"
  - "interrupt"
  - "scan"
  - "BIST"
  - "ATPG"
---

# SoC Integration

## Purpose

Plan and review SoC-level integration covering bus fabric topology, memory map allocation, IP block qualification, interrupt routing, DFT strategy, and production test readiness.

## Scope Constraints

Reviews SoC architecture documents, IP datasheets, register maps, and DFT specifications. Does not modify design files or execute EDA tools. Does not perform physical design.

## Inputs

- SoC architecture block diagram and IP list
- Bus protocol requirements (AMBA AHB, AXI4, AXI4-Lite, APB)
- Memory map and address space allocation
- IP blocks to integrate with their interface specifications
- DFT and production test requirements

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Define bus fabric topology
- [ ] Step 2: Allocate memory map
- [ ] Step 3: Plan IP qualification
- [ ] Step 4: Design interrupt architecture
- [ ] Step 5: Plan DFT strategy
- [ ] Step 6: Production test readiness

### Step 1: Define Bus Fabric Topology

- Select bus protocols per performance tier (AXI4 for high-bandwidth, APB for config).
- Define interconnect topology: crossbar, ring, hierarchical bridge.
- Specify arbitration policy per master (fixed priority, round-robin, weighted).
- Plan outstanding transaction support and ID width.
- Define QoS parameters for latency-sensitive paths.

### Step 2: Allocate Memory Map

- Assign address ranges to each peripheral and memory region.
- Verify no address overlap and document reserved regions.
- Define secure vs non-secure address space partitioning.
- Plan boot address mapping and remapping.
- Document register map for each IP block (base address, register offsets, field definitions).

### Step 3: Plan IP Qualification

- Define IP integration checklist per block: interface compliance, clock/reset, documentation.
- Verify IP protocol compliance (AMBA protocol checker assertions).
- Check clock domain requirements and CDC interfaces.
- Verify reset requirements (async/sync, reset ordering).
- Confirm silicon-proven status or required validation level.

### Step 4: Design Interrupt Architecture

- Define interrupt controller topology (centralized GIC, distributed).
- Map interrupt sources to controller inputs with priority assignments.
- Specify edge vs level sensitivity per interrupt.
- Plan interrupt routing for multi-core configurations.
- Verify interrupt latency budget from source to handler.

### Step 5: Plan DFT Strategy

- Define scan architecture: full scan, compressed scan (DFTMAX, EDT).
- Plan memory BIST for all embedded memories.
- Specify JTAG/boundary scan (IEEE 1149.1) implementation.
- Define ATPG fault coverage targets (stuck-at >98%, transition >95%).
- Plan test mode control and isolation.
- Define analog/mixed-signal test access (if applicable).

### Step 6: Production Test Readiness

- Define production test flow: wafer sort, package test, system-level test.
- Specify test time budget per die.
- Plan for design-for-debug: trace ports, performance counters, embedded logic analyzers.
- Define die ID and fusing strategy.
- Document known-good-die (KGD) criteria.

> **Compaction resilience**: If context was lost, re-read the Inputs section for the SoC under integration, check the Progress Checklist, then resume from the earliest incomplete step.

## Output Format

### Integration Status Matrix

| IP Block | Bus Interface | Address Range | Clock Domain | DFT | Status |
|----------|--------------|---------------|-------------|-----|--------|
| CPU core | AXI4 master | N/A | clk_core | Scan | ... |
| UART | APB slave | 0x4000_0000 | clk_periph | Scan+BIST | ... |
| SRAM | AXI4 slave | 0x2000_0000 | clk_core | MBIST | ... |

## Handoff

- Hand off to chip-design-flow for physical implementation of the integrated SoC.
- Hand off to verification-methodology for SoC-level verification planning.
- Hand off to forge/rtl-security-review for security audit of bus fabric and access controls.

## Quality Checks

- [ ] Bus fabric topology defined with protocol selection justified
- [ ] Memory map complete with no address overlaps
- [ ] All IP blocks qualified against integration checklist
- [ ] Interrupt architecture documented with priorities
- [ ] DFT strategy covers scan, BIST, and ATPG targets
- [ ] Production test flow and time budget defined

## Evolution Notes
<!-- Observations appended after each use -->
