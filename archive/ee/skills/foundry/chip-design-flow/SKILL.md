---
name: chip-design-flow
department: "foundry"
description: "Use when guiding RTL-to-GDSII chip design flow including RTL coding style, synthesis constraints, place-and-route strategy, timing closure, and tape-out checklist. Do not use for verification methodology (use verification-methodology) or SoC integration (use soc-integration)."
version: 1
triggers:
  - "RTL"
  - "synthesis"
  - "tape-out"
  - "place and route"
  - "timing closure"
  - "SDC"
  - "floor plan"
  - "GDSII"
  - "EDA"
  - "clock tree"
---

# Chip Design Flow

## Purpose

Guide the end-to-end RTL-to-GDSII design flow, ensuring clean synthesizable RTL, realistic constraints, timing closure, and tape-out readiness.

## Scope Constraints

Reviews RTL source, constraint files, and EDA tool reports. Does not execute EDA tools or modify design files. Does not perform physical verification (LVS/DRC) directly.

## Inputs

- RTL source files or design specification
- Target technology node and foundry PDK
- Performance targets (clock frequency, area budget, power budget)
- Existing SDC constraints and floor plan, if any

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
- [ ] Step 1: Review RTL coding style
- [ ] Step 2: Define synthesis constraints
- [ ] Step 3: Plan floor plan and power strategy
- [ ] Step 4: Guide place-and-route
- [ ] Step 5: Achieve timing closure
- [ ] Step 6: Tape-out readiness checklist

### Step 1: Review RTL Coding Style

- Verify all RTL is synthesizable (no `initial`, `#delay`, `force` in design code).
- Check clock domain crossing (CDC) handling with proper synchronizers.
- Verify reset strategy (async vs sync, reset tree planning).
- Flag combinational loops and unintended latches.
- Confirm coding style matches foundry library expectations (e.g., no tri-state in core logic).

### Step 2: Define Synthesis Constraints

- Write SDC constraints: clock definitions, generated clocks, clock groups.
- Define input/output delay constraints relative to system timing.
- Set false paths and multicycle paths with justification.
- Specify max transition, max fanout, and max capacitance.
- Define operating conditions for multi-corner multi-mode (MCMM) analysis.

### Step 3: Plan Floor Plan and Power Strategy

- Define die/block area targets based on gate count estimates.
- Plan macro placement (memories, PLLs, IO pads).
- Design power grid: supply ring, power stripes, via density targets.
- Plan clock tree topology (balanced tree, mesh, hybrid).
- Define placement blockages and routing blockages.

### Step 4: Guide Place-and-Route

- Set placement density targets (70-80% for timing, lower for routability).
- Configure global routing and detail routing options.
- Define metal layer usage (signal vs clock vs power).
- Check antenna rule compliance.
- Verify routing DRC clean before timing optimization.

### Step 5: Achieve Timing Closure

- Run static timing analysis (STA) across all MCMM corners.
- Fix setup violations: buffer insertion, gate sizing, logic restructuring.
- Fix hold violations: delay cell insertion, useful skew adjustment.
- Verify clock skew and insertion delay targets.
- Check signal integrity: crosstalk delta delay, noise margin.

### Step 6: Tape-Out Readiness Checklist

- LVS clean (layout vs schematic match).
- DRC clean (design rule compliance).
- ERC clean (electrical rule check).
- Formal equivalence check (RTL vs netlist, netlist vs layout).
- IR drop analysis within spec.
- Antenna rule compliance verified.
- Metal fill inserted and DRC re-verified.

> **Compaction resilience**: If context was lost, re-read the Inputs section for design targets, check the Progress Checklist, then resume from the earliest incomplete step.

## Output Format

| Stage | Status | Key Metrics | Issues | Action Items |
|-------|--------|-------------|--------|--------------|
| RTL review | ... | CDC crossings: N | ... | ... |
| Synthesis | ... | Area: X um2, WNS: Y ns | ... | ... |
| P&R | ... | Density: Z%, routing DRC: clean/N violations | ... | ... |
| Timing | ... | Setup WNS: Y ns, Hold WNS: Z ns | ... | ... |
| Tape-out | ... | LVS/DRC/ERC: clean | ... | ... |

## Handoff

- Hand off to verification-methodology for post-synthesis or post-layout simulation.
- Hand off to forge/rtl-security-review if security-critical RTL needs audit.

## Quality Checks

- [ ] RTL is synthesizable with no coding style violations
- [ ] CDC crossings identified and synchronized
- [ ] SDC constraints cover all clocks and inter-clock paths
- [ ] Floor plan has realistic area and power grid
- [ ] Timing closure achieved across all MCMM corners
- [ ] LVS, DRC, ERC clean
- [ ] Formal equivalence verified at each transformation stage

## Evolution Notes
<!-- Observations appended after each use -->
