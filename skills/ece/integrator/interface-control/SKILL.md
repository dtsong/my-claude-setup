---
name: "interface-control"
department: "integrator"
description: "Use when defining or managing interfaces between subsystems and with external systems. Covers signal interfaces, power interfaces, mechanical interfaces, connector pinouts, and interface verification. Do not use for requirements decomposition (use requirements-decomposition) or V&V planning (use v-model-planning)."
version: 1
triggers:
  - "interface"
  - "ICD"
  - "connector"
  - "signal"
  - "boundary"
  - "protocol"
  - "pinout"
  - "mechanical interface"
  - "crossing"
---

# Interface Control

## Purpose

Define and manage interfaces between subsystems and with external systems. Produces an interface register, signal/power/mechanical interface tables, and an interface verification matrix that form the basis of interface control documents (ICDs).

## Scope Constraints

- Produces interface definitions and ICD content only; does not design the internals of any subsystem.
- Covers electrical signals, power distribution, mechanical form factor, and data protocols at subsystem boundaries.
- Does not decompose requirements — hand off to requirements-decomposition.
- Does not assign verification schedules — hand off to v-model-planning.

## Inputs

- System block diagram with subsystem boundaries
- Requirements decomposition output (especially cross-subsystem dependencies)
- Connector and cable constraints (available connectors, cable length limits, EMC requirements)
- Existing ICDs (if modifying an established interface)
- Applicable standards (IEC 60601-1 for isolation boundaries, IEC 61000-4-x for EMC interfaces)

## Input Sanitization

No user-provided values are used in commands or file paths. All inputs are treated as read-only analysis targets.

## Procedure

### Progress Checklist
<!-- Track completion across compaction boundaries -->
- [ ] Step 1: Enumerate Subsystem Boundaries
- [ ] Step 2: Define Signal Interfaces
- [ ] Step 3: Define Power Interfaces
- [ ] Step 4: Define Mechanical Interfaces
- [ ] Step 5: Define Interface Verification Methods
- [ ] Step 6: Establish Interface Change Control

### Step 1: Enumerate Subsystem Boundaries

From the system block diagram, list every boundary where signals, power, or mechanical connections cross between subsystems or between the system and the external environment. For each boundary, assign an interface ID using the format IF-[FROM]-[TO]-[NNN] (e.g., IF-AFE-DSP-001).

Categorize each crossing:
- **Signal** — analog signals, digital data, control lines, clock signals
- **Power** — supply voltages, ground connections, battery connections
- **Mechanical** — mounting interfaces, thermal paths, cable routing, enclosure penetrations
- **Data protocol** — SPI, I2C, UART, USB, Ethernet, wireless RF

### Step 2: Define Signal Interfaces

For each signal crossing, document in the Signal Interface Table:
- Interface ID and signal name
- Direction (A->B, B->A, bidirectional)
- Signal type (analog, digital, differential, single-ended)
- Voltage levels (logic high/low thresholds, analog range, common-mode range)
- Impedance (source impedance, load impedance, characteristic impedance for transmission lines)
- Timing (data rate, clock frequency, setup/hold times, propagation delay budget)
- Connector type and pin assignment
- Isolation requirements (MOPP/MOOP if crossing a patient safety boundary)

For differential signals, specify the differential voltage swing and common-mode voltage range. For analog signals, specify the signal bandwidth, noise floor at the interface, and full-scale range.

### Step 3: Define Power Interfaces

For each power crossing, document in the Power Interface Table:
- Interface ID and rail name
- Nominal voltage and tolerance (e.g., 3.3V +/- 5%)
- Maximum current (steady-state and peak/transient)
- Ripple and noise specification at the interface point
- Power sequencing requirements (which rails must be up first)
- Protection (overcurrent, overvoltage, reverse polarity, inrush limiting)
- Isolation requirements (reinforced, basic, or none; creepage and clearance distances)
- Connector type and pin assignment (power pins sized for current capacity)

### Step 4: Define Mechanical Interfaces

For each mechanical crossing, document in the Mechanical Interface Table:
- Interface ID and description
- Form factor constraints (dimensions, keep-out zones, mating geometry)
- Mounting method (screws, clips, press-fit, adhesive) with torque specs if applicable
- Thermal interface (thermal pad, gap filler, heatsink mounting, thermal resistance budget)
- Cable routing (cable type, bend radius, strain relief, EMC shielding requirements)
- Sealing requirements (IP rating at the interface, gasket specification)
- Material compatibility (galvanic corrosion, biocompatibility if patient-facing)

### Step 5: Define Interface Verification Methods

For each interface in the register, assign a verification method:
- **Test** — Measure the actual signal/power/mechanical parameter at the interface boundary
- **Analysis** — Calculate or simulate the interface parameter (e.g., impedance matching simulation)
- **Inspection** — Visual or dimensional check (connector type, pinout labeling, cable routing)
- **Demonstration** — Functional demonstration that the interface operates correctly in system context

Document the verification in the Interface Verification Matrix with pass/fail criteria that match the interface specification.

### Step 6: Establish Interface Change Control

Define the change control process for each interface:
- Interface baseline date (when the ICD is frozen for that boundary)
- Change request process (who can request, who approves)
- Impact assessment requirements (which subsystems are affected by a change)
- Version control (ICD revision history)

Flag any interfaces where both sides are being designed concurrently — these require more frequent coordination and are higher risk for integration issues.

> **Compaction resilience**: If context was lost during a long session, re-read the Inputs section to reconstruct what system is being analyzed, check the Progress Checklist for completed steps, then resume from the earliest incomplete step.

## Handoff

- If interface definitions reveal missing or ambiguous requirements, recommend loading integrator/requirements-decomposition.
- If interface verification needs scheduling into the V-model, recommend loading integrator/v-model-planning.
- If an interface crosses a patient safety boundary, recommend loading shield/safety-analysis for isolation analysis.
- If signal integrity or EMC concerns arise at an interface, recommend loading tracer/emc-strategy.

## Output Format

```markdown
# Interface Control Document: [System/Project Name]

## Interface Register

| Interface ID | From | To | Type | Description | ICD Rev |
|-------------|------|-----|------|-------------|---------|
| IF-AFE-DSP-001 | AFE | DSP | Signal | ADC data bus (SPI) | A |
| IF-PSU-AFE-001 | PSU | AFE | Power | Analog 5V supply rail | A |

## Signal Interface Table: [Boundary Name]

| Interface ID | Signal Name | Direction | Type | Voltage Levels | Impedance | Timing | Connector/Pin | Isolation |
|-------------|------------|-----------|------|---------------|-----------|--------|--------------|-----------|
| IF-AFE-DSP-001 | SPI_CLK | AFE->DSP | Digital | 0/3.3V LVCMOS | 50 ohm | 20 MHz max | J3 pin 4 | None |

## Power Interface Table

| Interface ID | Rail Name | Voltage | Tolerance | Max Current | Ripple | Sequencing | Protection | Connector/Pin |
|-------------|-----------|---------|-----------|-------------|--------|------------|------------|--------------|
| IF-PSU-AFE-001 | AVDD_5V | 5.0V | +/-2% | 250 mA steady, 400 mA peak | <10 mVpp | After 3.3V digital | OCP at 500 mA, OVP at 5.5V | J1 pin 1-2 |

## Mechanical Interface Table

| Interface ID | Description | Form Factor | Mounting | Thermal | Cable/Routing | Sealing |
|-------------|-------------|-------------|----------|---------|--------------|---------|
| IF-AFE-ENC-001 | AFE board to enclosure | 45x30mm, 2mm keep-out | 4x M2.5 screws, 0.4 Nm | Thermal pad to chassis, Rth < 5 C/W | N/A | IP54 gasket |

## Interface Verification Matrix

| Interface ID | Parameter | Specification | Verification Method | Pass/Fail Criteria |
|-------------|-----------|--------------|--------------------|--------------------|
| IF-AFE-DSP-001 | SPI clock frequency | 20 MHz max | Test — oscilloscope | Clock period >= 50 ns |

## Interface Change Control

| Interface ID | Baseline Date | Stakeholders | Risk Level |
|-------------|--------------|-------------|------------|
| IF-AFE-DSP-001 | TBD | EE-Analog, EE-Digital | Medium — concurrent design |
```

## Quality Checks

- [ ] Every subsystem boundary in the block diagram has at least one defined interface
- [ ] Signal names are consistent across both sides of the boundary (no naming conflicts)
- [ ] Voltage levels are compatible across each interface (driver output levels match receiver input thresholds)
- [ ] Connector pinouts are fully documented with no unassigned pins on in-use connectors
- [ ] Power interfaces specify current capacity, protection, and sequencing
- [ ] Isolation boundaries are identified and classified (MOPP/MOOP) per IEC 60601-1
- [ ] Every interface has a verification method assigned with measurable pass/fail criteria
- [ ] No "TBD" entries remain in signal levels, voltage tolerances, or current ratings for baselined interfaces

## Evolution Notes
<!-- Observations appended after each use -->
